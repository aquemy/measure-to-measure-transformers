#!/usr/bin/env bash
# audit.sh -- kernel-honesty drift guard (regenerate-and-compare).
#
# Runs the canonical lean-math / ClaimGraph honesty tools and fails if the committed status feed has
# drifted from what the Lean kernel actually certifies. Three orthogonal checks:
#
#   1. axiom-report        -- #print axioms per blueprint node -> .cache/axiom-report.txt
#   2. claimgraph audit    -- VALIDITY gate: fail if a node is shown proved but the kernel refutes it
#   3. claimgraph reconcile-- DRIFT gate: fail if any node is "stale-blueprint" (blueprint status
#                             disagrees with the kernel, in either direction)
#   4. lean-sorry-gate     -- sweep the Lean tree for sorry/admit/sorryAx/native_decide/new axioms
#
# "ungrounded" / "paper-only" reconcile categories are curation (the blueprint is a curated subset),
# reported as warnings, not failures.
#
# The project must already build (`lake build`). Run from the repo root:  scripts/audit.sh
#
# Tool locations are overridable by env var so CI can point at pinned, vendored copies:
#   AXIOM_REPORT      path to the axiom-report binary
#   CLAIMGRAPH_SRC    path to an editable checkout of the claimgraph package (for `uv run`)
set -uo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo" || { echo "audit: cannot cd to repo root" >&2; exit 1; }

TEX="blueprint/src/content.tex"
CLAIMS="claims.toml"
CACHE=".cache"
mkdir -p "$CACHE"

# --- resolve tooling ----------------------------------------------------------------------------
plugin_bin="$(ls -d "$HOME"/.claude/plugins/cache/aquemy-personal/lean-math/*/bin 2>/dev/null | sort -V | tail -1)"
# Prefer the vendored copy (scripts/axiom-report) so CI and fresh checkouts need no private
# tooling; the AXIOM_REPORT env override and the plugin fallback are kept.
if [ -x "scripts/axiom-report" ]; then
  AXIOM_REPORT="${AXIOM_REPORT:-scripts/axiom-report}"
else
  AXIOM_REPORT="${AXIOM_REPORT:-$plugin_bin/axiom-report}"
fi
CLAIMGRAPH_SRC="${CLAIMGRAPH_SRC:-/Users/aquemy/projects/hother/claimgraph}"

claimgraph() {
  uv run --no-project --python 3.13 --with-editable "$CLAIMGRAPH_SRC" claimgraph "$@"
}

fail=0
note() { printf '\n== %s ==\n' "$*"; }

# --- 0. build gate ------------------------------------------------------------------------------
# The honesty tools below read `.olean`s via `#print axioms`. If those oleans are stale (or the tree
# does not compile), the checks silently certify whatever the last good build left behind -- exactly
# the false-green that let a W2/Axioms name collision break `main` unnoticed (PR #36). So force a real
# build first and fail loudly on any error. `lake build` is incremental: a no-op when nothing changed.
note "lake build (regenerate oleans; a broken/stale build must fail here, not false-green below)"
if ! lake build; then
  echo "audit: FAIL -- lake build failed; the kernel-honesty checks below read oleans, so a broken" >&2
  echo "       or stale build must fail the audit rather than certify stale oleans (see PR #36)." >&2
  exit 1
fi

# --- 1. axiom-report ----------------------------------------------------------------------------
note "axiom-report (#print axioms per blueprint node)"
if [ ! -x "$AXIOM_REPORT" ]; then
  echo "audit: axiom-report not found at $AXIOM_REPORT (set AXIOM_REPORT=...)" >&2
  exit 127
fi
"$AXIOM_REPORT" . --tex "$TEX" > "$CACHE/axiom-report.txt"
ar=$?    # 0 = all clean, 3 = ran fine with non-clean nodes (expected), other = error
if [ "$ar" != 0 ] && [ "$ar" != 3 ]; then
  echo "audit: axiom-report errored (exit $ar)" >&2; exit 1
fi
cat "$CACHE/axiom-report.txt"

# --- 2. validity gate ---------------------------------------------------------------------------
note "claimgraph audit (validity gate: proved-but-kernel-refutes)"
if claimgraph audit "$TEX" --repo . --claims "$CLAIMS" --axioms "$CACHE/axiom-report.txt"; then
  echo "audit: OK -- no honesty gaps."
else
  echo "audit: FAIL -- a node is shown proved but the kernel refutes it." >&2
  fail=1
fi

# --- 3. drift gate ------------------------------------------------------------------------------
note "claimgraph reconcile (drift gate: stale-blueprint)"
claimgraph reconcile "$TEX" . --claims "$CLAIMS" --axioms "$CACHE/axiom-report.txt" > "$CACHE/reconcile.txt" 2>&1
stale="$(grep -E '^stale-blueprint +\([0-9]+\)$' "$CACHE/reconcile.txt" | grep -oE '[0-9]+' || echo 0)"
ungrounded="$(grep -E '^ungrounded +\([0-9]+\)$' "$CACHE/reconcile.txt" | grep -oE '[0-9]+' || echo 0)"
paperonly="$(grep -E '^paper-only +\([0-9]+\)$' "$CACHE/reconcile.txt" | grep -oE '[0-9]+' || echo 0)"
if [ "${stale:-0}" -gt 0 ]; then
  echo "audit: FAIL -- $stale stale-blueprint node(s): blueprint status disagrees with the kernel." >&2
  sed -n '/^stale-blueprint/,/^[a-z].*([0-9]*)$/p' "$CACHE/reconcile.txt" | sed '$d' >&2
  fail=1
else
  echo "audit: OK -- no stale-blueprint nodes."
fi
echo "note: $ungrounded ungrounded, $paperonly paper-only (curation, not failures; see $CACHE/reconcile.txt)."

# --- 4. incompleteness sweep --------------------------------------------------------------------
# Gate only on GENUINE incompleteness / trust-widening: sorry / admit / sorryAx / native_decide.
# We do NOT gate on `axiom` declarations here -- the labeled-axiom layer (Axioms/ plus the
# deliberately-axiomatized mid-level statements in Statements/) is the honest, reviewed, kernel-
# visible infrastructure, and its status is already grounded by axiom-report + reconcile above.
note "incompleteness sweep (sorry / admit / sorryAx / native_decide)"
# `Regression/` is swept too (its disproofs are real kernel-checked theorems). `Refutations/` is
# deliberately excluded: those files never compile (must-fail adapters, checked by the gate below).
hits="$(grep -rnE '\b(sorry|admit|sorryAx|native_decide)\b' MeasureToMeasure ForMathlib Regression \
          --include='*.lean' 2>/dev/null || true)"
if [ -z "$hits" ]; then
  echo "audit: OK -- no sorry/admit/sorryAx/native_decide in the Lean tree."
else
  echo "audit: FAIL -- incompleteness/trust-widening markers found:" >&2
  echo "$hits" >&2
  fail=1
fi

# --- 5. refutation regression gate ---------------------------------------------------------------
# Statement-truth guard (findings F11-F16): every Refutations/*.lean derives a kernel-refuted OLD
# axiom statement from the CURRENT axiom and must FAIL to elaborate; the Regression lib (witnesses
# + disproofs) already built in step 0.
note "refutation regression gate (must-fail refutations / must-pass witnesses)"
if scripts/refutation-gate.sh --skip-build; then
  echo "audit: OK -- no axiom re-loosened; witnesses healthy."
else
  echo "audit: FAIL -- refutation gate (axiom re-loosened, or a refutation file broke)." >&2
  fail=1
fi

# --- verdict ------------------------------------------------------------------------------------
note "verdict"
if [ "$fail" = 0 ]; then echo "audit: PASS"; exit 0; else echo "audit: FAIL"; exit 1; fi
