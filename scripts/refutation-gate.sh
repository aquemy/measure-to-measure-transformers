#!/usr/bin/env bash
# refutation-gate.sh -- refutation regression gate (public deps only: bash, grep, lake).
#
# MUST-PASS half: the Regression lib (kernel-checked disproofs of historical false axiom
#   statements + per-axiom non-vacuity witnesses) is a lake default target; `lake build` here
#   is the witness gate.
# MUST-FAIL half: every Refutations/*.lean is an adapter deriving a kernel-refuted old axiom
#   statement from the CURRENT axiom. Each must FAIL to elaborate:
#     compiles            -> axiom re-loosened           -> gate FAILS loudly
#     fails, deny match   -> drift (rename/import/typo)  -> gate FAILS (wrong reason)
#     fails, expected     -> OK
# Exit: 0 all good; 1 re-loosened axiom or wrong-reason failure; 2 infrastructure problem.
set -uo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo" || exit 2

REFUTE_DIR="Refutations"
DENY_RE='[Uu]nknown identifier|unknownIdentifier|[Uu]nknown constant|[Uu]nknown module|[Uu]nknown package|bad import|object file|[Nn]o such file|unexpected token|invalid import'
ALLOW_RE='synthInstanceFailed|failed to synthesize|[Tt]ype mismatch|Function expected|not an inductive'

skip_build=0
[ "${1:-}" = "--skip-build" ] && skip_build=1

command -v lake >/dev/null || { echo "gate: lake not found" >&2; exit 2; }

if [ "$skip_build" = 0 ]; then
  echo "gate: lake build (must-pass half: witnesses + refuted-old-statement disproofs)"
  lake build || { echo "gate: FAIL -- build broke; the must-pass half is unhealthy" >&2; exit 2; }
fi

shopt -s nullglob
files=("$REFUTE_DIR"/*.lean)
[ ${#files[@]} -gt 0 ] || { echo "gate: FAIL -- no files in $REFUTE_DIR/" >&2; exit 2; }

fail=0 ok=0 n=0 total=${#files[@]}
for f in "${files[@]}"; do
  n=$((n+1)); tag="gate: [$n/$total] $f"
  grep -q '^-- MUST-FAIL:' "$f" ||
    { echo "$tag: missing '-- MUST-FAIL:' header" >&2; fail=1; continue; }
  grep -q '^set_option autoImplicit false' "$f" ||
    { echo "$tag: missing 'set_option autoImplicit false' (typo-masking hazard)" >&2; fail=1; continue; }

  out="$(lake env lean "$f" 2>&1)"; rc=$?

  if [ "$rc" -eq 0 ]; then
    echo "$tag: COMPILED -- AXIOM RE-LOOSENED to a kernel-refuted shape (see Regression/Refuted)" >&2
    fail=1; continue
  fi
  if printf '%s' "$out" | grep -Eq "$DENY_RE"; then
    echo "$tag: FAILED-WRONG-REASON (drift signature):" >&2
    printf '%s\n' "$out" | grep -E "$DENY_RE" | head -3 >&2
    fail=1; continue
  fi
  bad=0; had_expect=0
  while IFS= read -r pat; do
    had_expect=1
    printf '%s' "$out" | grep -Eq "$pat" ||
      { echo "$tag: FAILED-WRONG-REASON (EXPECT-ERROR /$pat/ not in output)" >&2; bad=1; }
  done < <(sed -n 's/^-- EXPECT-ERROR: //p' "$f")
  if [ "$had_expect" -eq 0 ] && ! printf '%s' "$out" | grep -Eq "$ALLOW_RE"; then
    echo "$tag: FAILED-WRONG-REASON (no expected error class in output)" >&2; bad=1
  fi
  if [ "$bad" -eq 0 ]; then
    reason="$(printf '%s' "$out" | grep -Eo "$ALLOW_RE" | head -1)"
    echo "$tag: FAIL-AS-EXPECTED (${reason:-EXPECT-ERROR matched})"; ok=$((ok+1))
  else
    fail=1
  fi
done

echo "gate: $ok/$total refutation files fail as expected."
if [ "$fail" -eq 0 ]; then echo "gate: PASS"; exit 0; else echo "gate: FAIL" >&2; exit 1; fi
