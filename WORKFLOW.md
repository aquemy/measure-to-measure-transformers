# Validation workflow: experiments interleaved with proofs

This repository formalizes an existing paper (Geshkovski-Rigollet-Ruiz-Balet, *Measure-to-measure
interpolation using Transformers*, arXiv:2411.04551v3). Numerical experiments are not an afterthought
bolted on at the end: they are run **alongside** the proofs, so that simulation builds the intuition a
proof formalizes and then witnesses, on a seeded instance, that the formalized statement actually
holds.

## The principle

> Sometimes **before** a proof, **always after** it.

Each mathematical claim (a leaf computation, a proposition, a theorem) is paired with at least one
seeded experiment. The experiment plays one or both of two roles:

- **Before (exploratory, optional).** When the right statement or constant is unclear, run a quick
  probe first. It shapes the hypothesis, exposes sign errors, and tells you what is even true before
  you spend effort proving it. This is how the campaign caught review finding **F1**: experiment E1
  failed at mass fraction 0.27 until the gate sign of Lemma B.2 was corrected (see `ERRATA.md` and
  `RESEARCH.md` F1), at which point it passed at fraction 1.0.
- **After (validation, mandatory).** Once the claim is stated (and, for a leaf, proved in Lean), a
  seeded experiment integrates the actual dynamics and checks the claim's quantitative content against
  a pass criterion. This is the standing regression guard: re-running it re-validates the claim at the
  current commit.

A proof says *why* a statement is true for all inputs; an experiment says *that* it holds for this
seed, with numbers and a picture. Neither replaces the other. Keeping them adjacent is what makes the
proofs legible.

## The per-claim cycle

```
        (optional)                              (mandatory)
   ┌─ before probe ─┐      ┌─ prove / state ─┐      ┌─ after validation ─┐
   │ form hypothesis│  ->  │ Lean leaf or    │  ->  │ seeded run.py:     │
   │ pick constants │      │ informal proof  │      │ verdict + figure   │
   │ catch sign bugs│      │ (claims.toml)   │      │ + manifest         │
   └────────────────┘      └─────────────────┘      └────────────────────┘
                                                              │
                                                     science CKC commit
                                                  Status: sci.measured
                                                  Depends-On: claim:<the math claim>
                                                  Closes:     claim:exp-<name>
```

## What every experiment emits

Each `experiments/E*/run.py` is deterministic (`SEED = 0`) and, via the shared helpers in
`experiments/common.py`, writes three artifacts under `experiments/results/<name>/`:

| Artifact | Produced by | Role |
| --- | --- | --- |
| `summary.json` | `Result.write` | the **verdict**: `passed`, `criterion`, `metrics`, plus the `hypothesis` and `explanation` narrative and the `figures` list. Single source of truth for the experiment's story. |
| `manifest.json` | `Result.write` | the **provenance**: `git_sha`, `created_at` (ISO-UTC), `seed`, `host`, `python`, `platform`, `numpy`. Records when and against which commit the verdict was last produced. |
| `*.png` + `*.svg` | `save_figure` | the **visual evidence**: at least one figure per experiment that *shows* the verdict (a contraction curve, a retention plot, a separation trace). The report and website embed these. |

The figures and the two JSON files are tracked in git (see `.gitignore`); raw arrays (`.npz`, `.pkl`)
are not, because they regenerate from the seeded code.

## Running the campaign

```sh
cd experiments
uv run python -m E1_mass_transport.run     # one experiment
for e in E1_mass_transport E2_clustering E3_disentangle E4_matching \
         E5_lyapunov E6_end_to_end E7_linear_impossible; do
  uv run python -m ${e}.run                 # the whole campaign
done
```

Each run prints `[PASS]` / `[FAIL]` with its metrics and (re)writes the three artifacts. Exit code is
`0` on pass, `1` on fail, so the loop doubles as a regression check.

## Experiment ↔ claim map

Every experiment is cross-linked to the claim(s) it tests, both here and as a `tests = [...]` field on
the `[claims.exp-*]` entries in `claims.toml`. The science commit that records each run carries the
same link as a `Depends-On: claim:<slug>` footer, so the dependency is a real edge in the ClaimGraph.

| Exp | Tests (math claim) | Leaf / paper node | Verdict figure |
| --- | --- | --- | --- |
| E1 mass transport | `leaf-gate-ode` (L2), `leaf-ball-chain-induction` (L9), `lem-b-2`, `lem-b-1` | gate ODE + ball-chain retention | per-stage retention vs `(1-eps)^k` floor |
| E2 clustering | `prop-2-1` | self-attention clustering | diameter contraction + `T(eps) ~ log(1/eps)` |
| E3 disentangle | `prop-3-1`, `lem-3-3`, `leaf-barycenter-ode` (L6), `leaf-barycenter-noncolinear` (L11) | barycenter separation | min cross-measure distance over time |
| E4 matching | `prop-4-2`, `prop-4-1`, `leaf-sep-hyperplane` (L3) | gated selective steering | distance-to-target: active vs parked |
| E5 Lyapunov | `leaf-lyapunov` (L5) | `E = 1 - cos theta` decrease | `E(t)` ensemble decreasing to 0 |
| E6 end-to-end | `thm-1-1`, `thm-1-2` | the full `disentangle -> cluster -> match` | three-phase transport panels |
| E7 linear impossible | `thm-1-1` (necessity of nonlinearity) | negative control, eq. 1.7 | obstruction gap vs attention escape gap |

## CKC commit convention for a validation run

A run is recorded as a `science`-profile Conventional Knowledge Commit:

```
experiment(eN): <one-line what the figure shows> (<paper node>)

<short paragraph: construction, what is measured, the headline number/figure>

Status: sci.measured
Seed: 0
Verified-By: experiments/EN_name/run.py
Depends-On: claim:<the math claim it tests>
Closes: claim:exp-eN-name
```

The `Depends-On` line is what wires the experiment to the proof in the dependency graph; the
`Verified-By` line names the script that produced the verdict; `Seed` makes the run reproducible.

## Refutation regression suite

Every axiom admitted into `Statements/` (or `Axioms/`) lands together with two committed
artifacts. First, a *witness*: an `example` in `Regression/NonVacuity/` that instantiates every
hypothesis with concrete data (a Dirac at a unit vector, a cap-avoiding measure) and applies the
axiom -- an over-strengthened or vacuous axiom then breaks `lake build`. Second, whenever the
admission audit kernel-refuted a looser draft, a *refutation pair*: the refuted signature is
transcribed as an `abbrev ...Sig` in `Regression/OldStatements.lean` (weakened to what the
disproof uses), the disproof is committed as `theorem ..._false : ...Sig -> False` in
`Regression/Refuted/` (kernel-checked forever), and a short must-fail adapter
`example : ...Sig := fun ... => current_axiom ...` goes in
`Refutations/F<nn>_<axiom>_<exploit>.lean`. `scripts/refutation-gate.sh` (run by
`scripts/audit.sh` step 5 and by CI) asserts every `Refutations/` file still fails for an
expected reason; if one compiles, the axiom has been re-loosened to a shape the kernel already
refuted -- composing the adapter with the committed disproof would literally prove `False`. On a
Lean/Mathlib bump, message drift cannot green-wash the gate: the proof machinery lives in the
`Regression` lib, so renames surface as ordinary build failures; if an adapter then fails with a
drift signature (unknown identifier/constant/module), the gate reports FAILED-WRONG-REASON and
only the adapter's plumbing is repaired -- never the old signature or the disproof. A deliberate
re-statement of an axiom requires re-deriving its adapters and re-running the gate before merge,
and gets a fresh `RESEARCH.md` finding id.
