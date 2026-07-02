# Contributing

This repository tracks knowledge work with Conventional Knowledge Commits (CKC), a strict superset
of Conventional Commits for mathematical proofs and scientific findings. Spec:
https://conventional-knowledge-commits.org/0.1.0/en/

## Setup

```
pre-commit install --hook-type commit-msg
```

This wires the `ckc` commit-message validator and the opt-in `ckc-axiom-check` proof-honesty hook
(see `.pre-commit-config.yaml`). Profiles `proof` and `science` are active (`.ckc.toml`).

## The rules we follow

- One claim per commit. A commit asserts a single theorem, lemma, definition, experiment, or result.
- Grammar: `<type>[~][(scope)][!]: <description>`, then body, then footers (git trailers).
- Pick the type from the right profile:
  - proof: `state`, `proof`, `formalize`, `axiomatize`, `strengthen`, `generalize`, `weaken` (`!`), `port`.
  - science: `experiment`, `result`, `replicate`, `null`, `data`, `protocol`, `method`, `analysis`.
  - shared: `conjecture`, `lit`, `review`, `refute` (`!`), `retract` (`!`), `expose`, `meta`.
- Set the epistemic `Status:` footer:
  - `math.proved-informal` (paper proof, reviewed, not yet formalized),
  - `math.axiomatised` (Lean statement resting on a cited axiom),
  - `math.machine-checked` (clean Lean kernel: `Axioms:` shows only
    `propext, Classical.choice, Quot.sound`),
  - `math.open` (a `sorry`/`sorryAx` is present),
  - science: `sci.hypothesis`, `sci.measured`, `sci.supported`, `sci.falsified`.
- Build the ClaimGraph with relation footers: `Depends-On`, `Assumes`, `Proves`, `Closes`,
  `Refutes`, `Supersedes`. Reference a claim by its Lean fully-qualified name or its `claims.toml`
  slug (`claim:<slug>`), never a commit hash.
- When the status is not clean, add a `~` on the type and an uppercase marker footer: `AXIOM:`,
  `OPEN:`, `ASSUMES:`. Add provenance: `Lean:` (declaration id), `Axioms:` (literal `#print axioms`).
- Honesty: never claim `math.machine-checked` while a `sorry`/`sorryAx` or a non-standard axiom is
  present. A status advances only by a new commit, never by editing an old one.

## Honesty drift guard

`scripts/audit.sh` is the regenerate-and-compare guard: it runs `axiom-report` (`#print axioms` per
blueprint node), `claimgraph audit` (the validity gate: fail if a node is shown proved but the kernel
refutes it), `claimgraph reconcile` (the drift gate: fail on any `stale-blueprint` node whose committed
status disagrees with the kernel), and an incompleteness sweep for `sorry`/`admit`/`sorryAx`/
`native_decide`. It runs automatically inside `site/build.py` (fail fast, before the render; set
`SKIP_AUDIT=1` to skip for a site-only iteration) and in CI (`.github/workflows/verify.yml`, no deploy).
Run it directly before publishing: `bash scripts/audit.sh` (the project must already `lake build`).

## Example commits

A kernel-checked leaf:

```
formalize(leaves): prove the tangential projector inner-product identity

Lean: MeasureToMeasure.Leaves.projector_inner_sub_sq
Status: math.machine-checked
Axioms: 'projector_inner_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
Closes: claim:leaf-projector
Depends-On: MeasureToMeasure.Foundations.tangentialProjector
```

A labeled axiom:

```
axiomatize~(wasserstein): assume W2 with Kantorovich-Rubinstein duality

CKC honest record: Mathlib lacks a developed optimal-transport / Wasserstein theory, so W2 and
its duality are introduced as axioms here.
Lean: MeasureToMeasure.Axioms.W2
Status: math.axiomatised
AXIOM: W2 (no Mathlib optimal-transport theory at v4.31.0)
Closes: claim:lem-5-2
```

A numerical experiment:

```
experiment(e1): integrate the gated flow, mass reaches B0 cap B1 above 1-eps

Status: sci.measured
Depends-On: claim:leaf-gate-ode
Verified-By: experiments/E1_mass_transport/run.py
Seed: 0
Closes: claim:exp-e1-mass-transport
```

## House style

Plain, non-LLM voice. No em-dashes in commit messages, docs, or code comments.
