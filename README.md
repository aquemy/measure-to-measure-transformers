# Measure-to-measure interpolation using Transformers: formal verification

A machine-checked Lean 4 formalization effort, plus a targeted numerical validation campaign, for

> B. Geshkovski, P. Rigollet, D. Ruiz-Balet.
> *Measure-to-measure interpolation using Transformers.* arXiv:2411.04551v3 (math.OC).

The reference PDF is in [`references/paper.pdf`](references/paper.pdf).

## What the paper proves

A Transformer is recast as a continuity equation on the unit sphere,

```
dt mu + div( mu v[mu] ) = 0      on [0,T] x S^{d-1},
```

whose velocity field `v[mu]` combines a mean-field self-attention term and a perceptron, projected
onto the tangent space (layer normalization). The main result is a controllability statement: a
single set of piecewise-constant parameters steers `N` arbitrary input measures arbitrarily close
(in `W2`) to `N` arbitrary target measures, under the minimal assumption that each input/target
pair is matchable by some transport map. The strategy is

```
Phi_fin = (Phi_t3)^{-1} . Phi_t2 . Phi_t1
```

that is, disentangle the input supports, match, then un-disentangle the targets. The measure
dependence of self-attention is what makes this possible: a single *linear* continuity equation
provably cannot do it (eq. 1.7).

## What this repository delivers

A full kernel-checked proof of the whole paper is not achievable today, because Mathlib lacks the
required infrastructure (optimal transport and `W2` with Kantorovich duality, continuity-equation
well-posedness and mean-field flow maps, geodesic convexity on the sphere, LaSalle invariance,
Hartman-Grobman). Building that is a multi-year effort. Instead this repository provides the honest
formalization pipeline:

1. An adversarial proof review of every argument (`RESEARCH.md`).
2. A full Lean blueprint: every one of the paper's statements made type-correct, wired into a
   dependency graph (`MeasureToMeasure/Statements/`, `blueprint/`).
3. A foundations layer built from Mathlib (sphere, tangential projector, geodesic distance) and a
   clearly labeled axiom layer for the deep prerequisites (`MeasureToMeasure/Axioms/`).
4. Kernel-checked Lean proofs of the self-contained leaf lemmas: the projector and gate-ODE
   identities, the separating-hyperplane bounds, the geodesic gradient, the Lyapunov sign, the
   barycenter ODE, the transport coupling bound, the Markov bound, the ball-chain induction, and the
   pigeonhole step (`MeasureToMeasure/Leaves/`).
5. A targeted numerical validation campaign E1-E7 (`experiments/`), each experiment isolating one
   theorem or proposition with a seeded pass/fail criterion.

Every claim is tracked with [Conventional Knowledge Commits](https://conventional-knowledge-commits.org)
(CKC), so the real epistemic status of each result (machine-checked, axiomatised, proved-informal)
is recorded in the commit history and the ClaimGraph, and cross-checked against the Lean kernel via
`#print axioms`. See `CONTRIBUTING.md` and `claims.toml`.

## Layout

```
MeasureToMeasure/
  Foundations/   sphere, tangential projector, geodesic distance (from Mathlib)
  Axioms/        labeled axioms for the deep prerequisites Mathlib lacks
  Leaves/        kernel-checked self-contained lemmas L1-L10
  Statements/    type-correct statements of every paper result (blueprint nodes)
experiments/     numerical validation campaign E1-E7 (uv, Python 3.14, JAX)
blueprint/       Lean Blueprint LaTeX + dependency graph
docs/            published blueprint site (classic GitHub Pages from /docs)
claims.toml      the CKC claim registry
RESEARCH.md      the proof-review and status ledger
```

## Build

```
lake exe cache get     # fetch prebuilt Mathlib oleans
lake build             # build the formalization
```

Lean is pinned to `v4.31.0` and Mathlib to the matching `v4.31.0` tag.
