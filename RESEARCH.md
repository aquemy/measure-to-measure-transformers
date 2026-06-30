# Research ledger

Status of the formalization and validation of Geshkovski-Rigollet-Ruiz-Balet,
*Measure-to-measure interpolation using Transformers* (arXiv:2411.04551v3).

This file is the human-readable companion to `claims.toml` and the ClaimGraph. It records the
proof review, the formalization status of each node, and the precise boundary between what is
kernel-checked and what rests on axioms.

## Rough correctness review (Phase 1, initial pass)

Worked through the key computations from the PDF. No errors found. Hand-verified clean:

- Gate ODE (B.5): with `U=-1 z^T`, `b=cos(R) 1`, `W 1 = omega`, the velocity is
  `W(Ux+b)_+ = (cos R - <z,x>)_+ omega`, hence
  `d/dt <x,omega> = <P_x^perp omega, omega> (cos R - <z,x>)_+ = (1 - <x,omega>^2)(cos R - cos d_g(z,x))_+`.
  Matches the paper.
- Separating hyperplane (Prop 4.2 Step 1): `<omega, x_0^M> - cos(pi/8 + tau) < 0` because
  `d_g(omega, x_0^M) >= 3pi/8 > pi/8 + tau` and `cos` is decreasing on `[0, pi]`.
- Barycenter ODE (B.9): `d/dt <x,alpha> = <E_mu[x], alpha>(1 - <alpha,x>^2)`, sign-preserving,
  converges to `+-alpha`.
- Lyapunov (Example 6.1): `E = 1 - cos theta`, `theta' = -alpha sin theta`, so `E' = -alpha sin^2 theta <= 0`.
- Coupling bound (Lemma 5.2): `W2^2(T1_# mu, T2_# mu) <= integral ||T1 - T2||^2 d mu` via the
  map-induced coupling.
- Ball-chain induction (Lemma B.1): `mu(T, B_K) >= (1-eps)^K mu_0(union B_k)` by backward induction
  on the chain, each step from Lemma B.2.

Parts that are correct but rest on cited machinery (these become labeled axioms): clustering via
LaSalle invariance, exponential rates via Hartman-Grobman, geodesic-convex-hull nesting, and
continuity-equation well-posedness / flow-map existence.

## Mathlib coverage (Phase 0)

Determined by grepping the checked-out Mathlib `v4.31.0` source (`.lake/packages/mathlib`).

| Prerequisite | Mathlib v4.31.0 status | Plan |
| --- | --- | --- |
| Sphere `S^{d-1}`, norm/inner facts | present (`Metric.sphere`, `EuclideanSpace`) | use directly |
| Sphere as a smooth manifold | present (`Geometry/Manifold/Instances/Sphere`) | use if needed |
| Tangential projector `I - x x^T` | buildable from inner-product API | define + prove L1 |
| Geodesic distance `arccos <x,y>` | partial: `InnerProductGeometry.angle` exists; not packaged as the Riemannian geodesic distance | wrap `arccos<x,y>` as `d_g` |
| Geodesic convexity / geodesic convex hull | absent (no `geodesic` in `Geometry`) | axiomatize the nesting facts |
| ODE existence/uniqueness, Picard-Lindelof, Gronwall | present (`Analysis/ODE/`) | use for the L2/L5/L6 ODE facts |
| Wasserstein `W2`/`W1`, Kantorovich duality, transport maps | absent (only `LevyProkhorovMetric`, `Prokhorov` weak-convergence) | axiomatize |
| Continuity-equation well-posedness, mean-field flow maps | absent (no `continuityEquation`) | axiomatize |
| LaSalle invariance, Hartman-Grobman | absent | axiomatize |

Conclusion: the axiom boundary is exactly the analytic infrastructure (optimal transport,
continuity-equation flows, geodesic convexity, long-time ODE behaviour). Everything below it
(projector algebra, the gate and barycenter ODE identities as Picard-Lindelof/Gronwall facts,
monotone-cos inequalities, the abstract ball-chain induction, the pigeonhole step) is provable from
Mathlib and becomes the kernel-checked leaf set L1-L10.

## Node status

See `claims.toml` for the authoritative registry. As commits land, each node advances from
`math.proved-informal` to `math.axiomatised` or `math.machine-checked`. A node's *effective* status
is the minimum over its `Depends-On` / `Assumes` closure, so any result above an axiom reads
`math.axiomatised`, honestly.
