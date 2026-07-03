# Research ledger — Measure-to-measure interpolation using Transformers

> Human-readable companion to `claims.toml` and the ClaimGraph, for the formalization of
> Geshkovski-Rigollet-Ruiz-Balet, *Measure-to-measure interpolation using Transformers*
> (arXiv:2411.04551v3). This file records *where we are*; `blueprint/src/content.tex` + the CKC
> history + `bin/axiom-report` (via `scripts/audit.sh`) are the source of truth for *what is proved*.
> The dashboard below follows the `lean-math:math-research` ledger template; the detailed working
> record is preserved verbatim in the appendix.

## Snapshot
- **Entry point:** existing paper (arXiv:2411.04551v3).
- **Current phase:** J mathlib-ready / ongoing axiom discharge (M2 optimal transport, M3 mean-field
  flow). Every paper statement is stated in Lean; the deep analytic layer is honestly axiomatized and
  being discharged milestone by milestone (M8a and the `W₁` KR bound are done).
- **Last updated:** 2026-07-02.

## Conjecture / claims
- **Main claim:** the paper's Theorems 1.1 / 1.2 — a Transformer (the measure-valued flow of the
  layer-normalized attention dynamics) can interpolate an absolutely continuous measure to any
  discrete/target measure to arbitrary `W₂` accuracy with a controlled number of switches.
- **Sub-claims / lemmas:** Props 2.1, 2.2, 3.1, 4.1, 4.2; Lemmas 3.2-3.4, 5.1, 5.2, 5.4, B.1, B.2;
  Claim 2 (Markov bound); the self-contained leaf cores L1-L11.
- **Success criteria:** every statement of the paper stated type-correctly in Lean with **zero
  `sorry`** and an honest per-node status; the irreducible analytic facts axiomatized at the *most
  primitive faithful point* and clearly labeled; axioms discharged opportunistically where Mathlib
  permits (done: M8a atomless splitting, the `W₁` Kantorovich-Rubinstein bound).

## Definitional decisions (locked at Gate D)
| Object | Chosen Mathlib representation | Bridge obligation | Status |
| --- | --- | --- | --- |
| Ambient space | `Eucl d := EuclideanSpace ℝ (Fin d)` | defeq / none | built |
| Unit sphere | `sphere d := Metric.sphere (0 : Eucl d) 1` | defeq (`‖x‖ = 1`) | built |
| Tangential projector | in-repo `tangentialProjector x v = v - ⟪x,v⟫•x` | relates to `orthogonalProjection {x}ᗮ`; general form staged in `ForMathlib/` | built |
| Geodesic distance | `arccos⟪x,y⟫`; on the sphere **is** `InnerProductGeometry.angle` | bridge `angle_eq_arccos_inner_of_norm_eq_one` (`ForMathlib/`) | built |
| Barycenter | `∫ x ∂μ` (Bochner) | `Convex.integral_mem` | built |
| `W₁` / `W₂` | built from `Measure.prod` + marginals (`Foundations.W1`, `W2sq`); `Axioms.W1` a def, `Axioms.W2` opaque | `W₁` discharged (KR bound proved); `W₂` still an opaque axiom | partial |
| Continuity-equation flow | opaque `flowMap` (Axioms); `measureFlow := μ.map (flowMap θ t)` | no Mathlib continuity-equation solver | axiom |
| Atomless prescribed-mass split | Sierpiński IVT via CDF-primitive + IVT (`Foundations`) | discharged (M8a) | built |

## Gate decisions (append-only log)
| Date | Gate | Decision | Why |
| --- | --- | --- | --- |
| 2026-06 | A: pursue? | yes | formalize a published, self-contained result with a clear axiom boundary |
| 2026-06 | B: novel? | known (formalize) | the mathematics is published; the Lean formalization is the contribution |
| 2026-06 | C: sound? | formalize, one fix-first | adversarial review found F1 (sign typo, load-bearing) and F2 (rigor gap); both handled |
| 2026-06 | D: build vs axiomatize | per-prereq | OT / continuity-equation flow / geodesic convexity / LaSalle absent in Mathlib -> axiomatize at the primitive point; projector / ODE identities / pigeonhole -> build |
| 2026-06-19 | F: validate | yes | seven seeded experiments E1-E7 corroborate the quantitative content |
| 2026-06-30 | discharge | M8a done | Sierpiński IVT + atomless splitting fully machine-checked |
| 2026-07-01 | discharge | `W₁` KR bound done | Markov bound (L8) flipped to machine-checked (#27) |
| 2026-07-02 | I: site & badges honest? | yes | `scripts/audit.sh` (regenerate-and-compare) passes; one stale badge (L8) fixed (#29) |
| 2026-07-02 | J: mathlib-ready | staged | spherical-geometry cluster staged in `ForMathlib/`, `#print axioms`-clean (#30) |
| 2026-07-03 | C: sound? (re-audit) | fixed 3 false stubs | F11: `lemma_3_4_part1/part2`, `lemma_5_1` dropped paper hypotheses and were refutable; restored `μ≠ν`/orthant/colinearity and `DisjointSupports`. Orphan axioms, no proved result affected; disproofs machine-checked |
| 2026-07-03 | C: sound? (full fidelity matrix + refutation harness) | fixed 7 more stubs; 1 structural gap open | F12: sphere/support/dimension hypotheses restored across the axiom layer (4 kernel disproofs, 3 in-system); F13: Lemma 5.1 "invertible ψ" unsatisfiable (paper statement/proof mismatch, E2); F14 OPEN: linear `measureFlow` cannot express disentanglement (eq. 1.7) -- mean-field attention model decided; F15: B.1/B.2 quantifier order (E3); F16: lemma_B_1 docstring corrected |
| 2026-07-03 | C: sound? (F14 fix) | mean-field restatement landed | F14 FIXED: `Foundations/Attention.lean` (eq. (1.2) field, `IsMeanFieldFlow`, well-posedness axiom pair) + Statements restated per-layer (paper's `V ≡ 0` constructions stay linear; attention-driven results move to `AttnSchedule`); `SharedMissingDirection` gap form; `exists_disentangling_balls` gains `μ₀^i ≢ μ₀^j` + per-member flow maps; `prop_2_2` re-axiomatised (its old assembly needed mixture linearity, invalid for mean-field); all refutation files now fail to typecheck |
| 2026-07-03 | G: guarded? (regression suite) | committed | Refutation regression suite: `Regression/` lib (kernel-checked disproofs of the F11/F12/F14 false shapes + per-axiom non-vacuity witnesses) and `Refutations/` must-fail adapters, gated by `scripts/refutation-gate.sh` in audit.sh step 5 and CI; a re-loosened axiom now fails the build instead of surviving 135 commits |
| 2026-07-03 | G: guarded? (admission hardening) | landed | Axiom admission protocol (WORKFLOW.md: verbatim anchor, six-axis fidelity diff, degenerate attack, witness, model adequacy, fidelity footers); `ckc-axiom-check` v0.2.0 requires `Paper-Ref:`/`Refutation-Attempt:` on axiomatised commits; per-node axiom footprints in public CI (vendored `scripts/axiom-report`); per-claim `fidelity` records in claims.toml gated by `claimgraph audit --require-fidelity` |
| 2026-07-03 | F: prove (M4 discharge) | lemma_B_2 + lemma_B_1 machine-checked | The gated two-cap retention is PROVED (`Leaves.gated_twoCap_retention`): amplitude-scaled self-centered gated block recentered at an overlap point, sub-cap mass (B.6) + geodesic triangle inequality (Mathlib `angle_le_angle_add_angle`) + logistic reaching with the amplitude buying the fixed-`T` budget + the pushforward bridge. `lemma_B_2` flips axiom → theorem after two discharge-time statement restrictions (probability measure: infinite rim mass defeats any single block; sub-hemisphere radii: rim stalling / `±ω` in one cap), and `#print axioms lemma_B_1` = `propext, Classical.choice, Quot.sound` -- the Appendix-B chain is fully kernel-checked. Statement-layer axiom count 13 → 12 |
| 2026-07-04 | F: prove (M5 complete) | Section 3.3 disentanglement geometry machine-checked | Strict spherical caps are geodesically convex (`geodesicConvex_inner_cap`), ball-to-cap polarization bridges (`inner_cap_of_mem_ball`, `dist_le_of_inner_cap`), cap disjointness from `2r`-separation, and the two separation transfers: `geodesicHull_disjoint_of_separated_balls` (hulls of clusters in `2r`-separated `r`-balls are disjoint) and `barycenter_not_sameRay_of_separated_balls` (their barycenters are non-colinear; strict via the a.e. argument `inner_barycenter_gt`, normalization controlled by `norm_barycenter_le_one`). The geometry the paper uses without proof on p. 17 ('shrunk until achieving the separation') is now kernel-checked; `exists_disentangling_balls` owes only mean-field dynamics (M3b) and the family/fixing-clause composition (M8b path) |

## Node status (refresh from `bin/axiom-report`; run `scripts/audit.sh`)
Of the 30 blueprint nodes: **13 clean** (machine-checked), **17 axiom** (rest on a labeled axiom).
No node is `sorryAx` (zero `sorry` repo-wide). Representative:

| Node (`\lean{}` name) | Status | Notes |
| --- | --- | --- |
| `MeasureToMeasure.Leaves.*` (L1-L6, L8, L9, L10, L11, L11′) | clean | the self-contained leaf cores; L8 `markov_bound` machine-checked since the `W₁` discharge |
| `MeasureToMeasure.Axioms.W2` | axiom | opaque `W₂` (Mathlib has no OT) |
| `MeasureToMeasure.Axioms.measureFlow` / `flowMap` | axiom | continuity-equation flow (no Mathlib solver) |
| `MeasureToMeasure.Leaves.lemma_5_2` (L7) | axiom | rests on `W2` / `W2_map_le_L2` |
| `MeasureToMeasure.Statements.{prop_2_1,lemma_3_2,3_3,3_4,prop_4_2,lemma_5_1,5_4,lemma_B_2}` | axiom | placeholder mid-level axioms |
| `MeasureToMeasure.Statements.{theorem_1_1,theorem_1_2,prop_2_2,prop_3_1,prop_4_1,lemma_B_1}` | axiom | **proved** by assembly; effective status = min over the axiom closure |

**Coverage gap (addressed).** `claimgraph reconcile` had reported ~73 machine-checked nodes recorded in
the CKC history but *absent from* `blueprint/src/content.tex`. The 12 curated foundation results tracked
in `claims.toml` -- the Sierpiński IVT + atomless partition (M8a), geodesic convexity/hull (M5), sphere
invariance + flow algebra (M3 Phase 1), and the `W₁`/`W₂` optimal-transport substrate (M2) -- are now
added to the blueprint as a "Machine-checked foundations" section, each `\leanok` / `[machine-checked]`.
The remaining ungrounded names are internal helper lemmas that `claims.toml` intentionally does not
track as separate nodes, so they stay out of the blueprint by design.

## Experiment campaign (Phase F; `lean-math:numerical-validation`)
Seven seeded experiments (`experiments/E*`, seed 0), each cross-linked to the claim it tests. Verdicts
are seed-honest and never upgrade a node's kernel status. Detail (incl. the E6 strengthening) in the
appendix *Validation campaign*.

| Claim | Validates | After verdict | Figure |
| --- | --- | --- | --- |
| E1 mass transport | L2, L9, B.2, B.1 | PASS (retention 1.0 > `(1-ε)^K`) | per-stage retention vs floor |
| E2 clustering | Prop 2.1 | PASS (diam→0, `T(ε)~log 1/ε`) | contraction + rate |
| E3 disentangle | Prop 3.1, L6, L11 | PASS (min cross-dist 0.08→π) | separation over time |
| E4 matching | Prop 4.2/4.1, L3 | PASS (active→target, parked fixed) | selective motion |
| E5 Lyapunov | L5 | PASS (`E` nonincreasing, 200 trials) | `E(t)` ensemble |
| E6 end-to-end | Thm 1.1/1.2 | PASS (three phases distinct) | three-phase transport |
| E7 linear impossible | Thm 1.1 (necessity) | PASS (linear gap 0, attention gap 0.38) | obstruction vs escape |

## Publish state (Phase I; `lean-math:publish-site`)
- **Site built:** yes (`site/build.py` / `bin/build-site` -> `docs/`; runs `scripts/audit.sh` fail-fast).
- **Badges honest:** yes — `scripts/audit.sh` (axiom-report + `claimgraph audit`/`reconcile`) passes; no
  page badges a node above its `#print axioms` status.
- **Deployed:** yes (classic Pages on `main /docs`): http://quemy.info/measure-to-measure-transformers/

## Mathlib-ready candidates (Phase J; `lean-math:mathlib-ready`)
Staged in `ForMathlib/` (generalized to a real inner product space, `#print axioms`-clean, lint-clean,
Apache-headed). Preparation only — nothing is contributed to Mathlib. See `ForMathlib/README.md`.

| Node | General-purpose? | Staged in `ForMathlib/`? | Readiness |
| --- | --- | --- | --- |
| `InnerProductGeometry.tangentialProjector` (+ identities) | yes | yes (`TangentialProjector.lean`) | ready |
| `InnerProductGeometry.{angle_eq_arccos_inner,cos_angle,inner_le_one}_of_norm_eq_one` | yes | yes (`UnitSphereGeodesic.lean`) | ready |
| `InnerProductGeometry.inner_lt_cos_of_pi_div_two_le_angle` | yes | yes (`SeparatingHyperplane.lean`) | ready |
| `barycenter_noncolinear_of_disjoint_hull` (+ `_general`) | partial | no | evaluated; special-purpose + Bochner dep, left in-project |

## Citations to carry into the write-up
- Geshkovski, Rigollet, Ruiz-Balet, *Measure-to-measure interpolation using Transformers*,
  arXiv:2411.04551v3 (the formalized source).
- LaSalle invariance principle; Hartman-Grobman ([Shu13]) — the cited dynamical-systems machinery
  behind Prop 2.1's clustering/rate (axiom layer).
- Santambrogio, *Optimal Transport for Applied Mathematicians* — the OT background for M2.

## Open questions / next step
- **Blueprint refresh (done):** the 12 curated machine-checked foundation nodes (M8a Sierpiński + atomless
  partition, M5 geodesic convexity/hull, M3 sphere invariance + flow algebra, M2 `W₁`/`W₂` substrate) are
  now in `blueprint/src/content.tex` under a "Machine-checked foundations" section; `claimgraph reconcile`
  reports no stale-blueprint nodes. The Quarto proofs pages (`site/proofs/_*.qmd`) remain a curated
  narrative and are a separate, deliberately smaller representation.
- **`W₂` axiom discharge (in progress):** slices 1--2 done. The `W₂` (root) distance is a machine-checked
  **pseudometric** (`W2_triangle`, Minkowski + gluing) and is **convex under mixtures**
  (`W2_convexCombo_le`: if `∑ aₖ = 1` and every `W₂(Pₖ,Qₖ) ≤ ε`, so is the mixture), both in
  `Foundations/Wasserstein.lean`. That exhausts the standalone `W₂` facts the mid-level assembly needs.
  Remaining (slice 3, invasive): the all-or-nothing flip of `Axioms.W2` to a concrete definition,
  threading integrability through its consumers (L7 `Coupling.lean` / Prop 2.2 `MidLevel.lean` /
  Theorem 1.2 `MainResults.lean`).
- **M3 mean-field flow:** discharge `flowMap` (global existence + McKean-Vlasov well-posedness), gated
  on completing M2.

---

## Appendix: detailed working record

The sections below are the append-only detailed record (proof review, coverage analysis, per-node
closing notes, axiom surface, fidelity corrections), preserved verbatim; the dashboard above
summarizes and refreshes from them.

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

## Leaf scoreboard (Phase 4)

| Leaf | Content | Lean | Status |
| --- | --- | --- | --- |
| L1 | projector identity `⟪P_x^⊥v,v⟫ = ‖v‖²−⟪x,v⟫²` | `projector_inner_sub_sq` | machine-checked |
| L2 | gate algebra + gate ODE (B.4-B.5) | `gate_hasDerivAt_inner` | machine-checked |
| L3 | separating hyperplane (Prop 4.2 Step 1) | `separating_hyperplane` | machine-checked |
| L4 | geodesic-distance derivative + gradient (4.4) | `geodesicDist_hasDerivAt` | machine-checked |
| L5 | Lyapunov `Ė=−α sin²θ ≤ 0` (Ex. 6.1) | `lyapunov_hasDerivAt` | machine-checked |
| L6 | barycenter ODE + strict increase (B.9) | `barycenter_hasDerivAt_inner` | machine-checked |
| L7 | linearized OT bound (Lemma 5.2) | `lemma_5_2` | axiomatised (over `W2`) |
| L8 | Markov bound (Claim 2) | `markov_bound` | **machine-checked** (W₁ axiom discharged) |
| L9 | ball-chain retention (Lemma B.1) | `ball_chain_geom` | machine-checked |
| L10 | pigeonhole (Lemma 3.4 Part 1) | `exists_ne_in_ball` | machine-checked |
| L11 | disjoint hulls ⟹ non-colinear barycenters (F2) | `barycenter_noncolinear_of_disjoint_hull` | machine-checked |
| L11′ | F2 general case (any probability measure) | `barycenter_noncolinear_of_disjoint_hull_general` | machine-checked |

L8 is now **machine-checked** (`markov_bound`): the truncated-distance bump `min(η₃, d(·,x₀))` is
`1`-Lipschitz (`distBump_lipschitz`), and the Markov inequality `μ.real{d(·,x₀) ≥ η₃} ≤ Cη₂/η₃` is
derived from it via integral monotonicity and Kantorovich-Rubinstein duality. That duality step
(formerly the axiom `W1_ge_of_lipschitz`) is now a **proved theorem** discharged from the from-scratch
optimal-transport development (`ofReal_integral_sub_le_W1`), so `markov_bound`'s `#print axioms` lists
only `propext`/`Classical.choice`/`Quot.sound` — it no longer rests on any `W₁` axiom. The discharge
adds the honest hypotheses the earlier axiom elided: integrability of the bump (proved in-lemma) and
finiteness of `W₁(μ, δ_{x₀})` (automatic for the compactly-supported measures on the sphere).

The mid-level connective lemmas (Props 2.1, 2.2, 4.1, 4.2; Lemmas 3.2-3.4, 5.1, 5.4, B.1, B.2) are now
present as type-correct Lean statements in `Statements/MidLevel.lean` (`sorry` stubs, `math.open`),
stated against the existing axiom layer with **no new axioms** (`supportedIn μ S := μ Sᶜ = 0`,
barycenter `:= ∫ x ∂μ`). With the leaves, the headlines, and these, every statement of the paper now
appears in Lean.

Finding F2 is fully discharged: the empirical case (`barycenter_noncolinear_of_disjoint_hull`) and the
general probability-measure case (`barycenter_noncolinear_of_disjoint_hull_general`, via Mathlib's
`Convex.integral_mem`) are both machine-checked.

## Validation campaign (Phase 4)

Seven seeded experiments (`experiments/E*`) validate the quantitative content of the claims, each
cross-linked to the claim(s) it tests (the `tests = [...]` field on the `[claims.exp-*]` entries, and
a `Depends-On:` footer on the recording commit). Experiments are run **alongside** the proofs, not
batched at the end: a *before* probe shapes the hypothesis when needed (this is how F1's gate sign was
caught), and an *after* run always validates. Each run writes a verdict (`summary.json`), a provenance
manifest (`manifest.json`: git sha, time, host, versions), and at least one figure (`*.png` / `*.svg`)
that shows the verdict. The full cycle is documented in `WORKFLOW.md`.

| Exp | Tests | Verdict (seed 0) | Figure |
| --- | --- | --- | --- |
| E1 mass transport | L2, L9, B.2, B.1 | single-ball + 4-ball-chain retention = 1.0, beats `(1-eps)^K` | per-stage retention vs floor |
| E2 clustering | Prop 2.1 | diameter -> 0, `T(eps) ~ log(1/eps)` fit slope 1.00 | contraction + rate |
| E3 disentangle | Prop 3.1, Lem 3.3, L6, L11 | min cross-distance 0.08 -> pi (antipodal) | separation over time |
| E4 matching | Prop 4.2/4.1, L3 | active point -> target < eps, parked points fixed | selective motion |
| E5 Lyapunov | L5 (Ex. 6.1) | `E` nonincreasing, `theta(T) -> 0` over 200 trials | `E(t)` ensemble |
| E6 end-to-end | Thm 1.1/1.2 | three phases distinct, W2 proxy 0.0 for both measures | three-phase transport |
| E7 linear impossible | Thm 1.1 (necessity) | linear image gap 0, attention velocity gap 0.38 | obstruction vs escape |

All seven pass. E6 was strengthened during this phase: the original parameterization disentangled to
convergence, which also collapsed each cloud to a point and left the cluster phase a no-op (visible as
an empty middle panel); shortening the disentangle horizon (`t_span = 3`) keeps the supports disjoint
(cross-distance 2.62) while leaving each cloud with diameter ~0.18 for the cluster phase to contract,
so all three phases of `Phi_fin` are genuinely exercised.

## Adversarial proof review (Phase 1, deep pass)

Skeptical referee pass over the mid-level lemmas (`[informal]` blueprint nodes), reading the proofs
verbatim from the PDF with the intent to break them. Page numbers refer to arXiv 2411.04551v3.
Findings are ordered by severity; each ends with a fix or the question to resolve. The headline
result: the formalization caught one real (typographical but load-bearing) sign error in the paper,
and one genuine rigor gap. Everything else is sound, and the leaves L1-L10 correctly capture the
self-contained cores.

### F1 (SERIOUS, typographical) Lemma B.2 gate is active on the wrong side of the ball (eq. B.4, p.31)

The construction sets `U = -z 1ᵀ`, `b = cos(R) 1`, giving the gate
`g(x) = (cos R - cos d_g(z,x))₊ = (cos R - ⟨z,x⟩)₊`. The paper claims (B.4) that
`g(x) > 0 ⟺ x ∈ ℬ₀ = B(z,R)`. This is **false**: `cos R - ⟨z,x⟩ > 0 ⟺ ⟨z,x⟩ < cos R ⟺ d_g(z,x) > R`,
i.e. `g` is active on the *complement* of `ℬ₀`. Our kernel-checked leaf L2 (`gate_pos_iff_dist`)
proves exactly `g(x) > 0 ⟺ d_g(z,x) > R`, contradicting the printed (B.4).

Why it matters: the proof body (B.5, "positive whenever `x ∈ ℬ₀ \ {ω}`") needs the gate active
*inside* `ℬ₀` to push interior mass toward `ω ∈ ℬ₀ ∩ ℬ₁`. With the printed parameters the interior
mass has `g ≡ 0` and never moves, so the lemma as written cannot transport anything.

Fix: flip the sign, `U = +z 1ᵀ`, `b = -cos(R) 1`, giving `g(x) = (cos d_g(z,x) - cos R)₊ = (⟨z,x⟩ - cos R)₊`,
which is positive exactly on `ℬ₀`; then (B.4), (B.5) and the rest of the proof are correct. This is a
sign typo in the (U,b) definition, not a flaw in the statement. Two independent corroborations:
(i) Prop 4.2 Step 3 (p.22) uses the *identical* construction `U₃ = -ω 1ᵀ`, `b₃ = cos(3π/16) 1` and
correctly states `(U₃x+b₃)₊ = 0 for x ∈ B(ω,3π/16)` (active outside) - so the paper is internally
inconsistent between B.2 and §4; (ii) numerical experiment E1 failed at fraction 0.27 until the seed
region was moved to the gate-active side `{d_g(z,x) > R}`, the exact region L2 pins down.

### F2 (SERIOUS, rigor gap) Prop 3.1 uses "disjoint hulls ⟹ non-colinear barycenters" unproved (p.16)

The induction asserts: "Since `supp μ₀ ⊂ Q₁^{d-1}`, (3.3) implies that `ℰ_{μᵢ}[x]` is not colinear with
`ℰ_{μⱼ}[x]` for `i ≠ j ∈ [1,N-1]`," and from this that `ℰ_{μ_N}` is colinear with at most one of them.
The implication is stated, not proved. In the open positive cone `Q₁^{d-1}` colinearity of barycenters
means same ray (positive multiple, since all coordinates are positive), so "at most one" follows by
transitivity *if* the first claim holds - but two measures can a priori have disjoint geodesic-convex
hulls while their barycenters lie on a common ray. The argument needs the lemma "geodesically convex,
pairwise-disjoint subsets of the open orthant cap have pairwise non-colinear barycenters," which is
not supplied.

Why it matters: the entire case split (colinear-with-at-most-one, relabel as `N-1`, apply Lemma 3.4)
is well-defined only if `ℰ_{μ_N}` cannot be colinear with two distinct earlier barycenters.

**Resolved (leaf L11, machine-checked).** The implication is true, with a clean proof. Within an open
hemisphere, spherical geodesics are radial projections of chords, so `conv_g(s) = cone(s) ∩ 𝕊^{d-1}`.
The barycenter `∫ x dμ` is a nonnegative average of support points, hence lies in `cone(supp μ)`;
its normalization lies in `conv_g(supp μ)`. If two barycenters were colinear (same ray — both in the
positive orthant, so "colinear" is a positive multiple, i.e. `SameRay`), their common normalized
direction would lie in both hulls, contradicting disjointness. Leaf L11
(`barycenter_noncolinear_of_disjoint_hull`) formalizes this for the empirical barycenter `∑ wₚ • p`
(`wₚ ≥ 0`), kernel-clean — exactly the regime of Theorem 1.1 (Dirac targets) and restricted
Theorem 1.2 (empirical targets). The only residual for the general-measure case is the standard fact
"the barycenter of a probability measure lies in the closed convex hull of its support," which does
not reintroduce the optimal-transport axioms. The Prop 3.1 headline stays `math.open` (it still rests
on the flow / `conv_g`-nesting axioms), but the F2 gap itself is closed.

### F3 (MINOR, expected) Prop 2.1 rate and clustering rest on cited dynamical-systems machinery (p.11)

Two steps are not self-contained and are correctly in the axiom layer: (i) the limiting argument
"if `φ* > 0`, compactness yields times `t_k → ∞` with boundary points that do not move inward,
contradicting strict interior-pointing" is a LaSalle-type invariance argument stated informally;
(ii) the exponential rate `inf{t : W₂(μ(t),δ_z) ≤ ε} = O(log 1/ε)` is outsourced to
`[GLPR25, Theorem 2.3]` and not proved here. Both map onto our `LaSalle` / `Hartman-Grobman` axiom
boundary. No error; this confirms the boundary is drawn in the right place. The norm bound in
Theorem 1.1 (`O(dN/T + log 1/ε)`) inherits the `log 1/ε` term from this cited rate.

### F4 (MINOR, expected) Prop 2.1 interior-pointing of the attention field rests on geodesic convexity (p.11)

The load-bearing geometric fact is that `γ(x) = 𝒜_B[μ](x)/‖·‖` points strictly into
`int conv_g supp μ₀` at boundary points, established via "a first-order expansion." This is the
geodesic-convex-hull / time-nesting property (`conv_g supp μ(t₂) ⊂ conv_g supp μ(t₁)`), which Lemma
3.3 and Prop 3.1 also rely on ("`conv_g supp μ(t) ⊂ conv_g supp μ₀`", p.17). Mathlib has no geodesic
convexity, so this is axiomatized. Correct, not self-contained.

### F5 (CONFIRMED sound) Lemma 5.2 / L7 coupling bound (p.24)

`T¹` bijective ⟹ `∃ ψ` measurable with `ψ ∘ T¹ = T²`; then `(id, ψ)` pushed through `T¹_#μ` is a
coupling of `T¹_#μ` and `T²_#μ` with cost `∫‖x-ψ(x)‖² d(T¹_#μ) = ∫‖T¹-T²‖² dμ`, giving
`W₂²(T¹_#μ, T²_#μ) ≤ ‖T¹-T²‖²_{L²(μ)}`. The bijectivity hypothesis is load-bearing (without it `ψ` is
only defined on `range T¹`) and is correctly stated. Leaf L7 axiomatizes `W₂` itself but states this
exact coupling inequality as its content - faithful.

### F6 (CONFIRMED sound) Prop 4.2 matching: hypotheses and switch count (p.18-23)

`d ≥ 3` is necessary and used: picking `ω ⊥ γ` with `d_g(ω, x₀ᴹ) ≥ π/2` and `d_g(ω, yᴹ) ≥ π/2`
needs `γ^⊥` to be at least 2-dimensional. The "≤ 6 switches" matches the explicit 6-piece schedule
with `W₅ = -W₁, W₆ = -W₂` (the gather/restore symmetry). Step 1's separating bound is leaf L3
(`separating_hyperplane`): `d_g(ω,x) ≥ 3π/8 ⟹ ⟨ω,x⟩ < cos(π/8+τ)` via monotone `cos`. Step 2's
gradient-flow identity `ẋ = -f̄ ∇₁ d_g(x,ω₊)` with `∇₁ d_g = -P_x^⊥ω₊/√(1-⟨x,ω₊⟩²)` is leaf L4.
The cap `δ₊ = {⟨γ,x⟩ ≥ ε}` is geodesically convex because `ε > 0` makes it a cap of radius `< π/2`
(used for flow-invariance); worth stating but true. Convergence to `ω₊` (LaSalle) and the exponential
approach (Hartman-Grobman, `[Shu13]`) are axiomatized. Cores captured by L3 + L4; the rest is the
axiom layer. Sound.

### F7 (CONFIRMED sound) Lemma B.1 / L9 ball-chain retention (p.31)

Backward induction: in the last interval the flow acts on `ℬ_{K-1}` (B.2 with `ℬ₀ = ℬ_{K-1}`,
`ℬ₁ = ℬ_K`) and is the identity outside `ℬ_{K-1}`, so mass in `ℬ_K \ ℬ_{K-1}` is untouched
(`μ(T;ℬ_K\ℬ_{K-1}) = μ(t_{K-1};·)`) while `μ(T;ℬ_K∩ℬ_{K-1}) ≥ (1-ε)μ(t_{K-1};ℬ_{K-1})` by B.2;
the `|k-k'| ≥ 2` disjointness prevents interference. Unrolling gives `(1-ε)^K μ₀(⋃ℬ_k)`. Leaf L9
(`ball_chain_geom`) captures the arithmetic `a_K ≥ (1-ε)^K a₀`; the geometric non-interference is the
parking property (axiom). Faithful scoping. Sound.

### F8 (CONFIRMED sound) Lemma 3.4 Part 1 / L10 pigeonhole (p.16, proof App. B.3)

The `γ₁ = 1` case must produce parameters with `ℰ_{μ(T)} ≠ ℰ_{ν(T)}`; the obstruction to avoid is a
map forced constant on a support. Leaf L10 (`exists_ne_in_ball`) supplies the self-contained core: a
nonempty open ball contains a point `≠ a`, so no map is constant on it. The full Part-1 construction
(and Part 2, ≤ 2 switches) is deferred to Appendix B.3 and rests on the flow-map / `conv_g`-invariance
axioms; not re-derived. Core captured.

### F9 (MINOR) Lemma 3.2 uniform exit time over the family (p.15)

The proof picks `ω ∉ ⋃ᵢ supp μ₀ⁱ` and claims `∃ T₀` with `supp μⁱ(T₀) ⊂ B(-ω, π/8)` for all `i`.
Uniformity over `i` is implicit: it holds because `N` is finite and the supports are closed and avoid
a fixed neighborhood of `+ω` (the only repelling fixed point of `ẋ = -P_x^⊥ω`), giving a uniform
finite exit time by compactness. Worth one sentence in a formalization; not an error. The drift sign
(`d/dt⟨x,ω⟩ = -(1-⟨x,ω⟩²) < 0`, motion *away* from `ω` toward `-ω`) matches leaves L1/L2 and was the
sign cross-checked by experiment E1.

### F10 (MINOR) Theorem 1.2 ε/C bookkeeping is internally consistent (p.25-28)

General case: the disentangling map `Φ_{θ₁}` is bi-Lipschitz with constant `C` (5.3); the match step
is performed to tolerance `ε/C` (5.5, 5.6) via Lemmas 5.1/5.4/5.2; applying `Φ_{θ₁}^{-1}` reinflates
by `C` (5.3) to land at `ε` (Step 3). The logic is sound. Restricted case (a.c. inputs, `M`-atom
targets) replaces the packing/`L²`-approximation by `M` recursive applications of Lemma B.2 (Claim 1
selects ball radii by IVT on `f(s,r) = νⁱ(B(γ(s),r))`, valid since `νⁱ` is a.c.), giving the trackable
`O((d+M)N)` switch count. Bookkeeping checks out; the constants are uniform in `ε` as claimed
(dependence on `M,N` is explicit via `≲_{M,N}`). The dense per-symbol details rest on the OT / flow
axioms and were not re-derived line-by-line.

### F11 (SERIOUS, stub fidelity — fixed 2026-07-03) Three axiom stubs dropped load-bearing hypotheses

A second-pass audit of the *axiom statements themselves* (not the paper math, which F5-F10 covered)
found three `math.axiomatised` stubs in `Statements/MidLevel.lean` that were **false as written**,
because the type-correct stub elided hypotheses the paper carries. Each is refutable:

- `lemma_3_4_part1` kept only `barycenter μ = barycenter ν`. Refutable by `μ = ν`: the equal-barycenter
  hypothesis holds trivially, yet `measureFlow θ T μ = measureFlow θ T ν` for every `θ`, so no `θ`
  separates the barycenters. (Machine-checked disproof.)
- `lemma_3_4_part2` kept **no** relation between `μ` and `ν`. Refutable by `μ = ν`: barycenters coincide
  after any flow and `SameRay ℝ v v` always holds, so `¬ SameRay …` is unsatisfiable. (Machine-checked.)
- `lemma_5_1` dropped the disentanglement (disjoint-supports) context. Refutable with Diracs:
  `μ₀ 0 = μ₀ 1 = δ_a` with distinct targets forces one `ψ` to take two values at `a`; a shared target
  with distinct sources breaks bijectivity.

The paper's hypotheses (Lemma 3.4: "let `μ₀, ν₀ ∈ P(Q₁^{d-1})` be two *different* measures such that
`ℰ_{μ₀} = γ₁ ℰ_{ν₀}`, `γ₁ ∈ (0,1]`"; Lemma 5.1: measures taken from Proposition 3.1 applied to *both*
families, i.e. pairwise-disjoint supports) were **restored**: `μ ≠ ν`, `IsProbabilityMeasure`, orthant
support, and the `γ ∈ (0,1)` colinearity for 3.4; `DisjointSupports μ₀` and `DisjointSupports μ₁` for
5.1. This is the same class of fix as prop_4_2 (injectivity) and lemma_B_2 (geodesic balls).

**Blast radius: none on proved results.** All three are *orphan* axioms — `#print axioms theorem_1_1`
= {cluster_to_point, exists_disentangling_balls, exists_parked_schedule} and `theorem_1_2` additionally
uses only `lemma_5_4`; none reference 3.4/5.1. So no proved theorem ever rested on the false stubs, and
the layer was never *jointly* inconsistent in a way the kernel could exploit (nothing derived `False`).
Lesson: a per-node `#print axioms` check cannot see a false-but-unused axiom; axiom statements need
their own fidelity review against the paper's hypotheses, not just a review of the paper's math (F8
confirmed the paper's Lemma 3.4 sound but did not audit the stub's hypotheses).

### F12 (SERIOUS, stub fidelity — fixed 2026-07-03) Per-measure axioms dropped sphere/support hypotheses

A third-pass audit (full fidelity matrix against the paper plus a kernel refutation harness) found
that most remaining axiom stubs quantified over objects far beyond the paper's `P(S^{d-1})` data
and were **false as written**. Kernel-refuted (compiling `False` scratch proofs, each depending on
exactly the target axiom plus Lean's three standard axioms):

- `lemma_3_2` and `lemma_3_3`: quantified over EVERY measure; refuted with the Lebesgue measure
  (`flowMap` is a Lipschitz bijection, so the pushforward of an open-positive infinite measure
  cannot be annihilated off the orthant or inside a bounded ball).
- `cluster_to_point`: the target `z` ranged over all of `Eucl d`; refuted with an off-sphere Dirac
  target (the flow keeps sphere mass on the sphere; `W₂(δ_p, δ_q) = dist p q` was proved exactly
  over the coupling definition, no `toReal` collapse).
- `lemma_3_4_part1/part2` (post-F11): `orthant d` is the AMBIENT positive orthant, so heavy-tailed
  orthant probability measures were admissible; their identity map is not Bochner-integrable, both
  barycenters are the junk value `0`, and no flow separates them (`SameRay ℝ 0 0` always holds).

In-system refutable (mechanism verified against kernel-checked theorems, disproofs not filed):

- `prop_4_2`: no sphere membership on the points; steering `e₁` to `2 • e₁` contradicts
  `flowMap_mem_sphere`.
- `lemma_B_2` at `d = 1`: radial tangency forces the field to vanish at `±1`, so both sphere
  points are fixed; with `R₀ > π` the ball is the whole two-point sphere and a Dirac at `1`
  refutes retention into `ℬ₁ = {-1}`.
- `exists_parked_schedule` at `d = 1, 2`: flow maps are monotone (resp. cyclic-order-preserving)
  homeomorphisms, so two Dirac targets cannot be swapped.

**Fixes** (this commit): probability + sphere support + `MissingCap` (the paper's
`⋃ supp ⊊ S^{d-1}` as a positive cap gap) for `lemma_3_2`; probability + sphere + orthant support
and an on-sphere `α` for `lemma_3_3`; sphere supports for `lemma_3_4_part1/part2`; on-sphere
points for `prop_4_2` (threaded through `prop_4_1`); `d ≥ 3`, on-sphere target, sphere support and
a `1 + 6` piece budget for `cluster_to_point`; probability, sphere support, measurable and a.e.
sphere-valued `ψ` for `lemma_5_4` (with the sphere-valued clause added to `Matchable`); `d ≥ 2`
and proper cap radii `R ∈ (0, π)` for `lemma_B_2` (threaded through `lemma_B_1`); `d ≥ 3` and
summed switch budgets for `exists_parked_schedule`. `prop_2_2` and `theorem_1_1/1_2` re-proved
with the threaded hypotheses; `prop_2_2` now carries an explicit `9 M` piece budget. Switch-count
convention recorded: Lean's `switches` counts constant PIECES; the paper counts discontinuities.

**Blast radius: statements only.** `#print axioms` footprints of all assembled results are
unchanged. The refutation scratch files fail to typecheck against the repaired statements
(regression evidence), and the untouched `exists_disentangling_balls` refutation still compiles
(see F14).

### F13 (paper statement/proof mismatch — fixed 2026-07-03) Lemma 5.1's "invertible ψ" is unsatisfiable

Even with F11's disjoint-supports repair, `lemma_5_1`'s conclusion `Function.Bijective ψ` is
unsatisfiable WITHIN a single pair: an atomless source with a Dirac target is matchable, but no
injection pushes an atomless measure onto an atom. The root cause is in the paper: Lemma 5.1
(p.24) prints "Lipschitz-continuous and invertible `ψ`", but its own proof (B.4, p.37) builds
`ψ^i = T^i_{Φ₃} ∘ T^i ∘ (T^i_{Φ₁})^{-1}` where the per-pair transport `T^i` need not be
invertible. Recorded as erratum candidate E2 in `ERRATA.md`; the Lean conclusion now keeps
measurability and drops invertibility, which is what the downstream `W₂` argument uses.

### F14 (STRUCTURAL, fixed 2026-07-03) The flow model was a linear continuity equation; disentanglement needs measure dependence

`measureFlow θ t μ := μ.map (flowMap θ t)` is a measure-INDEPENDENT pushforward — a linear
continuity equation. The paper's own eq. (1.7) proves such dynamics cannot interpolate, and its
central point (p.6) is that the measure dependence of self-attention is what makes disentanglement
possible. Consequently `exists_disentangling_balls` is refutable in the current model no matter
what per-measure hypotheses are added: two inputs with EQUAL supports (e.g. identical measures, or
interleaved dense atoms) cannot be sent into disjoint balls by ONE map (a kernel disproof via
dense-in-sphere atoms compiles; a two-identical-Diracs disproof is a ten-liner). No hypothesis
short of "already disentangled" fixes this linearly.

**Decision (2026-07-03):** build the full attention-field model — the concrete self-attention
velocity `v[μ]` with the paper's parameters, a mean-field-flow predicate, and a single
well-posedness axiom (the true M3 completion) — then restate the family-level axioms and
Theorems 1.1/1.2 over transformer schedules. Until that lands, `exists_disentangling_balls` (and
hence the assembled `prop_3_1`, `theorem_1_1`, `theorem_1_2`) remain honest about this in their
docstrings and here.

**Progress (2026-07-03):** the mean-field interface landed in `Foundations/Attention.lean`
(`AttnParams`, the concrete field of eq. (1.2) with the softmax average `attnAvg`,
`IsMeanFieldFlow`, the axiom pair `exists_meanFieldFlow`/`meanFieldFlow_unique`, and the schedule
operator `attnMeasureFlow` with probability/sphere preservation).

**Fixed (2026-07-03, Statements restatement):** every statement now lives on the layer its own
paper construction uses. Linear layer (`V ≡ 0`, measure-independent, faithfully): `lemma_3_2`
(W-only), `lemma_3_4_part1`, `prop_4_2`/`prop_4_1`, `lemma_B_2`/`lemma_B_1`, and `prop_2_2`
(the §2.2 gated construction; its former machine-checked assembly used the mixture linearity
`Φ_#(∑ αₖ Pₖ) = ∑ αₖ Φ_# Pₖ` through attention-based steps, which is meaningless for mean-field
dynamics — a mixture evolves as ONE system — so `prop_2_2` is now a labeled axiom whose honest
derivation is a future assembly over `lemma_B_1`). Mean-field layer (`AttnSchedule` /
`attnMeasureFlow`): `prop_2_1`, `lemma_3_3`, `lemma_3_4_part2`, `cluster_to_point`, `lemma_5_4`,
`exists_parked_schedule`, `exists_disentangling_balls` (now also requiring the paper's standing
assumption `μ₀^i ≢ μ₀^j` and exposing the per-member flow maps with on-sphere inverses),
`prop_3_1`, `theorem_1_1`, `theorem_1_2`. `SharedMissingDirection` strengthened to the positive
cap-gap form (the faithful (1.4)/(1.5)). The dense-atoms kernel disproof of the old
`exists_disentangling_balls` no longer typechecks; the axiom footprints of the main theorems now
include `exists_meanFieldFlow` (correct: the results are about the mean-field dynamics).

**Budget-deferral policy:** switch budgets are stated only where the paper is explicit (one piece
for Prop 2.1, two for Lemma 3.2, six for Prop 4.2, seven for the cluster-and-steer composite, one
per ball for B.2, sums for parking). Where the paper writes `O(d·N)`/`O(M)` with a non-explicit
constant (disentanglement, Prop 2.2, the main theorems), the budget clause is deliberately
DEFERRED rather than invented: a made-up constant would risk a false axiom. Parameter-norm bounds
(`O(dN/T + log 1/ε)`) are now expressible (AttnParams carries genuine operators) and remain
future work.

### F15 (paper erratum candidate) B.1/B.2 print a quantifier order their proofs do not support

Paper Lemmas B.1/B.2 (p.31) are printed "there exist parameters such that for all
`μ₀ ∈ P(S^{d-1})` …", but the proof of B.2 chooses `δ` (hence the parameters' time budget) AFTER
`μ₀` ("small enough so that `μ₀(B(z, R−δ)) ≥ (1−ε) μ₀(ℬ₀)`", p.32), and the uniform order looks
refutable outright: for fixed parameters and horizon, a Dirac slid close enough to the rim of
`ℬ₀` has an arbitrarily small gate and cannot reach `ℬ₀ ∩ ℬ₁` in time `T`. The Lean statements'
`∀ μ ∃ θ` order is the provable one. Recorded as erratum candidate E3 in `ERRATA.md`.

### F16 (internal, docs — fixed 2026-07-03) lemma_B_1's K = 0 justification was wrong

The docstring justified retaining `μ ℬ₀` instead of the paper's `μ (⋃ ℬ_k)` by claiming the union
makes the `K = 0` base case false. It does not: the paper's union is bounded (`k ∈ [0, K]`), so at
`K = 0` the union IS `ℬ₀` and the paper's base case is true. The real obstruction is that the Lean
`lemma_B_2` drops the paper's localization clause (flow = Id on `S^{d-1} ∖ ℬ₀`) and the
`|k − k'| ≥ 2` disjointness hypothesis, which the union form needs so that mass already sitting in
later balls stays put during earlier legs. Docstring corrected.

### Verdict

- **Ready to formalize as stated** (cores already kernel-checked): L1-L7, L9, L10 capture the
  self-contained content of B.2/B.5 (with the F1 sign correction), 5.2, B.1, 3.4-Part-1, Prop 4.2
  Steps 1-2, faithfully.
- **Ready after fixes**: Lemma B.2 needs the F1 sign correction (`U = +z1ᵀ, b = -cos(R)1`); the
  statement is true once corrected. Our Lean L2 already uses the mathematically correct gate identity.
- **F2 resolved**: Prop 3.1's "disjoint hulls ⟹ non-colinear barycenters" step is now the
  machine-checked leaf L11 (`barycenter_noncolinear_of_disjoint_hull`) for the empirical regime; only
  the standard "barycenter ∈ closed convex hull of support" remains for general measures (closed by
  leaf L11′). Prop 3.1 itself is now a faithful axiom (`math.axiomatised`); see Phase 7 below.
- No errors found that threaten the main theorems; the one real bug (F1) is a recoverable sign typo,
  and the formalization plus the numerical campaign caught it independently.

## Node status

See `claims.toml` for the authoritative registry. As commits land, each node advances from
`math.proved-informal` to `math.axiomatised` or `math.machine-checked`. A node's *effective* status
is the minimum over its `Depends-On` / `Assumes` closure, so any result above an axiom reads
`math.axiomatised`, honestly.

## Closing the open statements (Phase 7)

All 15 `sorry` stubs (the 3 headline statements + the 12 mid-level lemmas) are now discharged:
`lake build` is green with **zero `sorry`** repo-wide, and `#print axioms` on every closed statement
shows no `sorryAx`. A literal Mathlib-first-principles proof is impossible (the optimal-transport /
continuity-equation / geodesic-convexity / LaSalle infrastructure is absent), so the posture is
*axiomatize-and-assemble*: the irreducible analytic facts are clearly labeled axioms, and the results
above them are **proved** by assembling those facts, so the kernel verifies the paper's logical
skeleton. Effective status of everything here is `math.axiomatised`.

### What is proved vs axiomatized

- **Proved (genuine Lean, effective `math.axiomatised`):**
  - `theorem_1_1` and `theorem_1_2` (the two main theorems), assembled along
    `Φ_fin = (Φ_θ₁)⁻¹ ∘ Φ_θ₂ ∘ Φ_θ₁`. Theorem 1.2's `W₂` bookkeeping (transport map through the
    inverse flow, then `L²`-to-`W₂` via L7) is machine-checked.
  - `lemma_B_1` (ball-chain mass retention), a real induction over `lemma_B_2` and the flow algebra.
  - `prop_4_1` (match an ensemble), proved by induction on `M` over `prop_4_2` and the flow algebra
    (place one point per step; `6k + 6 = 6(k+1)` switch budget machine-checked via `switches_comp`).
  - `prop_2_2` (cluster to a discrete measure), proved over the probability-measure layer (needs
    `0 < d`): partition the atomless `μ` into probability pieces of the prescribed weights with
    pairwise disjoint supports (`exists_atomless_partition`); per piece, rotate into the orthant with
    one switch (`lemma_3_2`) — the orthant sits in a basis direction's open hemisphere — then cluster
    to its target (`cluster_to_point`), composing the schedules (`measureFlow_comp`); run all pieces
    with one parked schedule (`exists_parked_schedule`), then lift the per-piece bounds by the
    convexity of `W₂` under mixtures (`W2_convexCombo_le`). `measureFlow` distributes over the convex
    combination (`measureFlow_sum_smul`); the mixture bookkeeping is machine-checked.
  - `prop_3_1` (disentanglement), proved from `exists_disentangling_balls`: the disjointness +
    hemisphere packaging the paper states without proof (review finding F2) is machine-checked
    (`Metric.ball_disjoint_ball` from `2r`-separation; Cauchy-Schwarz `‖x - α i‖ < r < 1` forces
    `⟪α i, x⟫ > 1 - r > 0`). The dynamical construction stays in the more-primitive axiom.
  - `exists_atomless_partition` (atomless prescribed-mass decomposition), **fully de-axiomatized**
    (milestone M8a **complete**): normalize the restrictions `(αₖ)⁻¹ • μ.restrict(Aₖ)` to a disjoint
    partition carved by iterating the now-proved Sierpiński IVT
    (`Foundations.exists_disjoint_subset_measure_eq` then `exists_probability_decomposition`). Assumes
    positive weights (`αₖ ≠ 0`) so each piece is a genuine probability measure. Its `#print axioms`
    now lists **only** `propext`/`Classical.choice`/`Quot.sound` — the bespoke partition axiom *and*
    the Sierpiński IVT axiom beneath it are both gone, so `prop_2_2` no longer rests on any
    measure-theoretic axiom.
  - **Geodesic convexity on the sphere** (`Foundations/GeodesicConvex.lean`), milestone **M5**,
    foundations slice. `GeodesicConvex s` := `s ⊆ 𝕊` and closure under normalized positive chords
    `‖a·x + b·y‖⁻¹ • (a·x + b·y)` (`a,b > 0`) — the pure inner-product characterization, which on an
    open hemisphere coincides with the minimizing-geodesic-arc definition. Machine-checked lemmas:
    `geodesicConvex_open_hemisphere` (an open spherical hemisphere `{x ∈ 𝕊 | 0 < ⟪e,x⟫}` is
    geodesically convex — the paper's orthant/hemisphere confinement), `geodesicConvex_singleton`,
    `GeodesicConvex.inter` / `geodesicConvex_iInter` (so an orthant, an intersection of hemispheres, is
    geodesically convex). Mathlib has `Convex`/`ConvexCone`/`SameRay` but no geodesic convexity, so this
    is built in-repo. First slice toward the disentanglement geometry behind `exists_disentangling_balls`
    and a generalization of leaf L11; does not yet discharge an axiom.
  - **Geodesic hull is geodesically convex** (`Leaves/GeodesicHullConvex.lean`), M5 hull-bridge slice.
    Connects L11's `geodesicHull s = cone(s) ∩ 𝕊^{d-1}` to the `GeodesicConvex` predicate:
    `geodesicConvex_geodesicHull` — if `s` lies in the open hemisphere of `e` (`∀ p ∈ s, 0 < ⟪e,p⟫`),
    then `geodesicHull s` is geodesically convex; `geodesicHull_subset_hemisphere` — and it sits inside
    that hemisphere. This machine-checks the "`hull = cone ∩ sphere` is geodesic-convex" characterization
    the paper asserts, giving the geometric picture behind Section 3.3 (disjoint hulls inside a common
    hemisphere). Supporting: `inConicalSpan.add`, `inner_pos_of_inConicalSpan`. Kernel-clean.
  - **Geodesic hull is the smallest geodesic-convex set** (`Leaves/GeodesicHullConvex.lean`), M5
    minimality slice. `geodesicHull_subset_of_geodesicConvex` — if `C` is geodesically convex and
    contains every point of `s`, then `geodesicHull s ⊆ C` (the universal property of a hull). Proved by
    `Finset.induction` (`normalize_conical_mem`): each normalized conical combination is rebuilt as an
    iterated normalized positive chord that stays in `C`. Companions `geodesicHull_mono`,
    `mem_geodesicHull_self`, `inConicalSpan.mono`. Together with `geodesicConvex_geodesicHull` this
    closes the hull characterization (`hull = cone ∩ sphere = smallest geodesic-convex set`). Kernel-clean.
  - **Separating-hyperplane criterion for hull disjointness** (`Leaves/GeodesicHullConvex.lean`), M5.
    `geodesicHull_disjoint_of_separated` — a direction `e` positive on `s₁` and negative on `s₂` separates
    their hulls (disjoint); `inner_neg_of_inConicalSpan` (mirror); `barycenter_noncolinear_of_separated`
    composes it with leaf L11 to get non-colinear barycenters from a separating hyperplane. The clean
    sufficient condition Section 3.3 uses to make two clusters' hulls disjoint. Kernel-clean.
  - **`measureFlow` as a pushforward** (`Axioms/ContinuityEquation.lean`, `Axioms/Dynamics.lean`), the
    first M3 slice (ODE-free). `measureFlow θ t μ` is now **defined** as `μ.map (flowMap θ t)` rather than
    an opaque axiom, so `measureFlow_map` is definitional (`rfl`) and the measure-level semigroup laws
    `measureFlow_comp` / `measureFlow_id` / `measureFlow_inv` are now **derived theorems** (from
    `Measure.map_map` / `Measure.map_id` plus point-level flow facts). This removed the `measureFlow`
    constant and 4 measure-level axioms, replacing them with the two more-primitive point-level axioms
    `flowMap_id` (`flowMap idParams = id`) and `flowMap_inv` (`flowMap (inv θ) T ∘ flowMap θ T = id`);
    `flowMap_comp` already existed. Net −3 axioms, and the surface is now closer to "the most primitive
    faithful point" (the genuine ODE content is isolated in `flowMap`). Effective status of the layer
    stays axiomatised — it still rests on `flowMap` (Mathlib has no continuity-equation solver).
  - **Concrete schedule algebra** (`Axioms/ContinuityEquation.lean`, `Axioms/Dynamics.lean`), second M3
    slice (ODE-free). `Params d` is now **defined** as `List (Block d)` (`Block` an opaque per-block
    field parameter), so `idParams = []`, `comp = (· ++ ·)`, `inv = List.reverse`, `switches =
    List.length` are **definitions**, and `switches_comp` / `switches_id` are **derived theorems** (list
    arithmetic). This removed the opaque `Params`/`comp`/`idParams`/`inv`/`switches` constants and the
    two switch-budget axioms, so the depth/switch accounting behind `prop_4_1` (`6M`) and `lemma_B_1`
    (`K`) is now *proved*, not assumed. The only remaining schedule-layer opacity is `Block` and the
    `flowMap` facts over it.
  - **Sphere invariance of the layer-normalized flow** (`Foundations/SphereFlow.lean`), milestone **M3**,
    Phase 1 foundation (ODE-based, reusable). `sphere_invariant` — an integral curve of the
    tangentially-projected field `ẋ = P_x^⊥(g t)` that starts on `𝕊^{d-1}` stays on it throughout `[0,T]`,
    given a uniform bound on the raw radial drift `⟪x t, g t⟫` (automatic when `g` is bounded, e.g. the
    attention field on the compact sphere). The care point: `P_x^⊥ g` is tangent *only on* the sphere —
    `inner_tangentialProjector_left` gives `⟪x, P_x^⊥ w⟫ = ⟪x,w⟫(1 − ‖x‖²)`, which vanishes exactly at
    `‖x‖ = 1` — so `u(t) = ‖x t‖² − 1` solves the *linear homogeneous* ODE `u′ = c(t) u` with `u(0) = 0`,
    and Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le` + `gronwallBound_ε0_δ0`) forces `u ≡ 0`.
    Grönwall core isolated as `norm_sq_eq_one_of_radial_tangent`; the derivative of `‖x‖²` along a curve
    as `hasDerivAt_norm_sq_sub_one` (via `HasDerivAt.inner`). Reuses Mathlib's ODE/Grönwall substrate; the
    continuity-equation layer itself is absent from Mathlib, so this in-repo lemma is the geometric
    well-posedness core the mean-field flow (M3) and the LaSalle/Lyapunov convergence (M6) both rest on.
    Kernel-clean. Reusable infrastructure; does not yet discharge a paper flow axiom (that is M3 Phase 4).
  - **Flow algebra of an autonomous Lipschitz field** (`Foundations/SphereFlow.lean`), M3 Phase 1
    completion. Mathlib has *local* Picard–Lindelöf, global *uniqueness* (`ODE_solution_unique_univ`),
    and the Grönwall trajectory bound (`dist_le_of_trajectories_ODE`), but **no** global-existence
    continuation and **no** constructor turning a Lipschitz field into a `Flow` object (only `Flow.id` /
    `Flow.fromIter`). Rather than fabricate or axiomatize the `Flow` object, the flow *properties* the
    paper uses are proved per integral curve of the autonomous field `v ≡ V`: `integralCurve_unique`
    (curves agreeing at `0` are equal — injectivity behind `flowMap_bijective`), `integralCurve_dist_le`
    (`dist(γ₁ t)(γ₂ t) ≤ dist(γ₁ 0)(γ₂ 0) e^{K t}`, `t ≥ 0` — the Lipschitz-in-initial-value estimate
    behind `flowMap_lipschitz`, and *axiom-free*), `integralCurve_eq_of_field_zero` (field zero at `x` ⟹
    the curve through `x` is constant — the `Parked` / `flowMap_id_on_parked` content),
    `integralCurve_comp_add` + `integralCurve_semigroup` (`η t = γ(s+t)` — the `flowMap_comp` semigroup
    law `Φ^{s+t} = Φ^t ∘ Φ^s`). This is the genuine mathematical content of the four flow axioms; the only
    remaining gap is the (missing-in-Mathlib) global-existence packaging turning "for a given curve" into
    "for the flow map". Kernel-clean; does not yet discharge a paper flow axiom (needs global existence +
    the mean-field coupling, M3 Phase 4, gated on optimal transport M2).
  - **Optimal transport: couplings and the `W₁` Kantorovich cost** (`Foundations/Wasserstein.lean`),
    milestone **M2**, Phase 0/2 opening. Mathlib has the Lévy–Prokhorov metric but **no** optimal
    transport (no couplings, no Wasserstein, no Kantorovich duality; `Axioms/Wasserstein.lean`
    axiomatizes `W1`/`W2`). Built from scratch on `Measure.prod` / `Measure.fst` / `Measure.snd`:
    `IsCoupling π μ ν := π.fst = μ ∧ π.snd = ν` (a transport plan with fixed marginals), with
    `isCoupling_prod` (independent coupling), `isCoupling_diagonal` (the zero-cost diagonal plan), and
    `IsCoupling.swap` (coordinate swap exchanges marginals). The cost `transportCost π = ∫⁻ edist p.1 p.2 ∂π`
    (ℝ≥0∞-valued), with `transportCost_swap`/`transportCost_diagonal`. `W1 μ ν = ⨅` over couplings of the
    cost; on the ℝ≥0∞ lattice the metric facts hold unconditionally: `W1_le_transportCost`,
    `W1_self_eq_zero`, `W1_comm`. Kernel-clean. The first real slice of M2; the harder facts — the
    Kantorovich–Rubinstein bound (signed integrals), the triangle inequality (gluing of couplings), and
    completeness — are deferred, and the `W1`/`W2` axioms are not yet discharged (that is the M2 rewiring
    once KR + triangle land). This is the gating prerequisite for the mean-field flow (M3 Phase 3–4).
  - **Kantorovich–Rubinstein lower bound for `W₁`** (`Foundations/Wasserstein.lean`), M2. For a
    `1`-Lipschitz test function `f`, the dual pairing lower-bounds the transport cost of every coupling,
    hence lower-bounds `W₁`. `lipschitz_integral_sub_le_transportCost` (per coupling): `∫ f dμ − ∫ f dν ≤
    ∫ dist(x,y) dπ` — push `f` through both marginals (`integral_map`), bound the integrand by `dist p.1 p.2`
    (`LipschitzWith.dist_le_mul` + `le_abs_self`), integrate (`integral_mono`). `ofReal_integral_sub_le_W1`
    (descent): `ENNReal.ofReal (∫ f dμ − ∫ f dν) ≤ W₁ μ ν` for integrable `1`-Lipschitz `f` — per coupling,
    either the cost is `⊤` (trivial) or finite, whence `dist` is `π`-integrable
    (`hasFiniteIntegral_iff_ofReal`) with integral `(transportCost π).toReal`
    (`integral_eq_lintegral_of_nonneg_ae`), and `ofReal(toReal) ≤ id` closes it. This is **exactly the
    content of the axiom `W1_ge_of_lipschitz`** (the paper's Markov bound, Claim 2); discharging that axiom
    now reduces to threading the ℝ≥0∞/ℝ bookkeeping at the use sites. Kernel-clean. Requires integrability
    hypotheses the general axiom elides; the triangle inequality and completeness remain for the full M2.
  - **Triangle inequality for `W₁` via gluing** (`Foundations/Wasserstein.lean`), M2.
    `exists_coupling_transportCost_le` (the **gluing lemma**): given a coupling `π₁` of `(μ,ν)` and `π₂`
    of `(ν,ρ)`, there is a coupling `γ` of `(μ,ρ)` with `cost γ ≤ cost π₁ + cost π₂`. Construction:
    disintegrate `π₂ = ν ⊗ₘ κ₂` (its conditional `z|y`, via `Measure.disintegrate` + `condKernel`), lift
    `κ₂` to a `Y`-reading kernel on `X×Y` (`Kernel.comap Prod.snd`), form the triple `T = π₁ ⊗ₘ κ` on
    `(X×Y)×Z`; the `(X,Y)`-marginal is `π₁` (`fst_compProd`), the `(Y,Z)`-marginal collapses to
    `ν ⊗ₘ κ₂ = π₂` (`Measure.ext_of_lintegral` + `lintegral_compProd`, using the shared marginal
    `π₁.snd = ν = π₂.fst`), and the `(X,Z)`-marginal `γ` has cost bounded by `edist x z ≤ edist x y +
    edist y z` (`edist_triangle`) + Tonelli. `W1_le_transportCost_add` (per coupling) and `W1_triangle`
    (`W₁ μ ρ ≤ W₁ μ ν + W₁ ν ρ`, descending through the two infima via `ENNReal.iInf_add`/`add_iInf`).
    With `W1_self_eq_zero` + `W1_comm` this makes `W₁` a **pseudometric** on probability measures. Uses
    Mathlib's disintegration/kernel machinery (`condKernel`, `⊗ₘ`, `lintegral_compProd`) which the paper's
    OT layer is not otherwise built on. Kernel-clean. `W₂` and the `Axioms/Wasserstein.lean` rewiring remain.
  - **Quadratic Wasserstein cost `W₂²` and the map-coupling bound** (`Foundations/Wasserstein.lean`), M2.
    Mirrors the `W₁` construction for the quadratic cost: `sqTransportCost π = ∫⁻ edist(x,y)² ∂π`,
    `W2sq μ ν = ⨅` over couplings (the squared `W₂`, ℝ≥0∞-valued), with the unconditional facts
    `W2sq_self_eq_zero`, `W2sq_comm`, `W2sq_le_sqTransportCost`. `W2sq_map_le` (**Lemma 5.2, squared form**):
    `W₂²(T₁_# μ, T₂_# μ) ≤ ∫⁻ edist(T₁ x, T₂ x)² ∂μ`, the squared `W₂` between two pushforwards bounded by
    the `L²` cost of moving `T₁` to `T₂`, witnessed by the map coupling `(T₁,T₂)_# μ` (marginals via
    `fst_map_prodMk`/`snd_map_prodMk`, cost via `lintegral_map`). This is the content of the axiom
    `W2_map_le_L2`, in squared ℝ≥0∞ form. Kernel-clean. Deferred: the square root recovering `W₂`, the `W₂`
    triangle inequality (Minkowski/gluing), `W2_convexCombo_le`, and the `Axioms/Wasserstein.lean` rewiring.
- **Axiomatized (faithful, cited):** the irreducible mid-levels `prop_2_1`,
  `lemma_3_2/3.3/3.4`, `prop_4_2`, `lemma_5_1`, `lemma_5_4`, `lemma_B_2`.

### Axiom surface (what every closed statement ultimately rests on)

Beyond the core `propext` / `Classical.choice` / `Quot.sound`:

- **Wasserstein layer** (`Axioms/Wasserstein.lean`): `W2` and its facts `W2_map_le_L2` (L7 coupling),
  `W2_triangle`, `W2_convexCombo_le` (convexity of `W₂` under probability mixtures) remain axioms.
  **Discharged:** `W1` is now a *definition* (`(Foundations.W1 μ ν).toReal`) and `W1_ge_of_lipschitz`
  (KR duality) is a *proved theorem* (from `Foundations.ofReal_integral_sub_le_W1`), so the Markov
  bound (L8) no longer rests on any `W₁` axiom. Discharging the `W₂` facts is future work (it needs the
  integrability hypotheses threaded through the mid-level assembly, plus the `W₂` triangle/convexity).
- **Continuity-equation layer** (`Axioms/ContinuityEquation.lean`): `Block` (opaque per-block field
  parameter), `flowMap`, `flowMap_lipschitz`, `flowMap_bijective`, `Parked` + `flowMap_id_on_parked`.
  (`Params := List (Block d)`, `switches := List.length`, and `measureFlow := μ.map (flowMap θ t)` are
  now **definitions**, not axioms.)
- **Structural flow algebra** (`Axioms/Dynamics.lean`): the axioms are the point-level flow facts
  `flowMap_comp` / `flowMap_id` / `flowMap_inv`. Everything else is now **derived**: `comp` (`++`),
  `idParams` (`[]`), `inv` (`List.reverse`) are definitions; `switches_comp` / `switches_id` are
  theorems (list arithmetic); the measure-level `measureFlow_comp` / `measureFlow_id` /
  `measureFlow_inv` and `measureFlow_map` are theorems (via `Measure.map_map` / `Measure.map_id`).
  Standard semigroup / well-posedness facts; structural, not conclusions of the paper.
- **Analytic mid-levels** (`Statements/MidLevel.lean`): `prop_2_1`, `prop_2_2`, `lemma_3_2`,
  `lemma_3_3`, `lemma_3_4_part1/2`, `prop_4_2`, `lemma_5_1`, `lemma_5_4`, `lemma_B_2`,
  `cluster_to_point` (single-measure controllability = Prop 2.1 + Prop 4.1). (`prop_4_1` is *proved*
  from `prop_4_2`.)
- **Construction-level** (`Statements/MidLevel.lean`, `Statements/MainResults.lean`):
  `exists_disentangling_balls` (the geometric output of the Section 3.3 disentanglement; `prop_3_1`
  is *proved* from it) and `exists_parked_schedule` (Appendix B parking / simultaneous action on a
  disjoint-support family).
- **Measure-theoretic primitive — DISCHARGED (no longer an axiom).**
  Sierpiński's IVT is now fully machine-checked in `Foundations/AtomlessSplitting.lean`. The ℝ-case
  `exists_measurableSet_subset_measure_eq_real` (a measurable subset of `E` of any prescribed value
  `r ≤ μ E`) is *proved* directly: `t ↦ (μ(E ∩ Iic t)).toReal` is continuous because its increment over
  `[0,t]` is the Bochner primitive `∫₀ᵗ 𝟙_E dμ` (`intervalIntegral.continuous_primitive`, valid
  precisely because `μ` has `NoAtoms`), so it runs from `0` (`t → −∞`) to `(μ E).toReal` (`t → +∞`) and
  the intermediate value theorem attains `r.toReal`. The standard-Borel case
  `exists_measurableSet_subset_measure_eq` is *proved* from it by pushing `μ` forward along the
  measurable embedding `embeddingReal` into `ℝ` (injective ⇒ pushforward stays finite and atomless),
  solving there, and pulling the subset back. The prescribed-mass partition
  (`exists_disjoint_subset_measure_eq`) + probability decomposition (`exists_probability_decomposition`,
  hence `exists_atomless_partition`) sit above that. `#print axioms` on all of them lists only the three
  core logical axioms. **Milestone M8a is complete**; the standard-Borel hypothesis also supplies the
  soundness the bare `NoAtoms` statement lacks — see the fidelity corrections.

### Fidelity corrections made while closing

Several type-correct stubs were loose transcriptions; axiomatizing them as written would have been
*unsound* (a false axiom collapses the system). Corrected to faithful statements first:

- `lemma_B_1`: the retained fraction multiplies `μ(B₀)` (mass starting in the first ball, funneled
  along the chain), not `μ(⋃ Bₖ)` — the latter makes the `K = 0` base case `μ(⋃ Bₖ) ≤ μ(B₀)` false.
  Added the chain-overlap hypothesis.
- `lemma_B_2`: added the `switches θ ≤ 1` bound (one switch per ball), required for `lemma_B_1`'s
  `≤ K` budget.
- `prop_4_2`: added injective inputs/targets. The flow map is bijective, so steering the active point
  to its target while fixing the inactive ones is possible only if the points are distinct; without
  it the stub is false when targets collide.
- `prop_2_2` / `prop_2_1` / `cluster_to_point`: now carry `[IsProbabilityMeasure]`, and `prop_2_2`
  requires positive convex weights (`∑ αₖ = 1`, `αₖ ≠ 0`). `W₂` between measures of different total mass
  is ill-posed; the probability-measure layer makes the discrete-target statement well-posed and lets
  the pieces be normalized so clustering and the mixture bound apply cleanly. The `αₖ ≠ 0` hypothesis
  (added with the M8a de-axiomatization) keeps each normalized piece `(αₖ)⁻¹ • μ.restrict(Aₖ)` a genuine
  probability measure; a zero-weight atom is vacuous for a discrete target. `theorem_1_1` likewise now assumes
  each input is a probability measure (consumed by `cluster_to_point` via `isProbabilityMeasure_measureFlow`).
- `exists_atomless_partition` / `prop_2_2`: dropped the per-piece hemisphere clause from the partition
  axiom. Requiring every piece to sit in an open hemisphere is inconsistent at `M = 1` — it forces the
  whole atomless measure into a half-space through the origin, false for any centrally-symmetric
  measure (a Gaussian, or the uniform law on a ball/sphere). The sound statement keeps only the
  prescribed-mass disjoint decomposition; `prop_2_2` now acquires the hemisphere per piece dynamically
  (rotate into the orthant via `lemma_3_2`; the orthant lies in a basis direction's hemisphere),
  matching the paper's actual argument, and gains a `0 < d` hypothesis to name that basis direction.
- `exists_measurableSet_subset_measure_eq` (the Sierpiński IVT primitive, now a proved theorem):
  carries a `[StandardBorelSpace X]` hypothesis, not merely `NoAtoms`. Stated with `NoAtoms` alone the
  statement is *false* — on `ℝ` with the countable-cocountable σ-algebra and the `0/1` measure, every
  singleton is null (`NoAtoms` holds) yet no measurable set has measure `½`, so no subset of prescribed
  measure exists. `NoAtoms` is the point-mass notion; Sierpiński needs measure-algebra atomless-ness
  (every positive set splits), which `NoAtoms` supplies on a standard Borel space (Borel-isomorphic to
  `ℝ`, continuous CDF). `Eucl d` is standard Borel, so `exists_atomless_partition` and `prop_2_2` are
  unaffected. The correct hypothesis was fixed *before* the theorem was proved (caught by adversarially
  re-reading the then-axiom, the same discipline applied to the paper's own lemmas); the proof then goes
  through exactly the standard-Borel reduction that the soundness analysis predicted.
