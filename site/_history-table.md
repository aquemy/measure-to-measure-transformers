| # | date | type | subject | touches |
| --: | --- | --- | --- | --- |
| 1 | 2026-06-30 | `chore` | chore: bootstrap CKC repo, Lean+Mathlib project, and experiment harness | -- |
| 2 | 2026-06-30 | `review` | review(coverage): map Mathlib v4.31.0 support and fix the axiom boundary | `coverage` |
| 3 | 2026-06-30 | `formalize` | formalize(foundations): tangential projector and geodesic distance from Mathlib | `MeasureToMeasure.projector_inner_sub_sq` |
| 4 | 2026-06-30 | `axiomatize` | axiomatize~(axioms): introduce the labeled axiom layer for the missing Mathlib theory | `axioms` |
| 5 | 2026-06-30 | `formalize` | formalize(leaves): separating-hyperplane bound of Proposition 4.2 Step 1 (L3) | `MeasureToMeasure.Leaves.separating_hyperplane` |
| 6 | 2026-06-30 | `formalize` | formalize(leaves): ball-chain geometric retention of Lemma B.1 (L9) | `MeasureToMeasure.Leaves.ball_chain_geom` |
| 7 | 2026-06-30 | `formalize` | formalize(leaves): Lyapunov derivative and sign of Example 6.1 (L5) | `MeasureToMeasure.Leaves.lyapunov_hasDerivAt` |
| 8 | 2026-06-30 | `docs` | docs(claims): refresh status cache for the four machine-checked leaves | `claims` |
| 9 | 2026-06-30 | `formalize` | formalize(leaves): gate algebra and gate ODE of Lemma B.2 (L2) | `MeasureToMeasure.Leaves.gate_hasDerivAt_inner` |
| 10 | 2026-06-30 | `formalize` | formalize(leaves): barycenter ODE and strict increase of eq. B.9 (L6) | `MeasureToMeasure.Leaves.barycenter_hasDerivAt_inner` |
| 11 | 2026-06-30 | `formalize` | formalize(leaves): pigeonhole step of Lemma 3.4 Part 1 (L10) | `MeasureToMeasure.Leaves.exists_ne_in_ball` |
| 12 | 2026-06-30 | `axiomatize` | axiomatize~(leaves): linearized optimal-transport bound of Lemma 5.2 (L7) | `MeasureToMeasure.Leaves.lemma_5_2` |
| 13 | 2026-06-30 | `docs` | docs(claims): refresh status for leaves L2, L6, L7, L10 | `claims` |
| 14 | 2026-06-30 | `formalize` | formalize(leaves): gradient of geodesic distance along a path (L4) | `MeasureToMeasure.Leaves.geodesicDist_hasDerivAt` |
| 15 | 2026-06-30 | `docs` | docs(claims): mark L4 machine-checked and record the leaf scoreboard | `claims` |
| 16 | 2026-06-30 | `experiment` | experiment(e5): Lyapunov function decreases and theta converges (Example 6.1) | `e5` |
| 17 | 2026-06-30 | `experiment` | experiment(e1): gated flow transports mass through overlapping regions (Lemma B.2/B.1) | `e1` |
| 18 | 2026-06-30 | `docs` | docs(claims): mark experiments E1 and E5 as sci.measured | `claims` |
| 19 | 2026-06-30 | `experiment` | experiment(e2): self-attention clusters a hemisphere measure to a point (Proposition 2.1) | `e2` |
| 20 | 2026-06-30 | `experiment` | experiment(e3): barycenter separation disentangles overlapping supports (Proposition 3.1) | `e3` |
| 21 | 2026-06-30 | `experiment` | experiment(e4): gated steering moves the active point and parks the rest (Proposition 4.2) | `e4` |
| 22 | 2026-06-30 | `experiment` | experiment(e7): a single linear continuity equation cannot separate supports (eq. 1.7) | `e7` |
| 23 | 2026-06-30 | `experiment` | experiment(e6): end-to-end disentangle-cluster-match reaches the targets (Theorems 1.1/1.2) | `e6` |
| 24 | 2026-06-30 | `docs` | docs(claims): mark experiments E2, E3, E4, E6, E7 as sci.measured | `claims` |
| 25 | 2026-06-30 | `state` | state(statements): type-correct stubs for Theorems 1.1, 1.2 and Proposition 3.1 | `MeasureToMeasure.Statements.theorem_1_2` |
| 26 | 2026-06-30 | `docs` | docs(blueprint): dependency graph of all ~18 results with Lean refs and status | `blueprint` |
| 27 | 2026-06-30 | `docs` | docs(claims): build the ClaimGraph and mark the headline statements open | `claims` |
| 28 | 2026-06-30 | `chore` | chore: clear placeholder blueprint dir before leanblueprint scaffold | -- |
| 29 | 2026-06-30 | `docs` | docs(blueprint): scaffold leanblueprint, build PDF and web, publish to /docs | `blueprint` |
| 30 | 2026-06-30 | `docs` | docs(blueprint): point web nav links at the canonical Pages URL | `blueprint` |
| 31 | 2026-06-30 | `docs` | docs(review): adversarial proof-review of the mid-level lemmas | `review` |
| 32 | 2026-06-30 | `formalize` | formalize(leaves): disjoint hulls give non-colinear barycenters (L11, closes F2) | `MeasureToMeasure.Leaves.barycenter_noncolinear_of_disjoint_hull` |
| 33 | 2026-06-30 | `docs` | docs(claims): regenerate the ClaimGraph after the L11 leaf and proof review | `claims` |
| 34 | 2026-06-30 | `formalize` | formalize(leaves): general-measure barycenter non-colinearity (closes F2 residual) | `MeasureToMeasure.Leaves.barycenter_noncolinear_of_disjoint_hull_general` |
| 35 | 2026-06-30 | `formalize` | formalize(leaves): Markov mass bound via Kantorovich-Rubinstein duality (L8) | `MeasureToMeasure.Leaves.markov_bound` |
| 36 | 2026-06-30 | `formalize` | formalize(statements): type-correct Lean stubs for the mid-level lemmas | `MeasureToMeasure.Statements.prop_2_1` |
| 37 | 2026-06-30 | `docs` | docs: erratum for the B.2 sign error, ledger/registry/blueprint updates, republish | -- |
| 38 | 2026-06-30 | `feat` | feat(experiments): plotting, trajectory tracing, and provenance in the harness | `experiments` |
| 39 | 2026-06-30 | `experiment` | experiment(campaign): add verdict figures, hypotheses, and provenance to E1-E7 | `campaign` |
| 40 | 2026-06-30 | `docs` | docs(workflow): codify the before/prove/after cycle and cross-link experiments to claims | `workflow` |
| 41 | 2026-06-30 | `docs` | docs(report): data-driven experiment validation report (HTML + PDF) | `report` |
| 42 | 2026-06-30 | `docs` | docs(errata): correct the transpose in the Lemma B.2 gate parameter (F1) | `errata` |
| 43 | 2026-06-30 | `docs` | docs(blueprint): rich Quarto blueprint with verbatim paper extracts, Lean, and provenance | `blueprint` |
| 44 | 2026-06-30 | `docs` | docs(site): assemble the rich Quarto website into /docs for classic Pages | `site` |
| 45 | 2026-06-30 | `axiomatize` | axiomatize~(dynamics): structural flow algebra to assemble the construction | `MeasureToMeasure.Axioms.comp` |
| 46 | 2026-06-30 | `axiomatize` | axiomatize~(statements): close the mid-level lemmas; prove the ball-chain bound | `MeasureToMeasure.Statements.lemma_B_1` |
| 47 | 2026-06-30 | `formalize` | formalize(main): prove Theorems 1.1 and 1.2 by assembly | `MeasureToMeasure.Statements.theorem_1_1` |
| 48 | 2026-06-30 | `docs` | docs(ledger): record Phase 7 closure, axiom surface, and refreshed ClaimGraph | `ledger` |
| 49 | 2026-06-30 | `docs` | docs(site): republish with Phase 7 statuses (headlines now math.axiomatised) | `site` |
| 50 | 2026-06-30 | `formalize` | formalize(main): prove Proposition 3.1's disentanglement packaging | `MeasureToMeasure.Statements.prop_3_1` |
| 51 | 2026-06-30 | `docs` | docs(ledger): record Proposition 3.1 proved; refresh ClaimGraph and site | `ledger` |
| 52 | 2026-07-01 | `formalize` | formalize(statements): prove Proposition 4.1 by induction over Proposition 4.2 | `MeasureToMeasure.Statements.prop_4_1` |
| 53 | 2026-07-01 | `docs` | docs(ledger): record Proposition 4.1 proved; refresh ClaimGraph and site | `ledger` |
| 54 | 2026-07-01 | `formalize` | formalize(statements): prove Proposition 2.2 via a probability-measure refactor | `MeasureToMeasure.Statements.prop_2_2` |
| 55 | 2026-07-01 | `docs` | docs(ledger): record Proposition 2.2 proved; refresh ClaimGraph and site | `ledger` |
| 56 | 2026-07-01 | `docs` | docs: add "Beyond Mathlib" de-axiomatization roadmap page | -- |
| 57 | 2026-07-01 | `formalize` | formalize(statements): drop unsound hemisphere clause from exists_atomless_partition; re-thread prop_2_2 | `MeasureToMeasure.Statements.exists_atomless_partition` |
| 58 | 2026-07-01 | `formalize` | formalize(foundations): prove exists_atomless_partition from Sierpinski IVT (M8a Step 1) | `MeasureToMeasure.Foundations.exists_measurableSet_subset_measure_eq` |
| 59 | 2026-07-01 | `fix` | fix(foundations): require StandardBorelSpace in the Sierpinski IVT axiom (soundness) | `MeasureToMeasure.Foundations.exists_measurableSet_subset_measure_eq` |
| 60 | 2026-07-01 | `formalize` | formalize(foundations): reduce the Sierpinski IVT to the real line via embeddingReal | `MeasureToMeasure.Foundations.exists_measurableSet_subset_measure_eq_real` |
| 61 | 2026-07-01 | `formalize` | formalize(foundations): prove the Sierpinski IVT on R, fully discharging M8a | `MeasureToMeasure.Foundations.exists_measurableSet_subset_measure_eq_real` |
| 62 | 2026-07-01 | `docs` | docs(ledger): record Sierpinski IVT + atomless splitting proved; refresh ClaimGraph and site | `ledger` |
| 63 | 2026-07-01 | `formalize` | formalize(foundations): geodesic convexity on the sphere (M5 foundations) | `MeasureToMeasure.geodesicConvex_open_hemisphere` |
| 64 | 2026-07-01 | `docs` | docs(ledger): record geodesic-convexity foundations (M5); refresh ClaimGraph and site | `ledger` |
| 65 | 2026-07-01 | `formalize` | formalize(leaves): the geodesic hull is geodesically convex (M5 hull bridge) | `MeasureToMeasure.Leaves.geodesicConvex_geodesicHull` |
| 66 | 2026-07-01 | `docs` | docs(ledger): record geodesic-hull convexity (M5 bridge); refresh ClaimGraph and site | `ledger` |
| 67 | 2026-07-01 | `formalize` | formalize(leaves): the geodesic hull is the smallest geodesic-convex set (M5 minimality) | `MeasureToMeasure.Leaves.geodesicHull_subset_of_geodesicConvex` |
| 68 | 2026-07-01 | `docs` | docs(ledger): record geodesic-hull minimality (M5); refresh ClaimGraph and site | `ledger` |
| 69 | 2026-07-01 | `docs` | docs(site): mark M8a done and M5 in progress on the Beyond Mathlib page + build DAG | `site` |
| 70 | 2026-07-01 | `formalize` | formalize(leaves): separating-hyperplane criterion for hull disjointness (M5) | `MeasureToMeasure.Leaves.geodesicHull_disjoint_of_separated` |
| 71 | 2026-07-01 | `docs` | docs(ledger): record hull-disjointness criterion (M5); refresh ClaimGraph and site | `ledger` |
| 72 | 2026-07-01 | `formalize` | formalize(axioms): define measureFlow as a pushforward, deriving the measure-level flow laws (M3) | `MeasureToMeasure.Axioms.measureFlow` |
| 73 | 2026-07-01 | `docs` | docs(ledger): record measureFlow-as-pushforward (M3 slice); refresh ClaimGraph and site | `ledger` |
| 74 | 2026-07-01 | `formalize` | formalize(axioms): make the schedule type concrete, proving the switch algebra (M3) | `MeasureToMeasure.Axioms.switches_comp` |
| 75 | 2026-07-01 | `docs` | docs(ledger): record concrete schedule algebra (M3 slice); refresh ClaimGraph and site | `ledger` |
| 76 | 2026-07-01 | `formalize` | formalize(foundations): sphere invariance of the layer-normalized flow (M3 Phase 1) | `MeasureToMeasure.sphere_invariant` |
| 77 | 2026-07-01 | `docs` | docs(ledger): record sphere invariance (M3 Phase 1); refresh ClaimGraph and site | `ledger` |
| 78 | 2026-07-01 | `formalize` | formalize(foundations): flow algebra of an autonomous Lipschitz field (M3 Phase 1) | `MeasureToMeasure.integralCurve_unique` |
| 79 | 2026-07-01 | `docs` | docs(ledger): record the autonomous-field flow algebra (M3 Phase 1); refresh ClaimGraph and site | `ledger` |
| 80 | 2026-07-01 | `formalize` | formalize(foundations): couplings and the W1 Kantorovich cost (M2 Phase 0/2 opening) | `MeasureToMeasure.W1` |
| 81 | 2026-07-01 | `docs` | docs(ledger): record the W1 coupling foundation (M2 Phase 0/2); refresh ClaimGraph and site | `ledger` |
| 82 | 2026-07-02 | `formalize` | formalize(foundations): Kantorovich-Rubinstein lower bound for W1 (M2) | `MeasureToMeasure.lipschitz_integral_sub_le_transportCost` |
| 83 | 2026-07-02 | `docs` | docs(ledger): record the Kantorovich-Rubinstein W1 bound (M2); refresh ClaimGraph and site | `ledger` |
| 84 | 2026-07-02 | `docs` | docs(beyond-mathlib): frame re-usability + ForMathlib candidates + axiom-layer consistency | `beyond-mathlib` |
| 85 | 2026-07-02 | `formalize` | formalize(foundations): W1 triangle inequality via gluing of couplings (M2) | `MeasureToMeasure.exists_coupling_transportCost_le` |
| 86 | 2026-07-02 | `docs` | docs(ledger): record the W1 triangle inequality (M2); refresh ClaimGraph and site | `ledger` |
| 87 | 2026-07-02 | `formalize` | formalize(foundations): quadratic W2 cost and the map-coupling bound (M2) | `MeasureToMeasure.sqTransportCost` |
| 88 | 2026-07-02 | `docs` | docs(ledger): record the W2 map-coupling bound (M2); refresh ClaimGraph and site | `ledger` |
| 89 | 2026-07-02 | `formalize` | formalize(axioms): discharge the W1 Kantorovich-Rubinstein axiom; Markov bound machine-checked (M2) | `MeasureToMeasure.Axioms.W1_ge_of_lipschitz` |
| 90 | 2026-07-02 | `docs` | docs(ledger): record the W1 axiom discharge (M2); refresh ClaimGraph and site | `ledger` |
| 91 | 2026-07-02 | `docs` | docs(site): remove the 5-10 person-years scale estimate from the Beyond Mathlib page | `site` |
| 92 | 2026-07-02 | `meta` | meta(ci): add kernel-honesty drift guard (regenerate-and-compare) | `ci` |
| 93 | 2026-07-02 | `port` | port(formathlib): stage the spherical-geometry leaves as Mathlib-ready generalizations | `InnerProductGeometry.tangentialProjector` |
| 94 | 2026-07-02 | `docs` | docs(ledger): restructure RESEARCH.md into the v0.8.0 math-research ledger | `ledger` |
| 95 | 2026-07-02 | `docs` | docs(site): spot-check provenance/numerical fidelity; fix em-dashes; regenerate site | `site` |
| 96 | 2026-07-02 | `docs` | docs(blueprint): add the machine-checked foundations, closing the reconcile coverage gap | `MeasureToMeasure.Foundations.exists_measurableSet_subset_measure_eq_real` |
| 97 | 2026-07-02 | `formalize` | formalize(foundations): machine-check the W2 triangle inequality via Minkowski + gluing | `foundations` |
| 98 | 2026-07-02 | `formalize` | formalize(foundations): machine-check W2 convexity under mixtures | `foundations` |
| 99 | 2026-07-02 | `fix` | fix(foundations): disambiguate W2/W1 name collision between Foundations and Axioms | `foundations` |
| 100 | 2026-07-02 | `formalize` | formalize(foundations): concrete Block + per-block Picard-Lindelof existence (M3) | `foundations` |
| 101 | 2026-07-02 | `chore` | chore(audit): add a lake build gate so stale oleans cannot false-green | `audit` |
| 102 | 2026-07-02 | `formalize` | formalize(foundations): global point flow of a block via gluing (M3) | `foundations` |
| 103 | 2026-07-02 | `formalize` | formalize(foundations): the point flow map of a block and its group algebra (M3) | `foundations` |
| 104 | 2026-07-02 | `formalize` | formalize(foundations): the schedule flow map as a fold over blocks (M3) | `foundations` |
| 105 | 2026-07-02 | `formalize` | formalize(foundations): time-reversal of the schedule flow map (M3) | `foundations` |
| 106 | 2026-07-02 | `formalize` | formalize(axioms): discharge the continuity-equation flow-axiom layer (M3 complete) | `axioms` |
| 107 | 2026-07-02 | `formalize` | formalize(foundations): finiteness of W2 for boundedly-supported measures (M2) | `foundations` |
| 108 | 2026-07-02 | `formalize` | formalize(axioms): discharge the W2 optimal-transport axiom layer (M2 complete) | `axioms` |
| 109 | 2026-07-02 | `formalize` | formalize(foundations): measure continuity along a shrinking cap (lemma_B_2 slice 1, M4) | `foundations` |
| 110 | 2026-07-02 | `formalize` | formalize(foundations): logistic reaching estimate (lemma_B_2 slice 3, the ODE crux) | `foundations` |
| 111 | 2026-07-03 | `formalize` | formalize(foundations): reusable Lipschitz infra for the gated cutoff Block (M4 slice 2a) | `foundations` |
| 112 | 2026-07-03 | `formalize` | formalize(foundations): the gated cutoff Block instantiation (M4 slice 2 complete) | `foundations` |
| 113 | 2026-07-03 | `fix` | fix(statements): restrict lemma_B_2 to geodesic balls, not arbitrary sets (M4 fidelity) | `statements` |
| 114 | 2026-07-03 | `formalize` | formalize(leaves): the gated flow satisfies the logistic gate ODE (M4 discharge step 1) | `leaves` |
| 115 | 2026-07-03 | `formalize` | formalize(foundations): strict Cauchy-Schwarz on the sphere (M4 discharge prerequisite) | `foundations` |
| 116 | 2026-07-03 | `docs` | docs(site): refresh for the M4 gated-Block work; correct the Appendix-B prose | `site` |
| 117 | 2026-07-03 | `formalize` | formalize(leaves): the gated flow avoids the poles, so u stays in (-1,1) (M4 discharge step 2) | `leaves` |
| 118 | 2026-07-03 | `formalize` | formalize(leaves): finite-time reaching of the self-centered gated flow (M4 discharge step 3) | `leaves` |
| 119 | 2026-07-03 | `formalize` | formalize(axioms): mass retention under a set-mapping (M4 discharge step 4, B.8 core) | `axioms` |
| 120 | 2026-07-03 | `ci` | ci: stop accessing the private plugin marketplace; public-only build + sorry gate | -- |
| 121 | 2026-07-03 | `docs` | docs(site): surface the Appendix-B machinery on the landing page; refresh ClaimGraph | `site` |
| 122 | 2026-07-03 | `docs` | docs(site): update the Beyond-Mathlib roadmap for the discharged M2/M3 and in-progress M4 | `site` |
| 123 | 2026-07-03 | `formalize` | formalize(leaves): uniform cap contraction of the self-centered gated flow (B.7, set form) | `leaves` |
| 124 | 2026-07-03 | `docs` | docs(diagrams): recolor the build DAG to the current milestone status (M1/M2/M3 discharged) | `diagrams` |
| 125 | 2026-07-03 | `formalize` | formalize(leaves): mass retention of the self-centered gated flow (B.8, measure form) | `leaves` |
| 126 | 2026-07-03 | `fix` | fix(statements): restore dropped hypotheses in three false axiom stubs (soundness, F11) | `statements` |
| 127 | 2026-07-03 | `chore` | chore: add the Apache-2.0 LICENSE file referenced by the source headers | -- |
| 128 | 2026-07-03 | `fix` | fix(statements): restore sphere and support hypotheses across the axiom layer (soundness, F12-F16) | `statements` |
| 129 | 2026-07-03 | `docs` | docs: retire the stale Sierpinski-axiom wording and document tangentialProjector_apply | -- |
| 130 | 2026-07-03 | `formalize` | formalize(foundations): the self-attention mean-field flow interface (F14, M3b) | `MeasureToMeasure.Foundations.exists_meanFieldFlow` |
| 131 | 2026-07-03 | `fix` | fix(statements)!: restate the measure-level results over the attention mean-field flow (F14) | `statements` |
| 132 | 2026-07-03 | `refactor` | refactor: scope Sphere.lean to targeted Mathlib imports | -- |
| 133 | 2026-07-03 | `ci` | ci: wire lake lint (Batteries runLinter) into the verify workflow | -- |
| 134 | 2026-07-03 | `chore` | chore: baseline nolints.json for the linter (empty: tree is lint-clean) | -- |
| 135 | 2026-07-03 | `refactor` | refactor(foundations): simplify the Wasserstein proofs (no statement changes) | `foundations` |
| 136 | 2026-07-03 | `refactor` | refactor(foundations): simplify the flow-map proofs (no statement changes) | `foundations` |
| 137 | 2026-07-03 | `refactor` | refactor(foundations): simplify the gated-block Lipschitz proofs (no statement changes) | `foundations` |
| 138 | 2026-07-03 | `refactor` | refactor(foundations): simplify the atomless-splitting proofs (no statement changes) | `foundations` |
| 139 | 2026-07-03 | `port` | port(formathlib): generalize the separating bound and bridge the projector to starProjection | `InnerProductGeometry.inner_lt_cos_of_lt_angle` |
| 140 | 2026-07-03 | `refactor` | refactor: derive the projector, geodesic, and separating-hyperplane facts from the ForMathlib generics | -- |
| 141 | 2026-07-03 | `test` | test: add the refutation regression suite (Regression lib + must-fail gate) | -- |
| 142 | 2026-07-03 | `ci` | ci: vendor axiom-report and check per-node footprints in CI | -- |
| 143 | 2026-07-03 | `docs` | docs: the axiom admission protocol + strict fidelity hooks | -- |
| 144 | 2026-07-03 | `chore` | chore: fidelity records for the axiom layer | -- |
| 145 | 2026-07-03 | `fix` | fix(ci): portable mktemp in the vendored axiom-report | `ci` |
| 146 | 2026-07-03 | `chore` | chore: adopt ckc-tools v0.3.0 and the Source-Ref vocabulary | -- |
| 147 | 2026-07-03 | `fix` | fix(statements): probability and sub-hemisphere hypotheses for lemma_B_2/B_1 (gated-construction fidelity) | `MeasureToMeasure.Statements.lemma_B_2` |
| 148 | 2026-07-03 | `formalize` | formalize(leaves): two-cap retention of the amplitude-scaled gated flow (M4) | `MeasureToMeasure.gated_twoCap_retention` |
| 149 | 2026-07-03 | `formalize` | formalize(statements): discharge lemma_B_2; the Appendix-B chain is machine-checked (M4) | `MeasureToMeasure.Statements.lemma_B_2` |
| 150 | 2026-07-04 | `docs` | docs(site): refresh for the fidelity audit, mean-field restatement, and discharged M4 | `site` |
| 151 | 2026-07-04 | `formalize` | formalize~(foundations): bridge V=0 attention steps to the linear block flow | `MeasureToMeasure.Foundations.attnStep_eq_map_blockFlow` |
| 152 | 2026-07-04 | `test` | test(regression): non-vacuity witnesses for lemma_3_4 and exists_parked_schedule | `regression` |
| 153 | 2026-07-04 | `refactor` | refactor: sweep the remaining build warnings | -- |
| 154 | 2026-07-04 | `formalize` | formalize(foundations): strict spherical caps are geodesically convex (M5) | `MeasureToMeasure.geodesicConvex_inner_cap` |
| 155 | 2026-07-04 | `formalize` | formalize(leaves): the Section 3.3 separation transfer (M5 complete) | `MeasureToMeasure.Leaves.barycenter_not_sameRay_of_separated_balls` |
| 156 | 2026-07-04 | `docs` | docs(site): refresh for discharged M5, the attention bridge, and the completed witness suite | `site` |
| 157 | 2026-07-04 | `formalize` | formalize~(foundations): transport-map extraction for the attention solution operator | `foundations` |
| 158 | 2026-07-04 | `fix` | fix(statements)!: family forms for Lemmas 3.2-3.4 with the paper's fixing clauses (F17) | `statements` |
| 159 | 2026-07-04 | `formalize` | formalize~(foundations): quantitative moduli for the self-attention field (M3b groundwork) | `foundations` |
| 160 | 2026-07-04 | `formalize` | formalize(statements)!: discharge lemma_3_2 via the two-phase orthant rotation (F18) | `statements` |
| 161 | 2026-07-04 | `chore` | chore: remove the orphaned self-centered cap-mass leaf (GatedCapMass) | -- |
| 162 | 2026-07-04 | `formalize` | formalize(statements)!: discharge lemma_5_1 via disjoint-carrier gluing (F19) | `statements` |
| 163 | 2026-07-04 | `formalize` | formalize~(foundations): field measure-modulus reduction (M3b, toward mean-field well-posedness) | `foundations` |
| 164 | 2026-07-04 | `formalize` | formalize~(foundations): discharge the self-attention field W₁-modulus (M3b analytic core) | `foundations` |
| 165 | 2026-07-04 | `formalize` | formalize~(foundations): W1 map-coupling bound (M3b, mean-field uniqueness coupling step) | `foundations` |
| 166 | 2026-07-04 | `formalize` | formalize~(leaves): machine-check the discrete-clustering assembly core of prop_2_2 | `leaves` |
| 167 | 2026-07-04 | `formalize` | formalize~(foundations): the field's point-Lipschitz modulus on the sphere (M3b) | `foundations` |
| 168 | 2026-07-04 | `fix` | fix(foundations)!: meanFieldFlow_unique requires a sphere-supported datum (F20) | `foundations` |
| 169 | 2026-07-04 | `formalize` | formalize~(foundations): integral-form Grönwall for mean-field uniqueness (M3b) | `MeasureToMeasure.Foundations.gronwall_integral_zero` |
| 170 | 2026-07-04 | `formalize` | formalize~(foundations): FTC representation + velocity continuity of the mean-field flow (M3b, leaf 1/3) | `MeasureToMeasure.Foundations.velocity_continuousOn` |
| 171 | 2026-07-04 | `formalize` | formalize~(foundations): the averaged flow-distance functional + its continuity (M3b, leaf 2a) | `MeasureToMeasure.Foundations.meanFlowDist` |
| 172 | 2026-07-04 | `formalize` | formalize~(foundations): the averaged Grönwall integral inequality (M3b, leaf 2b) | `MeasureToMeasure.Foundations.flow_continuousOn_prod` |
| 173 | 2026-07-04 | `formalize` | formalize(foundations)!: discharge meanFieldFlow_unique via measure-averaged Grönwall (M3b) | `MeasureToMeasure.Foundations.meanFieldFlow_unique` |
| 174 | 2026-07-04 | `docs` | docs(site): refresh for meanFieldFlow_unique + lemma_5_1 discharges, DAG diagrams, roadmap | `site` |
| 175 | 2026-07-05 | `formalize` | formalize(leaves): barycenter of a flowed measure is the flow-averaged input (L1) | `leaves` |
| 176 | 2026-07-05 | `formalize` | formalize(leaves): a gated block fixes every point off its cap (L2) | `leaves` |
| 177 | 2026-07-05 | `formalize` | formalize(leaves): the barycenter-separation pigeonhole of Lemma 3.4 Part 1 (L3a) | `leaves` |
| 178 | 2026-07-05 | `docs` | docs(site): mark M7 partial (5.1 ✓) and M8b in-progress (§3.4 skeleton) in the build DAG | `site` |
| 179 | 2026-07-05 | `formalize` | formalize(leaves): distinct measures differ on some closed ball (L3-ball, Besicovitch) | `leaves` |
| 180 | 2026-07-05 | `formalize` | formalize(leaves): the barycenter is W₁-continuous (L3-wcont, Kantorovich–Rubinstein) | `leaves` |
| 181 | 2026-07-05 | `formalize` | formalize(leaves): single-block collapse displacement bound (L3-collapse-1) | `leaves` |
| 182 | 2026-07-05 | `formalize` | formalize(leaves): the rim annulus carries vanishing mass (L3-collapse-2) | `leaves` |
| 183 | 2026-07-05 | `formalize` | formalize(leaves): the W₂ collapse bound (L3-collapse-3, capstone) | `leaves` |
| 184 | 2026-07-05 | `formalize` | formalize(leaves): `W₁ ≤ W₂` for probability measures (assembly tail) | `leaves` |
| 185 | 2026-07-05 | `formalize` | formalize(leaves): the non-self-centered gated reach (Lemma 3.4 Part 1, Path I crux) | `leaves` |
| 186 | 2026-07-05 | `formalize` | formalize(leaves): barycenter of the non-self-centered collapse (Lemma 3.4 Part 1) | `leaves` |
| 187 | 2026-07-05 | `formalize` | formalize(leaves): a tight gate cap lies inside the carrier (Lemma 3.4 Part 1) | `leaves` |
| 188 | 2026-07-05 | `formalize` | formalize(leaves): off-center collapse displacement bound (Lemma 3.4 Part 1) | `leaves` |
| 189 | 2026-07-05 | `formalize` | formalize(leaves): non-self-centered W₂ collapse bound (Lemma 3.4 Part 1) | `leaves` |
| 190 | 2026-07-05 | `formalize` | formalize(leaves): mass-gap ball centred in a co-null target set (Lemma 3.4 Part 1) | `leaves` |
| 191 | 2026-07-05 | `formalize` | formalize(leaves): mass-gap cap inside the carrier (Lemma 3.4 Part 1) | `leaves` |
| 192 | 2026-07-05 | `formalize` | formalize(leaves): spherical-cap pigeonhole for the collapse pole (Lemma 3.4 Part 1) | `leaves` |
| 193 | 2026-07-05 | `formalize` | formalize(leaves): distinct measures force 2 ≤ d (Lemma 3.4 Part 1) | `leaves` |
| 194 | 2026-07-05 | `formalize` | formalize(leaves): grand-assembly infrastructure — block stacking, pole geometry, W₂ gap (Lemma 3.4 Part 1) | `leaves` |
| 195 | 2026-07-05 | `formalize` | formalize(statements): discharge lemma_3_4_part1 via the mass-gap cap collapse (App. B.3, 11→10) | `statements` |
| 196 | 2026-07-05 | `docs` | docs(site): refresh for lemma_3_4_part1 discharge (11 → 10 axioms) | `site` |
| 197 | 2026-07-06 | `formalize` | formalize~(foundations): P(sphere) is a compact, complete metric space (M3b existence, leaf E1) | `MeasureToMeasure.instCompleteSpaceLevyProkhorovSphere` |
| 198 | 2026-07-06 | `formalize` | formalize~(foundations): frozen-field tangency + sphere bound for mean-field existence (M3b, leaf E2-groundwork) | `MeasureToMeasure.Foundations.norm_rawField_le_onSphere` |
| 199 | 2026-07-06 | `formalize` | formalize~(foundations): radial retraction onto the closed unit ball is 1-Lipschitz (M3b existence, leaf E2a-1) | `MeasureToMeasure.lipschitzWith_ballProj` |
| 200 | 2026-07-06 | `formalize` | formalize~(foundations): ball-tamed raw attention field is globally bounded + Lipschitz (M3b existence, leaf E2a-2) | `MeasureToMeasure.Foundations.norm_rawFieldBall_sub_le` |
| 201 | 2026-07-06 | `formalize` | formalize~(foundations): tangential projector with a varying argument is bounded + Lipschitz on the ball (M3b existence, leaf E2a-3) | `MeasureToMeasure.norm_tangentialProjector_comp_sub_le_onBall` |
| 202 | 2026-07-06 | `formalize` | formalize~(foundations): the frozen attention field is a genuine well-posed Block (M3b existence, leaf E2a-4) | `MeasureToMeasure.Foundations.frozenBlock` |
| 203 | 2026-07-06 | `formalize` | formalize~(foundations): the frozen-field characteristic flow, solving the mean-field ODE on the sphere (M3b existence, leaf E2b) | `MeasureToMeasure.Foundations.frozenFlow_hasDerivAt_field` |
| 204 | 2026-07-06 | `ci` | ci: cross-check blueprint declarations with leanblueprint checkdecls | -- |
| 205 | 2026-07-06 | `fix` | fix(ci): commit blueprint/lean_decls instead of regenerating it in CI | `ci` |
| 206 | 2026-07-06 | `formalize` | formalize~(foundations): the sphere subtype-measure bridge (M3b existence, leaf S1) | `MeasureToMeasure.sphereProbEquiv` |
| 207 | 2026-07-06 | `formalize` | formalize~(foundations): W1 is finite on sphere-supported probability measures (M3b existence, leaf S2a) | `MeasureToMeasure.W1_ne_top_of_sphere_supported` |
| 208 | 2026-07-06 | `formalize` | formalize~(foundations): the W1 pseudometric on sphere-supported probability measures (M3b existence, leaf S2) | `MeasureToMeasure.instPseudoMetricSpaceSphereProb` |
| 209 | 2026-07-06 | `formalize` | formalize~(foundations): Kantorovich-Rubinstein estimate on SphereProb, the easy W1->weak direction (M3b existence, leaf S3a) | `MeasureToMeasure.SphereProb.abs_integral_sub_le_dist` |
| 210 | 2026-07-06 | `formalize` | formalize~(foundations): W1 map-coupling and mixture tools, the primal upper-bound layer (M3b existence, leaf S3b-i) | `MeasureToMeasure.W1_map_le` |
| 211 | 2026-07-06 | `formalize` | formalize~(foundations): W₁ rounding-approximation bound (M3b existence, leaf S3b-ii) | `MeasureToMeasure.W1_map_le_of_ae_edist_le` |
| 212 | 2026-07-06 | `formalize` | formalize~(foundations): W₁ ≤ 2·TV on the sphere via the min-coupling (M3b existence, leaf S3b-iii) | `MeasureToMeasure.W1_le_two_mul_tv` |
| 213 | 2026-07-06 | `formalize` | formalize~(foundations): finite μ-null-frontier ball cover of the sphere (M3b existence, leaf S3b-iv-cover) | `MeasureToMeasure.exists_finite_null_frontier_ball_cover` |
| 214 | 2026-07-06 | `formalize` | formalize~(foundations): measurable finite ε-rounding of the sphere (M3b existence, leaf S3b-iv-round) | `MeasureToMeasure.exists_finite_rounding` |
| 215 | 2026-07-06 | `formalize` | formalize~(foundations): discrete total-variation lower bound (M3b existence, leaf S3b-iv-tv) | `MeasureToMeasure.sum_min_le_inf_univ` |
| 216 | 2026-07-06 | `formalize` | formalize~(foundations): pushforward contracts total variation (M3b existence, leaf S3b-iv-tvmap) | `MeasureToMeasure.tv_map_le` |
| 217 | 2026-07-06 | `formalize` | formalize~(foundations): expose sel + cell null-frontiers in the rounding map (M3b existence, leaf S3b-iv-round-sel) | `MeasureToMeasure.exists_finite_rounding` |
| 218 | 2026-07-06 | `formalize` | formalize~(foundations): cell total variation → 0 under weak convergence (M3b existence, leaf S3b-iv-glue-tv) | `MeasureToMeasure.tendsto_residual_map_sel` |
| 219 | 2026-07-06 | `formalize` | formalize~(foundations): weak convergence ⇒ W₁ convergence on the sphere — the crux (M3b existence, leaf S3b-iv-glue) | `MeasureToMeasure.tendsto_W1_of_tendsto` |
| 220 | 2026-07-06 | `formalize` | formalize~(foundations): probability measures on the sphere are sequentially compact (M3b existence, leaf S4a) | `MeasureToMeasure.exists_subseq_tendsto_probabilityMeasure_sphere` |
| 221 | 2026-07-06 | `formalize` | formalize~(foundations): the W₁ space of sphere-supported probabilities is complete (M3b existence, leaf S4) | `MeasureToMeasure.instCompleteSpaceSphereProb` |
| 222 | 2026-07-07 | `chore` | chore(claims): reconcile stale claims.toml status against the kernel (D1-D3, D9) | `claims` |
