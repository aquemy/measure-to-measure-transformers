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
