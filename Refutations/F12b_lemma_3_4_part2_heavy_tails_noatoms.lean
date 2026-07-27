-- MUST-FAIL: regression for `lemma_3_4_part2` (finding F26, RESEARCH.md; the F12 heavy-tails
-- adapter re-derived against the 2026-07-27 non-vacuous re-statement, which added `[NoAtoms μ]`
-- and `hsupp` and deleted `_hu`/`hgenRest`; sibling of `F12_lemma_3_4_part2_heavy_tails.lean`,
-- which keeps guarding the older `¬ SameRay` no-sphere shape). Derives the sphere-support-free
-- shape from the current theorem. If this file ever COMPILES, the sphere supports have been
-- dropped: `Regression.Refuted.attnLemma34Part2NoSphereNoAtoms_false` refutes that shape
-- (atomless heavy-tailed junk-zero-barycenter mixtures).
-- EXPECT-ERROR: [Tt]ype mismatch|failed to synthesize
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.AttnLemma34Part2NoSphereNoAtomsSig :=
  fun μ ν hμp hνp hμa T hT hne hμo hνo hcol hsupp => by
    haveI := hμp; haveI := hνp; haveI := hμa
    exact (lemma_3_4_part2 μ ν T hT hne hμo hνo hcol hsupp).imp fun θ h => h.2.2
