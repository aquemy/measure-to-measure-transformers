-- MUST-FAIL: regression for `lemma_3_2` (finding F18, RESEARCH.md). Derives the kernel-refuted
-- `2 ≤ d`-free family form from the current discharged theorem by supplying the dimension
-- hypothesis for an arbitrary `d`. It fails because `2 ≤ d` is unprovable for a general `d`.
-- If this file ever COMPILES, `lemma_3_2` has dropped its `2 ≤ d` hypothesis, a shape already
-- proved false at `d = 1` by `Regression.Refuted.oldLemma32Family_dimOne_false`.
-- EXPECT-ERROR: omega|could not prove|unsolved
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldLemma32FamilyNoDimSig :=
  fun μ₀ hμ T hT hμs hmiss =>
    lemma_3_2 μ₀ hμ (by omega) T hT hμs hmiss
