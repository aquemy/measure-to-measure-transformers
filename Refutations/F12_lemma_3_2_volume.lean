-- MUST-FAIL: regression for `lemma_3_2` (finding F12, RESEARCH.md; repaired in db5889f).
-- Derives the kernel-refuted pre-F12 statement (every measure, no probability/sphere/cap
-- hypotheses) from the current axiom. If this file ever COMPILES, `lemma_3_2` has been
-- re-loosened to a shape already proved false by `Regression.Refuted.oldLemma32_false`
-- (Lebesgue volume).
-- EXPECT-ERROR: synthInstanceFailed|failed to synthesize
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldLemma32Sig :=
  fun μ T hT => (lemma_3_2 μ T hT).imp fun θ h => h.2
