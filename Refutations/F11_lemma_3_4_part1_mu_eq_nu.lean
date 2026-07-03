-- MUST-FAIL: regression for `lemma_3_4_part1` (finding F11, RESEARCH.md; repaired in 4411b08).
-- Derives the kernel-refuted pre-F11 statement (no distinctness/probability/support hypotheses)
-- from the current axiom. If this file ever COMPILES, `lemma_3_4_part1` has been re-loosened to
-- a shape already proved false by `Regression.Refuted.oldLemma34Part1_false` (composing the two
-- yields `False`).
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldLemma34Part1Sig :=
  fun μ ν T hT hbar => lemma_3_4_part1 μ ν T hT hbar
