-- MUST-FAIL: regression for `lemma_5_1` (finding F11, RESEARCH.md; repaired in 4411b08 and
-- db5889f/F13). Derives the disjoint-supports-free statement from the current axiom. If this
-- file ever COMPILES, the disjointness hypotheses have been dropped:
-- `Regression.Refuted.oldLemma51_false` already refutes that shape (shared source atom).
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldLemma51Sig :=
  fun μ₀ μ₁ hmatch => lemma_5_1 μ₀ μ₁ hmatch
