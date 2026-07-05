-- MUST-FAIL: regression for `lemma_3_4_part1` (finding F12, RESEARCH.md; repaired in db5889f).
-- Derives the post-F11/pre-F12 statement (orthant support but NO sphere support) from the
-- current axiom. If this file ever COMPILES, the sphere-support hypotheses have been dropped:
-- `Regression.Refuted.oldLemma34Part1Orthant_false` already refutes that shape (heavy tails).
import Regression.OldStatements
import MeasureToMeasure.Statements.Lemma34Part1
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldLemma34Part1OrthantSig :=
  fun μ ν hμp hνp T hT hne hμo hνo hbar => by
    haveI := hμp; haveI := hνp
    exact lemma_3_4_part1 μ ν T hT hne hμo hνo hbar
