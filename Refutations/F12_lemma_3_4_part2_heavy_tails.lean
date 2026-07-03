-- MUST-FAIL: regression for `lemma_3_4_part2` (finding F12, RESEARCH.md; repaired in db5889f,
-- restated on the mean-field layer in acafe3a). Derives the sphere-support-free shape from the
-- current axiom. If this file ever COMPILES, the sphere-support hypotheses have been dropped:
-- `Regression.Refuted.oldAttnLemma34Part2NoSphere_false` refutes that shape (junk-identity flow
-- on heavy-tailed measures).
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldAttnLemma34Part2NoSphereSig :=
  fun μ ν hμp hνp T hT hne hμo hνo hcol => by
    haveI := hμp; haveI := hνp
    exact (lemma_3_4_part2 μ ν T hT hne hμo hνo hcol).imp fun θ h => h.2.2
