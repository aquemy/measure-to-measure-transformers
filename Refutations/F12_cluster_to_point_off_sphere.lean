-- MUST-FAIL: regression for `cluster_to_point` (finding F12, RESEARCH.md; repaired in db5889f,
-- restated on the mean-field layer in acafe3a). Derives the unrestricted-target shape from the
-- current axiom. If this file ever COMPILES, the on-sphere restriction on `z` has been dropped:
-- `Regression.Refuted.oldAttnCluster_false` refutes that shape (off-sphere Dirac target).
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldAttnClusterSig :=
  fun μ hμp hd T ε hT hε z e he hμs hhemi => by
    haveI := hμp
    obtain ⟨θ, -, -, hW⟩ := cluster_to_point μ hd T ε hT hε z e he hμs hhemi
    exact ⟨θ, hW⟩
