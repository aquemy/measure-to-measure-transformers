-- MUST-FAIL: regression for `exists_parked_schedule` (finding F33, RESEARCH.md). Derives the
-- kernel-refuted horizon-free schema from the current axiom by attempting to prove `0 < T` for
-- an arbitrary real `T`. It fails because the positivity is unprovable. If this file ever
-- COMPILES, `exists_parked_schedule` has dropped its `hT : 0 < T` hypothesis, a shape already
-- proved inconsistent (empty family, `T = -1`) by
-- `Regression.Refuted.oldParkedScheduleNoHorizon_false`.
-- EXPECT-ERROR: linarith failed|could not prove|unsolved
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldParkedScheduleNoHorizonSig := by
  intro d N hd ν target T ε s hdisj hper
  obtain ⟨Θ, hdur, -, -⟩ :=
    exists_parked_schedule hd ν target T ε (by linarith) s hdisj hper
  exact ⟨Θ, hdur⟩
