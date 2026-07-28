-- MUST-FAIL: regression for `lemma_5_4` (finding F31, RESEARCH.md). Derives the kernel-refuted
-- dimension-free schema from the current axiom by supplying the dimension hypothesis for an
-- arbitrary `d`. It fails because `3 ≤ d` is unprovable for a general `d`. If this file ever
-- COMPILES, `lemma_5_4` has dropped its `3 ≤ d` hypothesis, a shape already proved false at
-- `d = 1` by `Regression.Refuted.oldLemma54NoDim_false`.
-- EXPECT-ERROR: omega|could not prove|unsolved
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldLemma54NoDimSig := by
  intro d μ hμ ψ T ε hT hε hμs hψm hψs
  haveI := hμ
  obtain ⟨θ, ψε, _hdur, hflow, hm, _hint, hL2⟩ :=
    lemma_5_4 (by omega) μ ψ T ε hT hε hμs hψm hψs
  exact ⟨θ, ψε, hflow, hm, hL2⟩
