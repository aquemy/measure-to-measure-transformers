-- MUST-FAIL: regression for `exists_disentangling_balls` (finding F14, RESEARCH.md; restated
-- with pairwise distinctness and the gap-form SharedMissingDirection in acafe3a). Derives the
-- shape without distinctness and with the pre-F14 point-form missing direction from the current
-- axiom. If this file ever COMPILES, those hypotheses have been dropped:
-- `Regression.Refuted.oldAttnDisentangle_false` refutes that shape (identical inputs cannot
-- enter disjoint balls).
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldAttnDisentangleSig :=
  fun hd μ₀ T hT hμ hμs hmiss => by
    obtain ⟨θ, α, r, -, hr0, hr1, -, hsep, hball, -⟩ :=
      exists_disentangling_balls hd μ₀ T hT hμ hμs hmiss
    exact ⟨θ, α, r, hr0, hr1, hsep, hball⟩
