-- MUST-FAIL: regression for `lemma_3_3` (finding F12, RESEARCH.md; repaired in db5889f,
-- restated on the mean-field layer in acafe3a). Derives the hypothesis-free shape from the
-- current axiom. If this file ever COMPILES, the measure hypotheses have been dropped:
-- `Regression.Refuted.oldAttnLemma33_false` refutes that shape (junk-identity flow on volume).
import Regression.OldStatements
set_option autoImplicit false
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

example : Regression.OldAttnLemma33Sig :=
  fun μ T ε hT hε => by
    obtain ⟨θ, α, -, -, hsupp⟩ := lemma_3_3 μ T ε hT hε
    exact ⟨θ, α, hsupp⟩
