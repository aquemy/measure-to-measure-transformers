import Regression.OldStatements

/-!
# F11: the pre-repair `lemma_3_4_part1` / `lemma_3_4_part2` are false

The pre-F11 statements (repaired in PR #64) carried no relation between the two measures beyond
(for part 1) equal barycenters. Instantiating both measures with the SAME measure satisfies every
hypothesis, while no schedule can separate (part 1) or de-colinearize (part 2) the identical
flowed barycenters. Disproofs originally machine-checked during the 2026-07-03 audit
(`RESEARCH.md`, finding F11).
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure

/-- F11: the pre-repair `lemma_3_4_part1` is false -- instantiate `μ := ν := 0`, where the
equal-barycenter hypothesis holds by `rfl` and the conclusion demands `x ≠ x`. -/
theorem oldLemma34Part1_false (ax : Regression.OldLemma34Part1Sig) : False := by
  obtain ⟨θ, hθ⟩ := ax (0 : Measure (Eucl 1)) (0 : Measure (Eucl 1)) 1 one_pos rfl
  exact hθ rfl

/-- F11: the pre-repair `lemma_3_4_part2` (linear record) is false -- with `μ := ν := 0` the
conclusion demands `¬ SameRay ℝ x x`, refuted by `SameRay.rfl`. -/
theorem oldLemma34Part2Linear_false (ax : Regression.OldLemma34Part2LinearSig) : False := by
  obtain ⟨θ, hθ⟩ := ax (0 : Measure (Eucl 1)) (0 : Measure (Eucl 1)) 1 one_pos
  exact hθ SameRay.rfl

end Regression.Refuted
