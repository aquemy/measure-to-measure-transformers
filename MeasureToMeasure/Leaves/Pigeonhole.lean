import Mathlib.Analysis.Normed.Module.Basic

/-!
# Leaf L10: the pigeonhole step of Lemma 3.4, Part 1

The proof of Lemma 3.4 chooses `x* ∈ 𝓑` so that two barycenters differ. If no such `x*` existed,
then `x*` would have to equal a fixed vector for every `x* ∈ 𝓑`, i.e. the identity would be constant
on the open ball `𝓑`, which is impossible. The mathematical core is exactly this: a nonempty open
ball in a nontrivial normed space is not a single point, so it contains a point different from any
prescribed `a`. We kernel-check this general fact.
-/

namespace MeasureToMeasure.Leaves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- L10: an open ball of positive radius in a nontrivial real normed space contains a point distinct
from any prescribed `a`. Hence no map can be forced to a single value on the ball, which is the
contradiction the pigeonhole step exploits. -/
theorem exists_ne_in_ball (c a : E) {r : ℝ} (hr : 0 < r) :
    ∃ x ∈ Metric.ball c r, x ≠ a := by
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set v : E := (r / (2 * ‖u‖)) • u with hv
  have hvnorm : ‖v‖ = r / 2 := by
    rw [hv, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hvne : v ≠ 0 := by
    rw [← norm_pos_iff, hvnorm]; linarith
  -- `c` and `c + v` both lie in the ball and are distinct
  have hc_mem : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hcv_mem : c + v ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : c + v - c = v := by abel
    rw [h1, hvnorm]; linarith
  -- at least one of the two distinct points differs from `a`
  rcases eq_or_ne c a with hca | hca
  · refine ⟨c + v, hcv_mem, fun h => hvne ?_⟩
    have h2 : c + v = c + 0 := by rw [add_zero, h, hca]
    exact add_left_cancel h2
  · exact ⟨c, hc_mem, hca⟩

end MeasureToMeasure.Leaves
