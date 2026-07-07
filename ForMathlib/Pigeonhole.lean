/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Quemy
-/
import Mathlib.Analysis.Normed.Module.Basic

/-!
# An open ball in a nontrivial normed space is not a single point

A nonempty open ball in a nontrivial normed space contains a point different from any prescribed
`a`: no map can be forced to a single value on it. This is the elementary pigeonhole fact behind
"if every point of a ball mapped to the same value the map would have to be constant, but a
positive-radius ball has more than one point."

*Preparation only:* staged for possible upstreaming, not contributed to Mathlib.
-/

namespace Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- An open ball of positive radius in a nontrivial real normed space contains a point distinct
from any prescribed `a`. -/
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

end Metric
