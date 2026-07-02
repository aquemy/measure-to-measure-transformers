/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Quemy
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The geodesic distance on the unit sphere is the unoriented angle

The geodesic (great-circle) distance between unit vectors `x`, `y` of a real inner product space is
`arccos ⟪x, y⟫`. Mathlib already has the unoriented angle `InnerProductGeometry.angle x y =
arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))`; on the unit sphere the normalizer is `1`, so the two coincide. This
file records that bridge (rather than introducing a shadowing definition), together with the two
Cauchy-Schwarz bounds `⟪x, y⟫ ∈ [-1, 1]` and the specialization `cos (angle x y) = ⟪x, y⟫`. The
range `angle x y ∈ [0, π]` is already `InnerProductGeometry.angle_nonneg` / `angle_le_pi`.

*Preparation only:* staged for possible upstreaming, not contributed to Mathlib.
-/

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For unit vectors the inner product is at most `1` (Cauchy-Schwarz). -/
theorem inner_le_one_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ ≤ 1 := by
  have hb : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one] at hb
  exact (abs_le.mp hb).2

/-- For unit vectors the inner product is at least `-1` (Cauchy-Schwarz). -/
theorem neg_one_le_inner_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (-1 : ℝ) ≤ ⟪x, y⟫ := by
  have hb : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one] at hb
  exact (abs_le.mp hb).1

/-- On the unit sphere the unoriented angle is the geodesic distance `arccos ⟪x, y⟫`. -/
theorem angle_eq_arccos_inner_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y = Real.arccos (⟪x, y⟫) := by
  rw [angle, hx, hy, mul_one, div_one]

/-- On the unit sphere, `cos (angle x y) = ⟪x, y⟫`. -/
theorem cos_angle_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.cos (angle x y) = ⟪x, y⟫ := by
  rw [cos_angle, hx, hy, mul_one, div_one]

end InnerProductGeometry
