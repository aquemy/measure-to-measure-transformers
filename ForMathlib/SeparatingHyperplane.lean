/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Quemy
-/
import ForMathlib.UnitSphereGeodesic

/-!
# A separating-hyperplane bound from cosine monotonicity

If two unit vectors `x`, `ω` subtend an angle strictly greater than a threshold `θ ∈ [0, π]`, then
`⟪ω, x⟫ < cos θ`: the point `x` lies strictly on the far side of the hyperplane
`{z : ⟪ω, z⟫ = cos θ}`. This is a direct consequence of the strict antitonicity of cosine on
`[0, π]`, using `cos (angle ω x) = ⟪ω, x⟫` on the sphere.

*Preparation only:* staged for possible upstreaming, not contributed to Mathlib.
-/

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For unit vectors, the inner product is strictly below `cos θ` whenever the angle strictly
exceeds `θ` (with `θ` in the principal range). Strict antitonicity of `cos` on `[0, π]`. -/
theorem inner_lt_cos_of_lt_angle {x ω : E} (hx : ‖x‖ = 1) (hω : ‖ω‖ = 1)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < angle ω x) :
    ⟪ω, x⟫ < Real.cos θ := by
  have ha : θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hθ0, hθ.le.trans (angle_le_pi ω x)⟩
  have hb : angle ω x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨angle_nonneg ω x, angle_le_pi ω x⟩
  have hcos : Real.cos (angle ω x) < Real.cos θ := Real.strictAntiOn_cos ha hb hθ
  rwa [cos_angle_of_norm_eq_one hω hx] at hcos

end InnerProductGeometry
