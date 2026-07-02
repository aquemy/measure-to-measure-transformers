/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Quemy
-/
import ForMathlib.UnitSphereGeodesic

/-!
# A separating-hyperplane bound from cosine monotonicity

If two unit vectors `x`, `ω` subtend an angle of at least `π/2` and `τ ∈ (0, 3π/8)`, then
`⟪ω, x⟫ < cos (π/8 + τ)`: the point `x` lies strictly on the far side of the hyperplane
`{z : ⟪ω, z⟫ = cos (π/8 + τ)}`. This is a direct consequence of the strict antitonicity of cosine
on `[0, π]` applied to `π/8 + τ < π/2 ≤ angle ω x`, using `cos (angle ω x) = ⟪ω, x⟫` on the sphere.

*Preparation only:* staged for possible upstreaming, not contributed to Mathlib.
-/

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Separating-hyperplane bound: for unit vectors `x`, `ω` with `angle ω x ≥ π/2` and
`τ ∈ (0, 3π/8)`, one has `⟪ω, x⟫ < cos (π/8 + τ)`. -/
theorem inner_lt_cos_of_pi_div_two_le_angle {x ω : E} (hx : ‖x‖ = 1) (hω : ‖ω‖ = 1)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 (3 * Real.pi / 8))
    (hfar : Real.pi / 2 ≤ angle ω x) :
    ⟪ω, x⟫ < Real.cos (Real.pi / 8 + τ) := by
  obtain ⟨hτ0, hτ8⟩ := hτ
  have hpi := Real.pi_pos
  have ha : Real.pi / 8 + τ ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hb : angle ω x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨angle_nonneg ω x, angle_le_pi ω x⟩
  have hab : Real.pi / 8 + τ < angle ω x := by nlinarith [hfar]
  have hcos : Real.cos (angle ω x) < Real.cos (Real.pi / 8 + τ) :=
    Real.strictAntiOn_cos ha hb hab
  rwa [cos_angle_of_norm_eq_one hω hx] at hcos

end InnerProductGeometry
