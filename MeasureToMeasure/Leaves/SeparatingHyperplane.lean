import ForMathlib.SeparatingHyperplane
import MeasureToMeasure.Foundations.GeodesicDistance

/-!
# Leaf L3: the separating hyperplane of Proposition 4.2, Step 1

In the matching construction the anchor `ω` is chosen with `d_g(ω, x₀ᴹ) ≥ π/2` (eq. 4.3). The
hyperplane `{x : ⟪ω, x⟫ = cos(π/8 + τ)}` then separates the active point from the cap `B(ω, π/8+τ)`:
for `τ ∈ (0, 3π/8)` one has `⟪ω, x₀ᴹ⟫ = cos d_g(ω, x₀ᴹ) < cos(π/8 + τ)`, because `cos` is strictly
decreasing on `[0, π]` and `π/8 + τ < π/2 ≤ d_g(ω, x₀ᴹ)`.

The cosine-monotonicity core is the constant-free generic
`InnerProductGeometry.inner_lt_cos_of_lt_angle` (`ForMathlib.SeparatingHyperplane`), applied at
the threshold `θ = π/8 + τ`; this leaf keeps the paper's constants arithmetic
(`0 ≤ π/8 + τ` and `π/8 + τ < π/2 ≤ d_g(ω, x)`) and the bridge from `geodesicDist` to
`InnerProductGeometry.angle`.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- L3 (separating side): if `x` is far from the anchor `ω` (`d_g(ω, x) ≥ π/2`) and
`τ ∈ (0, 3π/8)`, then `⟪ω, x⟫ < cos(π/8 + τ)`, so `x` lies strictly on the far side of the
separating hyperplane. -/
theorem separating_hyperplane {x ω : Eucl d} (hx : x ∈ sphere d) (hω : ω ∈ sphere d)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 (3 * Real.pi / 8))
    (hfar : Real.pi / 2 ≤ geodesicDist ω x) :
    ⟪ω, x⟫ < Real.cos (Real.pi / 8 + τ) := by
  obtain ⟨hτ0, hτ8⟩ := hτ
  have hnx : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hnω : ‖ω‖ = 1 := norm_eq_one_of_mem_sphere hω
  -- on the sphere the unoriented angle is the geodesic distance `arccos ⟪ω, x⟫`
  have hangle : InnerProductGeometry.angle ω x = geodesicDist ω x :=
    InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hnω hnx
  -- generic separation at threshold θ = π/8 + τ; the constants arithmetic stays here:
  -- 0 ≤ π/8 + τ, and π/8 + τ < π/2 ≤ d_g(ω, x) = angle ω x
  refine InnerProductGeometry.inner_lt_cos_of_lt_angle hnx hnω ?_ ?_
  · linarith [Real.pi_pos]
  · rw [hangle]; linarith

end MeasureToMeasure.Leaves
