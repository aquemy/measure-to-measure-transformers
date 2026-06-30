import MeasureToMeasure.Foundations.GeodesicDistance

/-!
# Leaf L3: the separating hyperplane of Proposition 4.2, Step 1

In the matching construction the anchor `ω` is chosen with `d_g(ω, x₀ᴹ) ≥ π/2` (eq. 4.3). The
hyperplane `{x : ⟪ω, x⟫ = cos(π/8 + τ)}` then separates the active point from the cap `B(ω, π/8+τ)`:
for `τ ∈ (0, 3π/8)` one has `⟪ω, x₀ᴹ⟫ = cos d_g(ω, x₀ᴹ) < cos(π/8 + τ)`, because `cos` is strictly
decreasing on `[0, π]` and `π/8 + τ < π/2 ≤ d_g(ω, x₀ᴹ)`.

This is a self-contained consequence of the monotonicity of cosine, kernel-checked here.
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
  have hpi := Real.pi_pos
  -- both angles lie in [0, π]
  have ha : Real.pi / 8 + τ ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hb : geodesicDist ω x ∈ Set.Icc (0 : ℝ) Real.pi := geodesicDist_mem_Icc ω x
  -- the far angle exceeds the cap angle
  have hab : Real.pi / 8 + τ < geodesicDist ω x := by nlinarith [hfar]
  -- cosine is strictly decreasing on [0, π]
  have hcos : Real.cos (geodesicDist ω x) < Real.cos (Real.pi / 8 + τ) :=
    Real.strictAntiOn_cos ha hb hab
  rwa [cos_geodesicDist hω hx] at hcos

end MeasureToMeasure.Leaves
