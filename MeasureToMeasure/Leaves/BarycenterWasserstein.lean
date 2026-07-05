import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Leaves.GeodesicHullConvex

/-!
# Leaf L3-wcont (Lemma 3.4 Part 1): the barycenter is `W₁`-continuous

The App. B.3 Part 1 argument closes by saying "the expectation of a measure is continuous with respect
to the measure in the sense of the Wasserstein distance", so the exact collapse (whose barycenters are
separated by the pigeonhole, leaf L3a) survives the `ε`-approximate flow. That continuity is exactly
the Kantorovich–Rubinstein bound applied in the direction of the barycenter gap:

  `‖ℰ_μ − ℰ_ν‖ ≤ W₁(μ, ν)`.

Take the unit vector `u` along `ℰ_μ − ℰ_ν`; the `1`-Lipschitz test function `f(x) = ⟪u, x⟫` has
`∫f dμ − ∫f dν = ⟪u, ℰ_μ − ℰ_ν⟫ = ‖ℰ_μ − ℰ_ν‖`, which the banked `W1_ge_of_lipschitz`
(`Axioms/Wasserstein.lean`) lower-bounds by `W₁`. Sphere support gives the integrability the dual
pairing needs (`integrable_id_of_sphere_support`), and `(innerSL ℝ u).integral_comp_comm` turns the
scalar integral into `⟪u, barycenter ·⟫`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **L3-wcont.** The barycenter is `W₁`-Lipschitz: `‖ℰ_μ − ℰ_ν‖ ≤ W₁(μ, ν)` for sphere-supported
probability measures with finite `W₁`. The Kantorovich–Rubinstein pairing in the barycenter-gap
direction. -/
theorem norm_barycenter_sub_le_W1 {μ ν : Measure (Eucl d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμs : μ (sphere d)ᶜ = 0) (hνs : ν (sphere d)ᶜ = 0)
    (hfin : MeasureToMeasure.W1 μ ν ≠ ⊤) :
    ‖barycenter μ - barycenter ν‖ ≤ Axioms.W1 μ ν := by
  set w := barycenter μ - barycenter ν with hw
  rcases eq_or_ne w 0 with h0 | h0
  · rw [h0, norm_zero]; exact ENNReal.toReal_nonneg
  · have hwne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    set u : Eucl d := ‖w‖⁻¹ • w with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w),
        inv_mul_cancel₀ hwne]
    -- `f(x) = ⟪u, x⟫` is `1`-Lipschitz (Cauchy–Schwarz with `‖u‖ = 1`)
    have hlip : LipschitzWith 1 (fun x : Eucl d => (⟪u, x⟫ : ℝ)) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      rw [Real.dist_eq, ← inner_sub_right, dist_eq_norm, NNReal.coe_one, one_mul]
      calc |(⟪u, x - y⟫ : ℝ)| ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm u (x - y)
        _ = ‖x - y‖ := by rw [hunorm, one_mul]
    -- integrability from sphere support
    have hμint := integrable_id_of_sphere_support hμs
    have hνint := integrable_id_of_sphere_support hνs
    have hiμ : Integrable (fun x => (⟪u, x⟫ : ℝ)) μ := by
      simpa using (innerSL ℝ u).integrable_comp hμint
    have hiν : Integrable (fun x => (⟪u, x⟫ : ℝ)) ν := by
      simpa using (innerSL ℝ u).integrable_comp hνint
    -- Kantorovich–Rubinstein
    have hkey := Axioms.W1_ge_of_lipschitz μ ν _ hlip hiμ hiν hfin
    -- the pairing equals `‖w‖`
    have hbμ : ∫ x, (⟪u, x⟫ : ℝ) ∂μ = ⟪u, barycenter μ⟫ := by
      simpa [barycenter] using (innerSL ℝ u).integral_comp_comm hμint
    have hbν : ∫ x, (⟪u, x⟫ : ℝ) ∂ν = ⟪u, barycenter ν⟫ := by
      simpa [barycenter] using (innerSL ℝ u).integral_comp_comm hνint
    have huw : (⟪u, w⟫ : ℝ) = ‖w‖ := by
      rw [hu, real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
        inv_mul_cancel₀ hwne, one_mul]
    have heq : ∫ x, (⟪u, x⟫ : ℝ) ∂μ - ∫ x, (⟪u, x⟫ : ℝ) ∂ν = ‖w‖ := by
      rw [hbμ, hbν, ← inner_sub_right, ← hw, huw]
    rw [heq] at hkey
    exact hkey

end MeasureToMeasure.Leaves
