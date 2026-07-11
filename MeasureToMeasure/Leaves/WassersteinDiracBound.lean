import MeasureToMeasure.Foundations.GeodesicDistance
import MeasureToMeasure.Foundations.Wasserstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Concentrated mass near a point bounds `W₂` to the Dirac there (prop_2_2 Stage 5)

The first leaf of the `prop_2_2` Steps 2-3 campaign (ball packing, path chaining, and this bound,
which turns "mass retained in a geodesic ball" -- exactly what `gated_forest_to_target_retention`
delivers -- into a `W₂`-distance bound to a Dirac target, the shape `measureFlow_W2_discrete_of_
perPiece` needs).

**Why this route, not the paper's own.** The paper argues via `W₁`-duality (Kantorovich-Rubinstein)
then invokes "all Wasserstein distances are equivalent on `S^{d-1}`" to pass to `W₂`. This codebase
has `W1_le_W2` (`WassersteinCompare.lean`) but not yet the reverse direction the paper's route would
need. Skipped entirely here: since the target is a single Dirac, `W₂(ν,δ_z)` has a much more direct
route -- the **only** coupling of any measure with a Dirac is the product coupling (`isCoupling_
prod`), so `W₂(ν,δ_z)² = ∫‖x-z‖²dν(x)` exactly, no infimum-over-couplings analysis needed at all.

**The bound.** Split the second-moment integral by whether `x` is within geodesic radius `R` of `z`:
the "close" mass (all but `≤δ`) contributes `≤R²` per point (`norm_sub_le_geodesicDist`: on the unit
sphere, straight-line distance is bounded by geodesic distance -- chord `≤` arc, `2sin(θ/2)≤θ` via
`Real.sin_le`); the rest contributes `≤4` per point (the sphere's own diameter, `‖x-z‖≤‖x‖+‖z‖=2`).
Together: `W₂(μ,δ_z) ≤ √(R²+4δ)`.
-/

namespace MeasureToMeasure

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- **Chord ≤ arc.** On the unit sphere, straight-line (ambient) distance is bounded by geodesic
distance: `‖x-y‖ = 2sin(θ/2) ≤ θ = geodesicDist x y` for `θ∈[0,π]`, via `sin t ≤ t`. -/
theorem norm_sub_le_geodesicDist {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    ‖x - y‖ ≤ geodesicDist x y := by
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hyn : ‖y‖ = 1 := norm_eq_one_of_mem_sphere hy
  have hsq : ‖x - y‖ ^ 2 = 2 - 2 * (⟪x, y⟫ : ℝ) := by
    rw [norm_sub_sq_real, hxn, hyn]; ring
  have hcos : (⟪x, y⟫ : ℝ) = Real.cos (geodesicDist x y) := (cos_geodesicDist hx hy).symm
  set θ := geodesicDist x y with hθdef
  have hθrange : θ ∈ Set.Icc (0 : ℝ) Real.pi := geodesicDist_mem_Icc x y
  have hhalf : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2mul : Real.cos (2 * (θ / 2)) = 2 * Real.cos (θ / 2) ^ 2 - 1 := Real.cos_two_mul (θ / 2)
    have h2 : (2 : ℝ) * (θ / 2) = θ := by ring
    rw [h2] at h2mul
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hchord : ‖x - y‖ = 2 * Real.sin (θ / 2) := by
    have heq : ‖x - y‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by rw [hsq, hcos, hhalf]; ring
    have hnn1 : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hnn2 : 0 ≤ 2 * Real.sin (θ / 2) := by
      have hb : 0 ≤ θ / 2 ∧ θ / 2 ≤ Real.pi / 2 := by constructor <;> linarith [hθrange.1, hθrange.2]
      have := Real.sin_nonneg_of_nonneg_of_le_pi hb.1 (by linarith [hb.2])
      linarith
    nlinarith [sq_nonneg (‖x - y‖ - 2 * Real.sin (θ / 2))]
  rw [hchord]
  exact le_trans (by linarith [Real.sin_le (by linarith [hθrange.1] : (0 : ℝ) ≤ θ / 2)]) le_rfl

/-- The squared distance to `z`, integrated against a sphere-supported measure, is bounded by a
`R²`-per-point contribution from the mass within geodesic radius `R` of `z` plus a `4`-per-point
(diameter-squared) contribution from the rest. -/
theorem lintegral_sq_edist_dirac_le (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hμS : μ (sphere d)ᶜ = 0) (z : Eucl d) (hz : z ∈ sphere d) (R : ℝ) :
    ∫⁻ x, edist x z ^ 2 ∂μ ≤ (ENNReal.ofReal R) ^ 2 * μ (geodesicBall z R) +
      4 * μ (geodesicBall z R)ᶜ := by
  have hae : ∀ᵐ x ∂μ, x ∈ sphere d := by rw [ae_iff]; exact hμS
  have hbound : ∀ᵐ x ∂μ, edist x z ^ 2 ≤
      (geodesicBall z R).indicator (fun _ => (ENNReal.ofReal R) ^ 2) x +
      (geodesicBall z R)ᶜ.indicator (fun _ => (4 : ℝ≥0∞)) x := by
    filter_upwards [hae] with x hxs
    have hedist : edist x z = ENNReal.ofReal ‖x - z‖ := by rw [edist_dist, dist_eq_norm]
    by_cases hxb : x ∈ geodesicBall z R
    · rw [Set.indicator_of_mem hxb, Set.indicator_of_notMem (by simpa using hxb), add_zero, hedist]
      have hle : ‖x - z‖ ≤ geodesicDist x z := norm_sub_le_geodesicDist hxb.1 hz
      have hlt : geodesicDist x z < R := by have := hxb.2; rwa [geodesicDist_comm] at this
      gcongr
      exact hle.trans hlt.le
    · rw [Set.indicator_of_notMem hxb, Set.indicator_of_mem (by simpa using hxb), zero_add, hedist]
      have hdiam : ‖x - z‖ ≤ 2 := by
        have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hxs
        have hzn : ‖z‖ = 1 := norm_eq_one_of_mem_sphere hz
        calc ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le x z
          _ = 2 := by rw [hxn, hzn]; ring
      have hstep : ENNReal.ofReal ‖x - z‖ ≤ ENNReal.ofReal (2 : ℝ) := ENNReal.ofReal_le_ofReal hdiam
      calc (ENNReal.ofReal ‖x - z‖) ^ 2 ≤ (ENNReal.ofReal (2 : ℝ)) ^ 2 := by gcongr
        _ = 4 := by rw [← ENNReal.ofReal_pow (by norm_num)]; norm_num
  calc ∫⁻ x, edist x z ^ 2 ∂μ
      ≤ ∫⁻ x, ((geodesicBall z R).indicator (fun _ => (ENNReal.ofReal R) ^ 2) x +
          (geodesicBall z R)ᶜ.indicator (fun _ => (4 : ℝ≥0∞)) x) ∂μ := lintegral_mono_ae hbound
    _ = (ENNReal.ofReal R) ^ 2 * μ (geodesicBall z R) + 4 * μ (geodesicBall z R)ᶜ := by
        rw [lintegral_add_left
            (Measurable.indicator measurable_const (measurableSet_geodesicBall z R)),
          lintegral_indicator (measurableSet_geodesicBall z R),
          lintegral_indicator (measurableSet_geodesicBall z R).compl,
          setLIntegral_const, setLIntegral_const]

/-- **Concentrated mass near a point bounds `W₂` to the Dirac there.** If `μ` is supported on the
sphere and all but `≤δ` of its mass lies within geodesic radius `R` of `z`, `W₂(μ, δ_z) ≤ √(R²+4δ)`
-- via the unique coupling `μ ⊗ δ_z` (a Dirac target admits only the product coupling), whose
squared cost is exactly `∫‖x-z‖²dμ`. -/
theorem W2_dirac_le_of_geodesicBall_mass (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hμS : μ (sphere d)ᶜ = 0) (z : Eucl d) (hz : z ∈ sphere d) (R δ : ℝ) (hR : 0 ≤ R)
    (hδ : 0 ≤ δ) (hmass : μ (geodesicBall z R)ᶜ ≤ ENNReal.ofReal δ) :
    W2 μ (Measure.dirac z) ≤ ENNReal.ofReal (Real.sqrt (R ^ 2 + 4 * δ)) := by
  have hcpl : IsCoupling (μ.prod (Measure.dirac z)) μ (Measure.dirac z) :=
    isCoupling_prod μ (Measure.dirac z)
  have hle := W2_le_rpow_sqTransportCost hcpl
  have hst : sqTransportCost (μ.prod (Measure.dirac z)) = ∫⁻ x, edist x z ^ 2 ∂μ := by
    rw [sqTransportCost, Measure.prod_dirac, lintegral_map (by fun_prop) (by fun_prop)]
  rw [hst] at hle
  have hbound := lintegral_sq_edist_dirac_le μ hμS z hz R
  have hμball : μ (geodesicBall z R) ≤ 1 := prob_le_one
  have hcombine : ∫⁻ x, edist x z ^ 2 ∂μ ≤ (ENNReal.ofReal R) ^ 2 + 4 * ENNReal.ofReal δ := by
    calc ∫⁻ x, edist x z ^ 2 ∂μ ≤ (ENNReal.ofReal R) ^ 2 * μ (geodesicBall z R) +
          4 * μ (geodesicBall z R)ᶜ := hbound
      _ ≤ (ENNReal.ofReal R) ^ 2 * 1 + 4 * ENNReal.ofReal δ := by gcongr
      _ = (ENNReal.ofReal R) ^ 2 + 4 * ENNReal.ofReal δ := by ring
  have hrpow : ((ENNReal.ofReal R) ^ 2 + 4 * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (R ^ 2 + 4 * δ)) := by
    have heq : (ENNReal.ofReal R) ^ 2 + 4 * ENNReal.ofReal δ = ENNReal.ofReal (R ^ 2 + 4 * δ) := by
      rw [← ENNReal.ofReal_pow hR, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [heq, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      show (2⁻¹ : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  calc W2 μ (Measure.dirac z) ≤ (∫⁻ x, edist x z ^ 2 ∂μ) ^ (2⁻¹ : ℝ) := hle
    _ ≤ ((ENNReal.ofReal R) ^ 2 + 4 * ENNReal.ofReal δ) ^ (2⁻¹ : ℝ) := by gcongr
    _ ≤ ENNReal.ofReal (Real.sqrt (R ^ 2 + 4 * δ)) := hrpow

end MeasureToMeasure
