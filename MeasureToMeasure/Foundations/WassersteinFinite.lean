import MeasureToMeasure.Foundations.Wasserstein
import MeasureToMeasure.Foundations.Sphere

/-!
# Finiteness of `W₁` on sphere-supported measures (M3b existence, leaf S2a)

Second leaf of the Wasserstein completeness sub-campaign toward `exists_meanFieldFlow` (M3b
existence). The bespoke `W₁ : Measure (Eucl d) → _ → ℝ≥0∞` can be `⊤`, and the repo's `ℝ`-valued
interface `Axioms.W1 := (W1 · ·).toReal` — together with every field measure-modulus of
`MeanFieldWellPosed` — is only faithful where `W₁ < ⊤` (they all carry a `W1 μ ν ≠ ⊤` hypothesis, and
`toReal` sends `⊤` to `0`). On the compact unit sphere `W₁` is always finite: the product coupling
moves mass a distance at most the diameter `2`. This leaf records that, mirroring the banked W₂
finiteness `W2_ne_top_of_ae_norm_le`:

* `W1_le_of_ae_norm_le` / `W1_ne_top_of_ae_norm_le` — for probability measures a.e.-supported in the
  ball of radius `R`, `W₁ ≤ 2R < ⊤` (product coupling has cost `≤ 2R`);
* `W1_le_two_of_sphere_supported`, `W1_ne_top_of_sphere_supported` — the `R = 1` specialization,
  which **discharges the `W1 μ ν ≠ ⊤` hypotheses** that pervade the field's measure moduli and makes
  `(W1 μ ν).toReal` a genuine (bounded) metric value on `SphereProb d`.
-/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace MeasureToMeasure

variable {d : ℕ}

/-- **`W₁` upper bound for boundedly-supported probability measures.** If `μ, ν` are a.e.-supported in
the ball of radius `R`, the product coupling moves mass a distance `≤ 2R`, so `W₁ μ ν ≤ 2R`. -/
theorem W1_le_of_ae_norm_le (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {R : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (hν : ∀ᵐ y ∂ν, ‖y‖ ≤ R) :
    W1 μ ν ≤ ENNReal.ofReal (2 * R) := by
  have hae : ∀ᵐ p ∂(μ.prod ν), edist p.1 p.2 ≤ ENNReal.ofReal (2 * R) := by
    have h1 : ∀ᵐ p ∂(μ.prod ν), ‖p.1‖ ≤ R := Measure.quasiMeasurePreserving_fst.ae hμ
    have h2 : ∀ᵐ p ∂(μ.prod ν), ‖p.2‖ ≤ R := Measure.quasiMeasurePreserving_snd.ae hν
    filter_upwards [h1, h2] with p hp1 hp2
    have hdist : dist p.1 p.2 ≤ 2 * R := by
      rw [dist_eq_norm]
      calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist
  calc W1 μ ν ≤ transportCost (μ.prod ν) := W1_le_transportCost (isCoupling_prod μ ν)
    _ ≤ ENNReal.ofReal (2 * R) := by
        rw [transportCost]
        calc ∫⁻ p, edist p.1 p.2 ∂(μ.prod ν)
            ≤ ∫⁻ _, ENNReal.ofReal (2 * R) ∂(μ.prod ν) := lintegral_mono_ae hae
          _ = ENNReal.ofReal (2 * R) := by rw [lintegral_const, measure_univ, mul_one]

/-- **`W₁` is finite for boundedly-supported probability measures.** -/
theorem W1_ne_top_of_ae_norm_le (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {R : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (hν : ∀ᵐ y ∂ν, ‖y‖ ≤ R) :
    W1 μ ν ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (W1_le_of_ae_norm_le μ ν hμ hν)

/-- A sphere-supported measure is a.e. of norm `≤ 1` (on the sphere `‖x‖ = 1`). -/
theorem ae_norm_le_one_of_sphere_supported {μ : Measure (Eucl d)} (hμ : μ (sphere d)ᶜ = 0) :
    ∀ᵐ x ∂μ, ‖x‖ ≤ 1 := by
  have h : ∀ᵐ x ∂μ, x ∈ sphere d := by rw [ae_iff]; exact hμ
  filter_upwards [h] with x hx
  exact le_of_eq (norm_eq_one_of_mem_sphere hx)

/-- **`W₁ ≤ 2` for sphere-supported probability measures** (diameter of the unit sphere). -/
theorem W1_le_two_of_sphere_supported {μ ν : Measure (Eucl d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ (sphere d)ᶜ = 0) (hν : ν (sphere d)ᶜ = 0) :
    W1 μ ν ≤ 2 := by
  have h := W1_le_of_ae_norm_le μ ν (ae_norm_le_one_of_sphere_supported hμ)
    (ae_norm_le_one_of_sphere_supported hν)
  rw [show (2 : ℝ) * 1 = 2 by ring, ENNReal.ofReal_ofNat] at h
  exact h

/-- **`W₁` is finite for sphere-supported probability measures** — discharges the `W1 μ ν ≠ ⊤`
hypotheses pervading the field's measure moduli, and makes `(W1 μ ν).toReal` a genuine metric value. -/
theorem W1_ne_top_of_sphere_supported {μ ν : Measure (Eucl d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ (sphere d)ᶜ = 0) (hν : ν (sphere d)ᶜ = 0) :
    W1 μ ν ≠ ⊤ :=
  W1_ne_top_of_ae_norm_le μ ν (ae_norm_le_one_of_sphere_supported hμ)
    (ae_norm_le_one_of_sphere_supported hν)

end MeasureToMeasure
