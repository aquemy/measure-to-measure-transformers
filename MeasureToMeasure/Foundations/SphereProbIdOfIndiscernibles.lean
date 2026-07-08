import MeasureToMeasure.Foundations.SphereW1Weak
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Identity of indiscernibles for the `W₁` distance on `SphereProb` (M3b existence, leaf S2b)

Upgrades the `PseudoMetricSpace (SphereProb d)` instance (leaf S2) to a genuine `MetricSpace`: if
`dist μ ν = 0` then `μ.val = ν.val` as measures on `Eucl d`.

The banked Kantorovich–Rubinstein bound `SphereProb.abs_integral_sub_le_dist` only tests
**Lipschitz** functions, while Mathlib's measure-extensionality tool
(`ext_of_forall_integral_eq_of_IsFiniteMeasure`) needs **all** bounded continuous functions — a gap
Mathlib has no ready-made density lemma to close. This leaf sidesteps that by testing against the
*concrete* Lipschitz family Mathlib already builds for exactly this purpose: the thickened indicators
`thickenedIndicator (δs n) F` of a closed set `F`, which are `(δs n)⁻¹`-Lipschitz
(`lipschitzWith_thickenedIndicator`) and whose integrals tend to `μ F` as the thickening radius
`δs n → 0` (`tendsto_integral_thickenedIndicator_of_isClosed`). Matching integrals against every
member of this Lipschitz family already pins down the measure of every closed set (by uniqueness of
limits), hence (by `ext_of_generate_finite` over the closed-sets `π`-system, which generates the
Borel σ-algebra) the whole measure.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MeasureToMeasure

variable {d : ℕ}

namespace SphereProb

/-- **Closed sets have equal measure once every Lipschitz integral agrees.** If `μ, ν` are
sphere-supported probability measures with `∫ f dμ = ∫ f dν` for every Lipschitz `f : Eucl d → ℝ`
(with some finite Lipschitz constant, not necessarily `1`), then `μ.val F = ν.val F` for every closed
`F`. The thickened indicators of `F` are the Lipschitz test family. -/
theorem val_apply_eq_of_forall_lipschitz_integral_eq {μ ν : SphereProb d}
    (h : ∀ (f : Eucl d → ℝ) (K : ℝ≥0), LipschitzWith K f →
      ∫ x, f x ∂μ.val = ∫ x, f x ∂ν.val)
    {F : Set (Eucl d)} (hF : IsClosed F) : μ.val F = ν.val F := by
  haveI := μ.property.1
  haveI := ν.property.1
  set δs : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1) with hδs
  have hδs_pos : ∀ n, 0 < δs n := fun n => Nat.one_div_pos_of_nat
  have hδs_lim : Tendsto δs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hint : ∀ n, ∫ x, (thickenedIndicator (hδs_pos n) F x : ℝ) ∂μ.val
      = ∫ x, (thickenedIndicator (hδs_pos n) F x : ℝ) ∂ν.val := fun n =>
    h (fun x => (thickenedIndicator (hδs_pos n) F x : ℝ)) (δs n).toNNReal⁻¹
      (lipschitzWith_thickenedIndicator (hδs_pos n) F)
  have hμtend := tendsto_integral_thickenedIndicator_of_isClosed μ.val hF hδs_pos hδs_lim
  have hνtend := tendsto_integral_thickenedIndicator_of_isClosed ν.val hF hδs_pos hδs_lim
  simp_rw [hint] at hμtend
  have := tendsto_nhds_unique hμtend hνtend
  rwa [Measure.real_def, Measure.real_def, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (measure_ne_top _ _)] at this

/-- **Identity of indiscernibles.** If `dist μ ν = 0` then `μ.val = ν.val`: the `W₁` distance is a
genuine metric on `SphereProb d`, not merely a pseudometric. -/
theorem eq_of_dist_eq_zero {μ ν : SphereProb d} (h : dist μ ν = 0) : μ.val = ν.val := by
  haveI := μ.property.1
  haveI := ν.property.1
  have hlip : ∀ (f : Eucl d → ℝ) (K : ℝ≥0), LipschitzWith K f →
      ∫ x, f x ∂μ.val = ∫ x, f x ∂ν.val := by
    intro f K hf
    rcases eq_or_ne K 0 with hK0 | hK0
    · -- a `0`-Lipschitz map is constant, so the integrals trivially agree (both probability).
      subst hK0
      have hconst : ∀ x y : Eucl d, f x = f y := fun x y => by
        have := hf.dist_le_mul x y
        simpa [dist_le_zero] using this
      rcases isEmpty_or_nonempty (Eucl d) with hE | ⟨⟨x₀⟩⟩
      · simp [integral_of_isEmpty]
      · have hfx : f = fun _ => f x₀ := funext fun x => hconst x x₀
        rw [hfx]; simp
    · have hK0' : (0 : ℝ) < K := by positivity
      have hf1 : LipschitzWith 1 (fun x => (K : ℝ)⁻¹ * f x) := by
        refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
        rw [NNReal.coe_one, one_mul, Real.dist_eq, ← mul_sub, abs_mul,
          abs_of_pos (inv_pos.mpr hK0'), ← Real.dist_eq]
        have hle := hf.dist_le_mul x y
        calc (K : ℝ)⁻¹ * dist (f x) (f y) ≤ (K : ℝ)⁻¹ * (K * dist x y) :=
              mul_le_mul_of_nonneg_left hle (inv_pos.mpr hK0').le
          _ = dist x y := by field_simp
      have hscaled := abs_integral_sub_le_dist hf1 μ ν
      rw [h, abs_le] at hscaled
      have heq : (K : ℝ)⁻¹ * ∫ x, f x ∂μ.val = (K : ℝ)⁻¹ * ∫ x, f x ∂ν.val := by
        have hμ' : Integrable (fun x => (K : ℝ)⁻¹ * f x) μ.val :=
          integrable_of_lipschitz hf1 μ
        have hν' : Integrable (fun x => (K : ℝ)⁻¹ * f x) ν.val :=
          integrable_of_lipschitz hf1 ν
        have hμint : ∫ x, (K : ℝ)⁻¹ * f x ∂μ.val = (K : ℝ)⁻¹ * ∫ x, f x ∂μ.val :=
          integral_const_mul _ _
        have hνint : ∫ x, (K : ℝ)⁻¹ * f x ∂ν.val = (K : ℝ)⁻¹ * ∫ x, f x ∂ν.val :=
          integral_const_mul _ _
        rw [← hμint, ← hνint]
        linarith [hscaled.1, hscaled.2]
      have hKne : (K : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hK0)
      exact mul_left_cancel₀ hKne heq
  have hclosed : ∀ {F : Set (Eucl d)}, IsClosed F → μ.val F = ν.val F :=
    fun hF => val_apply_eq_of_forall_lipschitz_integral_eq hlip hF
  apply MeasureTheory.ext_of_generate_finite {s | IsClosed s} ?_ isPiSystem_isClosed
    (fun s hs => hclosed hs) (hclosed isClosed_univ)
  rw [BorelSpace.measurable_eq (α := Eucl d), borel_eq_generateFrom_isClosed]

end SphereProb

/-- **`MetricSpace (SphereProb d)`.** The `W₁` pseudometric (leaf S2) is a genuine metric: the
subtype equality `μ.val = ν.val` from `SphereProb.eq_of_dist_eq_zero` gives the subtype equality
`μ = ν` via `Subtype.ext`. -/
noncomputable instance : MetricSpace (SphereProb d) where
  eq_of_dist_eq_zero h := Subtype.ext (SphereProb.eq_of_dist_eq_zero h)

end MeasureToMeasure
