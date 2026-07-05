import MeasureToMeasure.Foundations.Wasserstein
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Leaf (Lemma 3.4 Part 1 assembly tail): `W₁ ≤ W₂`

The App. B.3 Part 1 collapse is quantified in `W₂` (`W2_measureFlow_collapse_le`), but the barycenter
is `W₁`-continuous (`norm_barycenter_sub_le_W1`, Kantorovich–Rubinstein). The bridge is the standard
`W₁ ≤ W₂`: on any *probability* transport plan the linear cost is dominated by the root quadratic cost
(`L¹ ≤ L²`), and the two infima that define `W₁`, `W₂` preserve the inequality.

The per-plan step is Hölder with conjugate exponents `(2, 2)` and the constant `1`:
`∫ dist dπ = ∫ dist·1 dπ ≤ (∫ dist² dπ)^{1/2} · (∫ 1 dπ)^{1/2} = (∫ dist² dπ)^{1/2}`, the last factor
being `1` because `π` is a probability plan (its marginals are probabilities).
-/

namespace MeasureToMeasure

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- On a **probability** transport plan the linear transport cost is dominated by the root quadratic
cost: `∫ dist dπ ≤ (∫ dist² dπ)^{1/2}` (`L¹ ≤ L²`, Hölder with exponents `2, 2`). -/
theorem transportCost_le_rpow_sqTransportCost {π : Measure (Eucl d × Eucl d)}
    [IsProbabilityMeasure π] : transportCost π ≤ sqTransportCost π ^ (2⁻¹ : ℝ) := by
  have hf : AEMeasurable (fun p : Eucl d × Eucl d => edist p.1 p.2) π := by fun_prop
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq π Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hpow : ∀ p : Eucl d × Eucl d, edist p.1 p.2 ^ (2 : ℝ) = edist p.1 p.2 ^ 2 := fun p => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  calc transportCost π
      = ∫⁻ p, (fun p => edist p.1 p.2) p * (fun _ => (1 : ℝ≥0∞)) p ∂π := by
        simp only [mul_one]; rfl
    _ ≤ (∫⁻ p, edist p.1 p.2 ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) *
          (∫⁻ _, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) := hHolder
    _ = sqTransportCost π ^ (2⁻¹ : ℝ) := by
        rw [sqTransportCost, lintegral_congr hpow]
        simp [ENNReal.one_rpow, one_div]

/-- **`W₁ ≤ W₂`** for probability measures: the linear Wasserstein cost is at most the quadratic one.
Each coupling `π` is a probability plan, so `transportCost π ≤ (sqTransportCost π)^{1/2}`; the infima
defining `W₁` and `W₂` inherit the bound. -/
theorem W1_le_W2 {μ ν : Measure (Eucl d)} [IsProbabilityMeasure μ] : W1 μ ν ≤ W2 μ ν := by
  refine le_iInf₂ fun π hπ => ?_
  haveI hprob : IsProbabilityMeasure π := ⟨by rw [← Measure.fst_univ, hπ.1]; exact measure_univ⟩
  exact (W1_le_transportCost hπ).trans transportCost_le_rpow_sqTransportCost

end MeasureToMeasure
