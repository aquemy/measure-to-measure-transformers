import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Discrete total-variation lower bound (M3b existence, leaf S3b-iv-tv)

A self-contained discrete-measure fact used in the `weak ⇒ W₁` crux assembly (leaf S3b, toward
`exists_meanFieldFlow`). On a finite measurable-singleton space, the shared mass `(p ⊓ q) univ` of two
measures is at least the sum of pointwise minima. Applied to the cell-rounded pushforwards, this is the
lower bound that — squeezed against `(p ⊓ q) univ ≤ 1` — drives the total variation to `0` once the
cell masses converge (portmanteau).

* `sum_min_le_inf_univ` — `∑ᵢ min (p{i}) (q{i}) ≤ (p ⊓ q) univ`, via `∑ᵢ min(p{i},q{i}) • δᵢ ≤ p ⊓ q`
  (`le_inf`; each side is `≤ p` and `≤ q` by the atom decomposition `Measure.sum_smul_dirac`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace MeasureToMeasure

/-- **Discrete total-variation lower bound.** On a finite measurable-singleton space, the shared mass
of two measures dominates the sum of pointwise minima: `∑ᵢ min (p{i}) (q{i}) ≤ (p ⊓ q) univ`. The
discrete sub-measure `∑ᵢ min(p{i},q{i}) • δᵢ` sits below both `p` and `q` (hence below `p ⊓ q`) by the
atom decomposition `p = ∑ᵢ p{i} • δᵢ`. -/
theorem sum_min_le_inf_univ {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p q : Measure ι) :
    ∑ i, min (p {i}) (q {i}) ≤ (p ⊓ q) Set.univ := by
  have hsmul : ∀ (c d : ℝ≥0∞) (a : ι), c ≤ d → c • Measure.dirac a ≤ d • Measure.dirac a := by
    intro c d a hcd
    refine Measure.le_iff'.2 (fun s => ?_)
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr
  have hmp : (∑ i, min (p {i}) (q {i}) • Measure.dirac i) ≤ p := by
    conv_rhs => rw [← Measure.sum_smul_dirac p, Measure.sum_fintype]
    exact Finset.sum_le_sum (fun i _ => hsmul _ _ i (min_le_left _ _))
  have hmq : (∑ i, min (p {i}) (q {i}) • Measure.dirac i) ≤ q := by
    conv_rhs => rw [← Measure.sum_smul_dirac q, Measure.sum_fintype]
    exact Finset.sum_le_sum (fun i _ => hsmul _ _ i (min_le_right _ _))
  have huniv := Measure.le_iff'.1 (le_inf hmp hmq) Set.univ
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one] at huniv
  exact huniv

end MeasureToMeasure
