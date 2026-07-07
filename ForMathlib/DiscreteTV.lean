/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Quemy
-/
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Sub

/-!
# Total-variation tools for measure infima and pushforwards

Two self-contained total-variation facts stated for the residual mass `(μ − μ ⊓ ν)(univ)`:

* `sum_min_le_inf_univ` -- on a finite measurable-singleton space,
  `∑ᵢ min (p{i}) (q{i}) ≤ (p ⊓ q) univ` (`le_inf`; each side of `∑ᵢ min • δᵢ` is `≤ p` and `≤ q`
  by the atom decomposition `Measure.sum_smul_dirac`).
* `tv_map_le` -- **pushforward contracts total variation**:
  `(a_#f − a_#f ⊓ b_#f)(univ) ≤ (a − a ⊓ b)(univ)`.

*Preparation only:* staged for possible upstreaming, not contributed to Mathlib.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace MeasureTheory.Measure

/-- **Discrete total-variation lower bound.** On a finite measurable-singleton space, the shared
mass of two measures dominates the sum of pointwise minima: `∑ᵢ min (p{i}) (q{i}) ≤ (p ⊓ q) univ`.
The discrete sub-measure `∑ᵢ min(p{i},q{i}) • δᵢ` sits below both `p` and `q` (hence below `p ⊓ q`)
by the atom decomposition `p = ∑ᵢ p{i} • δᵢ`. -/
theorem sum_min_le_inf_univ {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p q : Measure ι) :
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

/-- **Pushforward contracts total variation.** For finite measures, pushing forward by a
measurable `f` cannot increase the residual mass: `(a_#f − a_#f ⊓ b_#f)(univ) ≤ (a − a ⊓ b)(univ)`.
Reduces to `(a ⊓ b)(univ) ≤ (a_#f ⊓ b_#f)(univ)`, which holds because
`(a ⊓ b)_#f ≤ a_#f ⊓ b_#f` (`map_mono` on both factors) and pushforward preserves total mass. -/
theorem tv_map_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (a b : Measure α) [IsFiniteMeasure a] [IsFiniteMeasure b] :
    ((a.map f) - (a.map f) ⊓ (b.map f)) Set.univ ≤ (a - a ⊓ b) Set.univ := by
  haveI hamap : IsFiniteMeasure (a.map f) :=
    ⟨by rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]; exact measure_lt_top a _⟩
  haveI : IsFiniteMeasure (a ⊓ b) := isFiniteMeasure_of_le a inf_le_left
  haveI : IsFiniteMeasure ((a.map f) ⊓ (b.map f)) := isFiniteMeasure_of_le (a.map f) inf_le_left
  have hkey : (a ⊓ b) Set.univ ≤ ((a.map f) ⊓ (b.map f)) Set.univ := by
    have h1 : (a ⊓ b).map f ≤ (a.map f) ⊓ (b.map f) :=
      le_inf (Measure.map_mono inf_le_left hf) (Measure.map_mono inf_le_right hf)
    have h2 := Measure.le_iff'.1 h1 Set.univ
    rwa [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ] at h2
  rw [Measure.sub_apply MeasurableSet.univ inf_le_left,
    Measure.sub_apply MeasurableSet.univ inf_le_left,
    Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
  exact tsub_le_tsub_left hkey _

end MeasureTheory.Measure
