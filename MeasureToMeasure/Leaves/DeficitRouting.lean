import MeasureToMeasure.Leaves.WassersteinWeightDiff

/-!
# A balanced supply/demand routing (`prop_2_2` Stage 1)

The purely combinatorial piece of Stage 1's resolved design (hybrid Voronoi cells + one-shot
deficit/surplus transportation, routed via inter-cell chains -- see the
`prop-2-2-steps-2-3-campaign` project notes). Given a supply `β k` and a demand `α k` at each of
`M` indices with equal totals, produces a routing `w j k` (mass sent from `j` to `k`) that sends
flow only from surplus indices to deficient ones, exactly closes every deficit, and drains every
surplus exactly.

**The construction.** Let `S j := β j - min (α j) (β j)` (`j`'s surplus, `0` unless `α j < β j`)
and `D k := α k - min (α k) (β k)` (`k`'s deficit, `0` unless `β k < α k`). Since `Σ α = Σ β`, the
truncated-subtraction identity `Σ(α k - β k) = Σα - Σβ = 0` forces `Σ D = Σ S =: T` exactly (the
positive and negative parts of a zero-summing sequence have equal total). The **proportional**
routing `w j k := T⁻¹ * S j * D k` (zero when `T = 0`, i.e. no imbalance at all) is then the
discrete analogue of `isCoupling_scaled_prod`'s normalized product `r⁻¹ • (A.prod B)`: summing over
`k` recovers `T⁻¹ * S j * T = S j`, and over `j` recovers `T⁻¹ * T * D k = D k`, using only
`ENNReal.inv_mul_cancel`. No induction, packing, or interval bookkeeping is needed.
-/

namespace MeasureToMeasure.Leaves

open scoped ENNReal

/-- **A balanced supply/demand vector admits a proportional routing.** `w j k ≠ 0` only between a
genuine surplus donor `j` (`α j < β j`) and a genuine deficient recipient `k` (`β k < α k`); every
`k`'s own supply plus everything routed in reaches `α k ⊔ β k` (exactly `α k` if deficient, `β k`
unchanged if not); every `j`'s total outflow is exactly its true surplus. -/
theorem exists_deficit_routing {M : ℕ} (β α : Fin M → ℝ≥0∞) (hβtop : ∀ k, β k ≠ ⊤)
    (hαβ : ∑ k, α k = ∑ k, β k) :
    ∃ w : Fin M → Fin M → ℝ≥0∞,
      (∀ j k, w j k ≠ 0 → β k < α k ∧ α j < β j) ∧
      (∀ k, β k + ∑ j, w j k = α k ⊔ β k) ∧
      (∀ j, ∑ k, w j k = β j - min (α j) (β j)) := by
  have hminle : ∀ k : Fin M, min (α k) (β k) ≤ β k := fun k => min_le_right _ _
  have hminle' : ∀ k : Fin M, min (α k) (β k) ≤ α k := fun k => min_le_left _ _
  have hmintop : ∀ k : Fin M, min (α k) (β k) ≠ ⊤ := fun k => ne_top_of_le_ne_top (hβtop k) (hminle k)
  have hDeq : ∑ k, (α k - min (α k) (β k)) = ∑ k, α k - ∑ k, min (α k) (β k) :=
    Finset.sum_tsub_of_le _ _ _ (fun k _ => hmintop k) (fun k _ => hminle' k)
  have hSeq : ∑ j, (β j - min (α j) (β j)) = ∑ j, β j - ∑ j, min (α j) (β j) :=
    Finset.sum_tsub_of_le _ _ _ (fun k _ => hmintop k) (fun k _ => hminle k)
  have hTeq : ∑ k, (α k - min (α k) (β k)) = ∑ j, (β j - min (α j) (β j)) := by
    rw [hDeq, hSeq, hαβ]
  set T : ℝ≥0∞ := ∑ j, (β j - min (α j) (β j)) with hTdef
  have hTtop : T ≠ ⊤ := by
    rw [hTdef]
    exact ENNReal.sum_ne_top.mpr fun k _ => ne_top_of_le_ne_top (hβtop k) tsub_le_self
  by_cases hT0 : T = 0
  · have hTsum0 : ∑ j, (β j - min (α j) (β j)) = 0 := by rw [← hTdef]; exact hT0
    have hle : ∀ k, β k ≤ α k := fun k => by
      have hk0 : β k - min (α k) (β k) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => zero_le)).mp hTsum0 k (Finset.mem_univ k)
      exact (tsub_eq_zero_iff_le.mp hk0).trans (min_le_left _ _)
    have hall : ∀ k, α k = β k := by
      have hsum0 : ∑ k, (α k - β k) = 0 := by
        rw [Finset.sum_tsub_of_le _ _ _ (fun k _ => hβtop k) (fun k _ => hle k), hαβ, tsub_self]
      intro k
      have hk0 : α k - β k = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => zero_le)).mp hsum0 k (Finset.mem_univ k)
      exact (tsub_eq_zero_iff_le.mp hk0).antisymm (hle k)
    refine ⟨fun _ _ => 0, by simp, fun k => ?_, fun j => ?_⟩
    · simp [hall k]
    · simp [hall j]
  · have hTcancel1 : ∀ a : ℝ≥0∞, T⁻¹ * T * a = a := fun a => by
      rw [ENNReal.inv_mul_cancel hT0 hTtop, one_mul]
    have hTcancel2 : ∀ a : ℝ≥0∞, T⁻¹ * a * T = a := fun a => by
      rw [mul_right_comm, ENNReal.inv_mul_cancel hT0 hTtop, one_mul]
    refine ⟨fun j k => T⁻¹ * (β j - min (α j) (β j)) * (α k - min (α k) (β k)), ?_, ?_, ?_⟩
    · intro j k hwjk
      simp only at hwjk
      have hSj : β j - min (α j) (β j) ≠ 0 := fun hS0 => hwjk (by rw [hS0]; ring)
      have hDk : α k - min (α k) (β k) ≠ 0 := fun hD0 => hwjk (by rw [hD0]; ring)
      refine ⟨?_, ?_⟩
      · rcases le_total (α k) (β k) with h | h
        · exact (hDk (by rw [min_eq_left h, tsub_self])).elim
        · exact lt_of_le_of_ne h (fun heq => hDk (by rw [heq, min_self, tsub_self]))
      · rcases le_total (α j) (β j) with h | h
        · exact lt_of_le_of_ne h (fun heq => hSj (by rw [heq, min_self, tsub_self]))
        · exact (hSj (by rw [min_eq_right h, tsub_self])).elim
    · intro k
      have hsum : ∑ j, T⁻¹ * (β j - min (α j) (β j)) * (α k - min (α k) (β k))
          = α k - min (α k) (β k) := by
        have hstep : ∑ j, T⁻¹ * (β j - min (α j) (β j)) * (α k - min (α k) (β k))
            = T⁻¹ * (∑ j, (β j - min (α j) (β j))) * (α k - min (α k) (β k)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [hstep, ← hTdef, hTcancel1]
      rw [hsum]
      rcases le_total (α k) (β k) with h | h
      · rw [min_eq_left h, tsub_self, add_zero, sup_eq_right.mpr h]
      · rw [min_eq_right h, add_tsub_cancel_of_le h, sup_eq_left.mpr h]
    · intro j
      have hstep : ∑ k, T⁻¹ * (β j - min (α j) (β j)) * (α k - min (α k) (β k))
          = T⁻¹ * (β j - min (α j) (β j)) * ∑ k, (α k - min (α k) (β k)) := by
        rw [← Finset.mul_sum]
      rw [hstep, hTeq, hTcancel2]

end MeasureToMeasure.Leaves
