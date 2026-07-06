import MeasureToMeasure.Foundations.Wasserstein

/-!
# `W₁` map-coupling and mixture tools (M3b existence, leaf S3b-i)

Toward the hard direction of the `W₁ ↔ weak` comparison (leaf S3b, `exists_meanFieldFlow`), we bound
`W₁` **from above** by exhibiting couplings. The repo already banks the analogous `W₂` tools
(`W2sq_map_le`, `sqTransportCost_finset_sum_smul`, `W2_convexCombo_le`); this file records the `W₁`
(linear) analogs, which are the primal upper-bound machinery the cell-matching coupling needs:

* `transportCost_finset_sum_smul` — the transport cost is linear in the mixing measure;
* `W1_map_le` — `W₁(T₁_# μ, T₂_# μ) ≤ ∫ dist(T₁ x, T₂ x) dμ`, witnessed by the coupling
  `(T₁, T₂)_# μ`. With `T₁ = id` and `T₂` a cell-rounding map this is the `W₁`-approximation step;
* `W1_convexCombo_le` — `W₁` is convex under mixtures: if `∑ aₖ = 1` and each `W₁(Pₖ, Qₖ) ≤ ε`, then
  `W₁(∑ aₖ • Pₖ, ∑ aₖ • Qₖ) ≤ ε` (simpler than the `W₂` version — the cost is already linear).

All three mirror the banked `W₂` proofs with `edist` in place of `edist²` and no root exponent.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureToMeasure

variable {d : ℕ}

/-- The **transport cost is linear in the mixing measure**:
`transportCost (∑ aₖ • πₖ) = ∑ aₖ · transportCost πₖ` (the lower integral splits over the finite sum
and pulls out each scalar). The `W₁` analog of `sqTransportCost_finset_sum_smul`. -/
theorem transportCost_finset_sum_smul {M : ℕ} (a : Fin M → ℝ≥0∞)
    (π : Fin M → Measure (Eucl d × Eucl d)) :
    transportCost (∑ k, a k • π k) = ∑ k, a k * transportCost (π k) := by
  rw [transportCost, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  rfl

/-- **Map-coupling bound for `W₁`.** The `W₁` distance between two pushforwards of `μ` is at most the
`L¹(μ)` cost of moving `T₁` to `T₂`, witnessed by the coupling `(T₁, T₂)_# μ`:
`W₁(T₁_# μ, T₂_# μ) ≤ ∫ dist(T₁ x, T₂ x) dμ`. The `W₁` analog of `W2sq_map_le`. -/
theorem W1_map_le {μ : Measure (Eucl d)} {T₁ T₂ : Eucl d → Eucl d}
    (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) :
    W1 (μ.map T₁) (μ.map T₂) ≤ ∫⁻ x, edist (T₁ x) (T₂ x) ∂μ := by
  have hcpl : IsCoupling (μ.map fun x => (T₁ x, T₂ x)) (μ.map T₁) (μ.map T₂) :=
    ⟨Measure.fst_map_prodMk hT₂, Measure.snd_map_prodMk hT₁⟩
  calc W1 (μ.map T₁) (μ.map T₂)
      ≤ transportCost (μ.map fun x => (T₁ x, T₂ x)) := W1_le_transportCost hcpl
    _ = ∫⁻ x, edist (T₁ x) (T₂ x) ∂μ := by
        rw [transportCost, lintegral_map (by fun_prop) (by fun_prop)]

/-- **Convexity of `W₁` under mixtures.** If `∑ aₖ = 1` and every component pair is within `ε`
(`W₁(Pₖ, Qₖ) ≤ ε`), then so is the mixture: `W₁(∑ aₖ • Pₖ, ∑ aₖ • Qₖ) ≤ ε`. Couple each pair near
optimally, mix the couplings (`isCoupling_finset_sum_smul`), and bound the mixed cost by `ε` via
`∑ aₖ = 1` (the cost is linear, so no Minkowski/root bookkeeping). The `W₁` analog of `W2_convexCombo_le`. -/
theorem W1_convexCombo_le {M : ℕ} (a : Fin M → ℝ≥0∞) {P Q : Fin M → Measure (Eucl d)}
    (ha : ∑ k, a k = 1) {ε : ℝ≥0∞} (hbound : ∀ k, W1 (P k) (Q k) ≤ ε) :
    W1 (∑ k, a k • P k) (∑ k, a k • Q k) ≤ ε := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη hε => ?_
  set B : ℝ≥0∞ := ε + (η : ℝ≥0∞) with hB
  have hdlt : ε < B := by rw [hB]; exact ENNReal.lt_add_right hε.ne (ENNReal.coe_pos.mpr hη).ne'
  have hk : ∀ k, ∃ πk : Measure (Eucl d × Eucl d),
      IsCoupling πk (P k) (Q k) ∧ transportCost πk < B := fun k => by
    simpa only [W1, iInf_lt_iff, exists_prop] using (hbound k).trans_lt hdlt
  choose π hcpl hcost using hk
  have hcplγ : IsCoupling (∑ k, a k • π k) (∑ k, a k • P k) (∑ k, a k • Q k) :=
    isCoupling_finset_sum_smul a hcpl
  have hA : ∑ k, a k * transportCost (π k) ≤ B := by
    calc ∑ k, a k * transportCost (π k)
        ≤ ∑ k, a k * B := Finset.sum_le_sum fun k _ => by gcongr; exact (hcost k).le
      _ = B := by rw [← Finset.sum_mul, ha, one_mul]
  calc W1 (∑ k, a k • P k) (∑ k, a k • Q k)
      ≤ transportCost (∑ k, a k • π k) := W1_le_transportCost hcplγ
    _ = ∑ k, a k * transportCost (π k) := transportCost_finset_sum_smul a π
    _ ≤ B := hA

end MeasureToMeasure
