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
  `W₁(∑ aₖ • Pₖ, ∑ aₖ • Qₖ) ≤ ε` (simpler than the `W₂` version — the cost is already linear);
* `W1_map_le_of_ae_edist_le` / `W1_map_le_of_edist_le` — **rounding approximation**: if a measurable
  `r` displaces `μ`-a.e. (resp. every) point by `≤ ε`, then `W₁(μ, r_# μ) ≤ ε`. The approximation half
  of the `weak ⇒ W₁` crux (leaf S3b-ii): it turns a geometric displacement bound into a `W₁` bound,
  taking the rounding map as a hypothesis so it is decoupled from how that map is built from a
  diam-`≤ ε` partition. The a.e. form is the one the crux consumes (the measure is sphere-supported).

All mirror the banked `W₂` proofs with `edist` in place of `edist²` and no root exponent.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
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

/-- **Rounding approximation for `W₁` (a.e. form).** If a measurable `r : Eucl d → Eucl d` moves
`μ`-a.e. point by at most `ε` (`edist x (r x) ≤ ε`), then pushing a probability measure forward through
`r` costs at most `ε` in `W₁`: `W₁(μ, r_# μ) ≤ ε`. Immediate from `W1_map_le` with `T₁ = id`, `T₂ = r`
(`μ.map id = μ`) and `∫⁻ ε ∂μ = ε` (the measure is a probability), the displacement bound applied under
the integral by `lintegral_mono_ae`. This is the **approximation half of the `weak ⇒ W₁` crux**
(leaf S3b-ii): a cell-rounding map to representatives of a diam-`≤ ε` partition realises the hypothesis
`μ`-a.e. (the measure is sphere-supported, and `r` is controlled only on the sphere), and this lemma
turns the geometric displacement bound into a `W₁` bound — independently of how `r` is constructed. -/
theorem W1_map_le_of_ae_edist_le {μ : Measure (Eucl d)} [IsProbabilityMeasure μ]
    {r : Eucl d → Eucl d} (hr : Measurable r) {ε : ℝ≥0∞} (hε : ∀ᵐ x ∂μ, edist x (r x) ≤ ε) :
    W1 μ (μ.map r) ≤ ε := by
  calc W1 μ (μ.map r)
      = W1 (μ.map id) (μ.map r) := by rw [Measure.map_id]
    _ ≤ ∫⁻ x, edist (id x) (r x) ∂μ := W1_map_le measurable_id hr
    _ ≤ ∫⁻ _, ε ∂μ := lintegral_mono_ae hε
    _ = ε := by rw [lintegral_const, measure_univ, mul_one]

/-- **Rounding approximation for `W₁` (everywhere form).** The special case of
`W1_map_le_of_ae_edist_le` when `r` displaces *every* point by at most `ε`. -/
theorem W1_map_le_of_edist_le {μ : Measure (Eucl d)} [IsProbabilityMeasure μ]
    {r : Eucl d → Eucl d} (hr : Measurable r) {ε : ℝ≥0∞} (hε : ∀ x, edist x (r x) ≤ ε) :
    W1 μ (μ.map r) ≤ ε :=
  W1_map_le_of_ae_edist_le hr (ae_of_all _ hε)

end MeasureToMeasure
