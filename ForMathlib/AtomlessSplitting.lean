/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Quemy
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Atomless prescribed-mass splitting (Sierpiński)

Mathlib `v4.31.0` has the atomless class `NoAtoms` but not **Sierpiński's intermediate-value
theorem** for nonatomic measures (the range of `μ` on the measurable subsets of a set `E` is the
whole interval `[0, μ E]`), which is the analytic core behind splitting an atomless probability
measure into pieces of prescribed masses with pairwise disjoint supports. That IVT is proved here
(no axiom): first on the real line (`exists_measurableSet_subset_measure_eq_real`, by continuity of
the primitive), then lifted to any standard Borel space
(`exists_measurableSet_subset_measure_eq`). Everything built on it -- the prescribed-mass disjoint
partition and the probability-measure decomposition -- is machine-checked as well.

The theorem requires a `[StandardBorelSpace X]` hypothesis, not merely `NoAtoms`. `NoAtoms` (null
singletons) is the *point-mass* notion and is too weak on its own: on `ℝ` with the
countable-cocountable σ-algebra and the `0/1` measure, every singleton is null yet no measurable
set has measure `½`, so the IVT fails. Sierpiński's theorem needs *measure-algebra* atomless-ness
(every positive set splits), which `NoAtoms` supplies on a standard Borel space (Borel-isomorphic to
`ℝ`, where an atomless measure has a continuous CDF); the Borel-isomorphism transfer is exactly how
the general form is derived from the real-line case (Fremlin, *Measure Theory* Vol. 2, §215D).

*Preparation only:* staged for possible upstreaming, not contributed to Mathlib.
-/

namespace MeasureTheory

open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- Sierpiński's intermediate-value theorem on the real line (subset form): for a finite atomless
measure on `ℝ`, a measurable `E`, and any `r ≤ μ E`, there is a measurable `F ⊆ E` with `μ F = r`.

Proof: the cumulative function `t ↦ (μ (E ∩ Iic t)).toReal` is continuous -- its increment over
`[0,t]` is the primitive `∫ x in 0..t, 𝟙_E ∂μ`, continuous by
`intervalIntegral.continuous_primitive` precisely because `μ` has no atoms. It runs from `0` (as
`t → -∞`, `Antitone.measure_iInter`) up to `(μ E).toReal` (as `t → +∞`, `Monotone.measure_iUnion`),
so by the intermediate value theorem it attains `r.toReal` at some `t₀`; take `F = E ∩ Iic t₀`. The
endpoints `r = 0` (`F = ∅`) and `r = μ E` (`F = E`) are handled directly.
(Sierpiński 1922; Fremlin §215D.) -/
theorem exists_measurableSet_subset_measure_eq_real (μ : Measure ℝ) [IsFiniteMeasure μ] [NoAtoms μ]
    {E : Set ℝ} (hE : MeasurableSet E) (r : ℝ≥0∞) (hr : r ≤ μ E) :
    ∃ F, MeasurableSet F ∧ F ⊆ E ∧ μ F = r := by
  rcases eq_or_lt_of_le hr with hrE | hrE
  · exact ⟨E, hE, subset_rfl, hrE.symm⟩
  rcases (bot_le : (0 : ℝ≥0∞) ≤ r).eq_or_lt with hr0 | hr0
  · exact ⟨∅, MeasurableSet.empty, Set.empty_subset _, by rw [measure_empty]; exact hr0⟩
  have hrtop : r ≠ ⊤ := ne_top_of_lt hrE
  have hmonoS : Monotone (fun t : ℝ => E ∩ Set.Iic t) := fun s t hst =>
    Set.inter_subset_inter_right E (Set.Iic_subset_Iic.mpr hst)
  have hmono : Monotone (fun t : ℝ => μ (E ∩ Set.Iic t)) := fun s t hst =>
    measure_mono (hmonoS hst)
  -- Continuity of the real-valued cumulative function via the indicator primitive.
  have hint : Integrable (E.indicator (fun _ => (1 : ℝ))) μ := (integrable_const 1).indicator hE
  have key : ∀ s u : ℝ, s ≤ u → (μ (E ∩ Set.Iic u)).toReal
      = (μ (E ∩ Set.Iic s)).toReal + ∫ x in s..u, E.indicator (fun _ => (1 : ℝ)) x ∂μ := by
    intro s u hsu
    have hIoc : (∫ x in s..u, E.indicator (fun _ => (1 : ℝ)) x ∂μ)
        = (μ (E ∩ Set.Ioc s u)).toReal := by
      rw [intervalIntegral.integral_of_le hsu, MeasureTheory.setIntegral_indicator hE]
      simp only [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Set.inter_comm,
        MeasureTheory.measureReal_def]
    rw [hIoc, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    congr 1
    have hdisj : Disjoint (E ∩ Set.Iic s) (E ∩ Set.Ioc s u) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx2.2.1 (not_lt.mpr hx1.2)
    rw [← measure_union hdisj (hE.inter measurableSet_Ioc), ← Set.inter_union_distrib_left,
      Set.Iic_union_Ioc_eq_Iic hsu]
  have hfeq : ∀ t : ℝ, (μ (E ∩ Set.Iic t)).toReal
      = (μ (E ∩ Set.Iic (0 : ℝ))).toReal
        + ∫ x in (0 : ℝ)..t, E.indicator (fun _ => (1 : ℝ)) x ∂μ := by
    intro t
    rcases le_total (0 : ℝ) t with h0t | ht0
    · exact key 0 t h0t
    · rw [intervalIntegral.integral_symm t 0]; linarith [key t 0 ht0]
  have hcont : Continuous (fun t : ℝ => (μ (E ∩ Set.Iic t)).toReal) := by
    rw [funext hfeq]
    exact continuous_const.add (hint.continuous_primitive 0)
  -- The cumulative reaches above `r` (union to `+∞`) and below `r` (intersection to `-∞`).
  obtain ⟨b, hb⟩ : ∃ b : ℝ, r < μ (E ∩ Set.Iic b) := by
    have htend : Filter.Tendsto (fun t : ℝ => μ (E ∩ Set.Iic t)) Filter.atTop (nhds (μ E)) := by
      have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun t : ℝ => E ∩ Set.Iic t) hmonoS
      rwa [← Set.inter_iUnion, Set.iUnion_Iic, Set.inter_univ] at h
    exact (htend.eventually (eventually_gt_nhds hrE)).exists
  obtain ⟨a, ha⟩ : ∃ a : ℝ, μ (E ∩ Set.Iic a) < r := by
    have hInter : ⋂ t : ℝ, E ∩ Set.Iic t = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      obtain ⟨t, ht⟩ := exists_lt x
      exact absurd (Set.mem_iInter.mp hx t).2 (by simp only [Set.mem_Iic, not_le]; exact ht)
    have htend : Filter.Tendsto (fun t : ℝ => μ (E ∩ Set.Iic t)) Filter.atBot (nhds 0) := by
      have h := tendsto_measure_iInter_atBot (μ := μ) (s := fun t : ℝ => E ∩ Set.Iic t)
        (fun t => (hE.inter measurableSet_Iic).nullMeasurableSet) hmonoS ⟨0, measure_ne_top _ _⟩
      rwa [hInter, measure_empty] at h
    exact (htend.eventually (eventually_lt_nhds hr0)).exists
  have hab : a ≤ b :=
    le_of_not_gt fun h => absurd (hmono h.le) (not_le.mpr (ha.trans hb))
  have hfa : (μ (E ∩ Set.Iic a)).toReal ≤ r.toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) hrtop).mpr ha.le
  have hfb : r.toReal ≤ (μ (E ∩ Set.Iic b)).toReal :=
    (ENNReal.toReal_le_toReal hrtop (measure_ne_top _ _)).mpr hb.le
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨hfa, hfb⟩
  simp only at ht
  refine ⟨E ∩ Set.Iic t, hE.inter measurableSet_Iic, Set.inter_subset_left, ?_⟩
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E ∩ Set.Iic t)), ht, ENNReal.ofReal_toReal hrtop]

/-- Sierpiński's intermediate-value theorem for nonatomic measures on a **standard Borel space**
(subset form): the range of `μ` over the measurable subsets of `E` is the full interval `[0, μ E]`.
Reduced to the real line via the measurable embedding `embeddingReal`: push `μ` forward to `ℝ`
(still finite and atomless, since the embedding is injective), solve there, and pull the subset
back. The `[StandardBorelSpace X]` hypothesis is essential -- `NoAtoms` alone is the point-mass
notion and does not imply the splitting property on a coarse σ-algebra (see the module docstring for
the countable-cocountable counterexample). -/
theorem exists_measurableSet_subset_measure_eq (μ : Measure X) [StandardBorelSpace X]
    [IsFiniteMeasure μ] [NoAtoms μ]
    {E : Set X} (hE : MeasurableSet E) (r : ℝ≥0∞) (hr : r ≤ μ E) :
    ∃ F, MeasurableSet F ∧ F ⊆ E ∧ μ F = r := by
  set e := embeddingReal X with he_def
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
  -- push `μ` forward to `ℝ`
  set ν := μ.map e with hν
  haveI : IsFiniteMeasure ν :=
    ⟨by rw [hν, he.map_apply, Set.preimage_univ]; exact measure_lt_top μ Set.univ⟩
  haveI : NoAtoms ν := by
    refine ⟨fun y => ?_⟩
    rw [hν, he.map_apply]
    have hss : (e ⁻¹' {y}).Subsingleton := fun a ha b hb =>
      he.injective (by simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb; rw [ha, hb])
    rcases hss.eq_empty_or_singleton with h | ⟨a, h⟩
    · rw [h, measure_empty]
    · rw [h, measure_singleton]
  -- transport `E` and solve on `ℝ`
  have hEim : MeasurableSet (e '' E) := he.measurableSet_image.mpr hE
  have hνE : ν (e '' E) = μ E := by
    rw [hν, he.map_apply, Set.preimage_image_eq E he.injective]
  obtain ⟨F', hF'meas, hF'sub, hF'μ⟩ :=
    exists_measurableSet_subset_measure_eq_real ν hEim r (by rw [hνE]; exact hr)
  refine ⟨e ⁻¹' F', he.measurable hF'meas, ?_, ?_⟩
  · calc e ⁻¹' F' ⊆ e ⁻¹' (e '' E) := Set.preimage_mono hF'sub
      _ = E := Set.preimage_image_eq E he.injective
  · rw [← he.map_apply, ← hν]; exact hF'μ

/-- Within a set `E` of sufficient measure, carve `M` pairwise-disjoint measurable subsets of
prescribed measures `α k`. Proved by induction on `M` over the Sierpiński IVT theorem
(`exists_measurableSet_subset_measure_eq`): peel off a
subset of measure `α 0` from `E`, then recurse into `E` minus that subset. -/
theorem exists_disjoint_subset_measure_eq (μ : Measure X) [StandardBorelSpace X]
    [IsFiniteMeasure μ] [NoAtoms μ] :
    ∀ {M : ℕ} (α : Fin M → ℝ≥0∞) {E : Set X}, MeasurableSet E → ∑ k, α k ≤ μ E →
      ∃ A : Fin M → Set X, (∀ k, MeasurableSet (A k)) ∧ (∀ k, A k ⊆ E) ∧
        Pairwise (fun i j => Disjoint (A i) (A j)) ∧ ∀ k, μ (A k) = α k := by
  intro M
  induction M with
  | zero =>
      intro α E _ _
      exact ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0, fun i _ => i.elim0, fun k => k.elim0⟩
  | succ M ih =>
      intro α E hE hle
      have hsum : α 0 + ∑ i : Fin M, α i.succ = ∑ k, α k := (Fin.sum_univ_succ α).symm
      have h0le : α 0 ≤ μ E := le_trans (by rw [← hsum]; exact le_self_add) hle
      have hα0top : α 0 ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ E) h0le
      obtain ⟨F, hFmeas, hFsub, hFμ⟩ := exists_measurableSet_subset_measure_eq μ hE (α 0) h0le
      have hE'meas : MeasurableSet (E \ F) := hE.diff hFmeas
      have hμE' : μ (E \ F) = μ E - α 0 := by
        rw [measure_sdiff hFsub hFmeas.nullMeasurableSet (measure_ne_top _ _), hFμ]
      have htaille : ∑ i : Fin M, α i.succ ≤ μ (E \ F) := by
        rw [hμE', ENNReal.le_sub_iff_add_le_left hα0top h0le, hsum]; exact hle
      obtain ⟨A', hA'meas, hA'sub, hA'disj, hA'μ⟩ := ih (fun i => α i.succ) hE'meas htaille
      -- `Fin.cons` computes definitionally at `0` and `i.succ`, so each componentwise
      -- obligation is a term-mode `Fin.cases`.
      refine ⟨Fin.cons F A', Fin.cases hFmeas hA'meas,
        Fin.cases hFsub fun i => (hA'sub i).trans Set.sdiff_subset, ?_, Fin.cases hFμ hA'μ⟩
      have h0 : ∀ j, Disjoint F (A' j) := fun j =>
        Set.disjoint_of_subset_right (hA'sub j) Set.disjoint_sdiff_left.symm
      intro a b hab
      induction a using Fin.cases with
      | zero => induction b using Fin.cases with
        | zero => exact absurd rfl hab
        | succ j => exact h0 j
      | succ i => induction b using Fin.cases with
        | zero => exact (h0 i).symm
        | succ j => exact hA'disj fun h => hab (congrArg Fin.succ h)

/-- Decompose an atomless probability measure into `M` probability measures `P k` with prescribed
convex weights `α k` (`∑ α k = 1`, each `α k ≠ 0`) and pairwise disjoint supports (carriers `S k`):
`μ = ∑ k, α k • P k`. Each `P k := (α k)⁻¹ • μ.restrict (A k)` is the normalized restriction to the
piece `A k` of the prescribed-mass partition. -/
theorem exists_probability_decomposition (μ : Measure X) [StandardBorelSpace X]
    [IsProbabilityMeasure μ] [NoAtoms μ]
    {M : ℕ} (α : Fin M → ℝ≥0∞) (hα : ∑ k, α k = 1) (hα0 : ∀ k, α k ≠ 0) :
    ∃ (P : Fin M → Measure X) (S : Fin M → Set X),
      (∀ k, IsProbabilityMeasure (P k)) ∧ μ = ∑ k, α k • P k ∧
      (∀ k, P k (S k)ᶜ = 0) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) := by
  -- each weight is finite (bounded above by the total mass `1`)
  have hαtop : ∀ k, α k ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top (by rw [hα]; exact ENNReal.one_ne_top)
      (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ k))
  -- carve pairwise-disjoint measurable pieces of prescribed masses inside `univ`
  obtain ⟨A, hAmeas, -, hAdisj, hAμ⟩ :=
    exists_disjoint_subset_measure_eq μ α MeasurableSet.univ
      (le_of_eq (hα.trans measure_univ.symm))
  have hunionmeas : MeasurableSet (⋃ k, A k) := MeasurableSet.iUnion hAmeas
  -- the pieces exhaust `μ`: their union is co-null
  have hμunion : μ (⋃ k, A k) = 1 := by
    rw [measure_iUnion hAdisj hAmeas, tsum_fintype]
    simp only [hAμ]; exact hα
  have hcompl : μ (⋃ k, A k)ᶜ = 0 := by
    rw [measure_compl hunionmeas (measure_ne_top _ _), measure_univ, hμunion, tsub_self]
  -- `μ` is the disjoint sum of its restrictions to the pieces
  have hμpart : μ = ∑ k, μ.restrict (A k) := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hAdisj hAmeas,
        Measure.restrict_congr_set (ae_eq_univ.mpr hcompl), Measure.restrict_univ]
  refine ⟨fun k => (α k)⁻¹ • μ.restrict (A k), A, ?_, ?_, ?_, hAdisj⟩
  · -- each normalized piece is a probability measure
    intro k
    refine ⟨?_⟩
    show ((α k)⁻¹ • μ.restrict (A k)) Set.univ = 1
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hAμ k,
        ENNReal.inv_mul_cancel (hα0 k) (hαtop k)]
  · -- reassembly: `α k • P k = μ.restrict (A k)`, and these sum to `μ`
    show μ = ∑ k, α k • ((α k)⁻¹ • μ.restrict (A k))
    refine hμpart.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [smul_smul, ENNReal.mul_inv_cancel (hα0 k) (hαtop k), one_smul]
  · -- each piece is supported on its carrier `A k`
    intro k
    show ((α k)⁻¹ • μ.restrict (A k)) (A k)ᶜ = 0
    rw [Measure.smul_apply, Measure.restrict_apply (hAmeas k).compl]
    simp

end MeasureTheory
