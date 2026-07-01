import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Atomless prescribed-mass splitting (Sierpiński)

The paper's Proposition 2.2 needs to split an atomless probability measure into pieces of prescribed
masses with pairwise disjoint supports (`exists_atomless_partition`). Mathlib `v4.31.0` has the
atomless class `NoAtoms` but not **Sierpiński's intermediate-value theorem** for nonatomic measures
(the range of `μ` on the measurable subsets of a set `E` is the whole interval `[0, μ E]`), which is
the analytic core. We take that IVT as a single, standard, clearly-true **labeled axiom**
(`exists_measurableSet_subset_measure_eq`) and *machine-check* everything built on it: the
prescribed-mass disjoint partition here, and the probability-measure decomposition in
`Statements/MidLevel.lean`.

The axiom requires a `[StandardBorelSpace X]` hypothesis, not merely `NoAtoms`. `NoAtoms` (null
singletons) is the *point-mass* notion and is too weak on its own: on `ℝ` with the
countable-cocountable σ-algebra and the `0/1` measure, every singleton is null yet no measurable set
has measure `½`, so the IVT fails. Sierpiński's theorem needs *measure-algebra* atomless-ness (every
positive set splits), which `NoAtoms` supplies on a standard Borel space (Borel-isomorphic to `ℝ`,
where an atomless measure has a continuous CDF). `Eucl d` is standard Borel, so the application is
unaffected. Discharging the axiom itself (a `StandardBorelSpace` + `NoAtoms` proof following Fremlin,
*Measure Theory* Vol. 2, §215D) is the remaining analytic step.
-/

namespace MeasureToMeasure.Foundations

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- AXIOM (Sierpiński's intermediate-value theorem for nonatomic measures, subset form). For a finite
atomless measure `μ` on a **standard Borel space**, a measurable set `E`, and any target `r ≤ μ E`,
there is a measurable subset `F ⊆ E` with `μ F = r`: the range of `μ` over the measurable subsets of
`E` is the full interval `[0, μ E]`. A classical theorem (Sierpiński 1922; Fremlin §215D), absent from
Mathlib `v4.31.0`. The `[StandardBorelSpace X]` hypothesis is essential: `NoAtoms` alone is the
point-mass notion and does not imply the splitting property on a coarse σ-algebra (see the module
docstring for the countable-cocountable counterexample). -/
axiom exists_measurableSet_subset_measure_eq (μ : Measure X) [StandardBorelSpace X]
    [IsFiniteMeasure μ] [NoAtoms μ]
    {E : Set X} (hE : MeasurableSet E) (r : ℝ≥0∞) (hr : r ≤ μ E) :
    ∃ F, MeasurableSet F ∧ F ⊆ E ∧ μ F = r

/-- Within a set `E` of sufficient measure, carve `M` pairwise-disjoint measurable subsets of
prescribed measures `α k`. Proved by induction on `M` over the Sierpiński IVT axiom: peel off a
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
      refine ⟨Fin.cons F A', ?_, ?_, ?_, ?_⟩
      · intro k; refine Fin.cases ?_ ?_ k
        · simpa using hFmeas
        · intro i; simpa using hA'meas i
      · intro k; refine Fin.cases ?_ ?_ k
        · simpa using hFsub
        · intro i; simpa using (hA'sub i).trans Set.sdiff_subset
      · intro a b
        refine Fin.cases ?_ ?_ a
        · refine Fin.cases ?_ ?_ b
          · intro hab; exact absurd rfl hab
          · intro j _
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact Set.disjoint_of_subset_right (hA'sub j) Set.disjoint_sdiff_left.symm
        · intro i
          refine Fin.cases ?_ ?_ b
          · intro _
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact Set.disjoint_of_subset_left (hA'sub i) Set.disjoint_sdiff_left
          · intro j hab
            simp only [Fin.cons_succ]
            exact hA'disj (fun h => hab (congrArg Fin.succ h))
      · intro k; refine Fin.cases ?_ ?_ k
        · simpa using hFμ
        · intro i; simpa using hA'μ i

/-- Decompose an atomless probability measure into `M` probability measures `P k` with prescribed
convex weights `α k` (`∑ α k = 1`, each `α k ≠ 0`) and pairwise disjoint supports (carriers `S k`):
`μ = ∑ k, α k • P k`. Each `P k := (α k)⁻¹ • μ.restrict (A k)` is the normalized restriction to the
piece `A k` of the prescribed-mass partition. This is the true content of `exists_atomless_partition`;
here it is proved (over the Sierpiński IVT axiom), removing the bespoke partition axiom. -/
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

end MeasureToMeasure.Foundations
