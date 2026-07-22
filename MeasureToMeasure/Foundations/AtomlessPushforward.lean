import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Map

/-!
# Pushforward of an atomless measure along an injective-on-support map

`Foundations/AtomlessSplitting.lean` (`exists_measurableSet_subset_measure_eq`) proves atomless-ness
is preserved under pushforward along a `MeasurableEmbedding`, inline, as a step towards Sierpiński's
IVT: it pushes `μ` forward along the (globally injective) `embeddingReal` and shows the pushforward is
still `NoAtoms`, via `(e ⁻¹' {y}).Subsingleton` from `he.injective`, then `measure_singleton`.

This file extracts and generalizes that argument: the map need only be `Measurable` and injective on
a set `s` carrying the full mass of `μ` (`μ sᶜ = 0`), not a global `MeasurableEmbedding`. The proof
is the same idea, widened by one step: `f ⁻¹' {y} ∩ s` is still a subsingleton (by `InjOn` on `s`
instead of global injectivity), hence null under `NoAtoms μ`; the co-null hypothesis `μ sᶜ = 0` then
transports that nullity from `f ⁻¹' {y} ∩ s` to the full preimage `f ⁻¹' {y}` via
`measure_union_le`/`Set.inter_union_distrib_left`.
-/

open MeasureTheory Measure

namespace MeasureToMeasure.Foundations

/-- Pushing an atomless measure `μ` forward along a map `f` that is measurable and injective on a
set `s` of full `μ`-mass (`μ sᶜ = 0`) yields an atomless measure. Generalizes the inline
`MeasurableEmbedding` argument in `exists_measurableSet_subset_measure_eq`
(`Foundations/AtomlessSplitting.lean`) from global injectivity of `f` to `Set.InjOn f s` on a
co-null set. -/
theorem noAtoms_pushforward_of_injOn {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] {μ : Measure α} [NoAtoms μ] {s : Set α} (hμs : μ sᶜ = 0)
    {f : α → β} (hf : Measurable f) (hinj : Set.InjOn f s) :
    NoAtoms (Measure.map f μ) := by
  refine ⟨fun y => ?_⟩
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  -- at most one point of `s` maps to `y`, so `f ⁻¹' {y} ∩ s` is a subsingleton
  have hss : (f ⁻¹' {y} ∩ s).Subsingleton := by
    intro a ha b hb
    have hfa : f a = y := ha.1
    have hfb : f b = y := hb.1
    exact hinj ha.2 hb.2 (hfa.trans hfb.symm)
  -- a subsingleton is null under an atomless measure
  have hnull : μ (f ⁻¹' {y} ∩ s) = 0 := by
    rcases hss.eq_empty_or_singleton with h | ⟨a, h⟩
    · rw [h, measure_empty]
    · rw [h, measure_singleton]
  -- transport nullity from `f ⁻¹' {y} ∩ s` to `f ⁻¹' {y}` using the co-null hypothesis on `s`
  have hle : μ (f ⁻¹' {y}) ≤ μ (f ⁻¹' {y} ∩ s) + μ sᶜ := by
    calc μ (f ⁻¹' {y}) = μ ((f ⁻¹' {y} ∩ s) ∪ (f ⁻¹' {y} ∩ sᶜ)) := by
          rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
      _ ≤ μ (f ⁻¹' {y} ∩ s) + μ (f ⁻¹' {y} ∩ sᶜ) := measure_union_le _ _
      _ ≤ μ (f ⁻¹' {y} ∩ s) + μ sᶜ := by
          gcongr
          exact Set.inter_subset_right
  rw [hnull, zero_add] at hle
  have hub : μ (f ⁻¹' {y}) ≤ 0 := hle.trans (le_of_eq hμs)
  exact le_antisymm hub bot_le

end MeasureToMeasure.Foundations
