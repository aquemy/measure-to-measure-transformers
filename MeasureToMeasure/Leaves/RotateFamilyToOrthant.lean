import MeasureToMeasure.Leaves.OrthantRotationMeanField
import MeasureToMeasure.Statements.MidLevel

/-!
# `exists_disentangling_balls` leaf 1, wired to the whole family

`exists_twoPhase_attnMapsTo_orthant` (`OrthantRotationMeanField.lean`) gives a single schedule
rotating ANY sphere-supported probability measure missing a shared direction into the orthant. This
file applies it ONCE to the WHOLE family (via `SharedMissingDirection`), giving the induction's
actual starting point: every member becomes simultaneously sphere-AND-orthant supported, via the
SAME schedule, before the strong induction on `N` proper begins.

M3b/mid-level staging: consumed when `exists_disentangling_balls`'s full induction is assembled; see
`Statements/MainResults.lean` and the `exists-disentangling-balls-campaign` project notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure MeasureToMeasure.Statements
open scoped RealInnerProductSpace
open MeasureToMeasure.Foundations MeasureToMeasure.Axioms

variable {d : ℕ} [NeZero d]

/-- **Leaf 1, wired to the whole family**: a shared missing direction gives ONE schedule that
rotates EVERY family member simultaneously into sphere-AND-orthant support -- the induction's
starting point, before the strong induction on `N` proper begins. `SharedMissingDirection`'s own
`δ` need not satisfy `δ ≤ 1` (only `0 < δ`); clamped to `δ' := min δ 1` internally, since a smaller
cap-gap only WEAKENS the missing-cap containment (the family stays supported off the enlarged cap
too), matching `exists_twoPhase_attnMapsTo_orthant`'s own requirement. -/
theorem exists_rotate_family_to_orthant {N : ℕ} (μ₀ : Fin N → Measure (Eucl d))
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) (hd : 2 ≤ d)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hmiss : SharedMissingDirection μ₀)
    (T : ℝ) (hT : 0 < T) :
    ∃ θ₀ : AttnSchedule d, AttnSchedule.switches θ₀ = 2 ∧
      ∀ i, supportedIn (attnMeasureFlow θ₀ (μ₀ i)) (sphere d) ∧
        supportedIn (attnMeasureFlow θ₀ (μ₀ i)) (orthant d) ∧
        ∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ₀ (μ₀ i) = (μ₀ i).map Φ ∧
          Set.MapsTo Φ (sphere d) (sphere d) := by
  obtain ⟨ω, hω, δ, hδ0, hmisscap⟩ := hmiss
  set δ' : ℝ := min δ 1 with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ0 one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'le : δ' ≤ δ := min_le_left _ _
  obtain ⟨θ₀, hsw, hall⟩ := exists_twoPhase_attnMapsTo_orthant hd hω hδ'0 hδ'1 hT
  refine ⟨θ₀, hsw, fun i => ?_⟩
  obtain ⟨Φ, hΦmeas, hΦeq, hΦsphere, hΦorth⟩ := hall (μ₀ i) (hμs i)
  refine ⟨?_, ?_, Φ, hΦmeas, hΦeq, hΦsphere⟩
  · rw [supportedIn, hΦeq]
    have hmscompl : MeasurableSet (sphere d)ᶜ := Metric.isClosed_sphere.measurableSet.compl
    rw [Measure.map_apply hΦmeas hmscompl]
    refine measure_mono_null (fun x hx => ?_) (hμs i)
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
    exact fun hxs => hx (hΦsphere hxs)
  · rw [supportedIn, hΦeq]
    have hmscompl : MeasurableSet (orthant d)ᶜ := by
      have heq : orthant d = ⋂ j : Fin d, {x : Eucl d | 0 < x j} := by
        ext x; simp only [orthant, Set.mem_setOf_eq, Set.mem_iInter]
      rw [heq]
      exact (MeasurableSet.iInter fun j => measurableSet_lt measurable_const (by fun_prop)).compl
    rw [Measure.map_apply hΦmeas hmscompl]
    have hsub : Φ ⁻¹' (orthant d)ᶜ ⊆ (sphere d)ᶜ ∪ {x : Eucl d | (⟪ω, x⟫ : ℝ) ≤ 1 - δ}ᶜ := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_compl_iff] at hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
      obtain ⟨hxs, hxcap⟩ := hcon
      simp only [Set.mem_setOf_eq] at hxcap
      exact hx (hΦorth x hxs (by linarith [hδ'le]))
    have hle : (μ₀ i) (Φ ⁻¹' (orthant d)ᶜ) ≤ 0 := by
      calc (μ₀ i) (Φ ⁻¹' (orthant d)ᶜ)
          ≤ (μ₀ i) ((sphere d)ᶜ ∪ {x : Eucl d | (⟪ω, x⟫ : ℝ) ≤ 1 - δ}ᶜ) := measure_mono hsub
        _ ≤ (μ₀ i) (sphere d)ᶜ + (μ₀ i) {x : Eucl d | (⟪ω, x⟫ : ℝ) ≤ 1 - δ}ᶜ := measure_union_le _ _
        _ = 0 := by rw [hμs i, hmisscap i]; simp
    exact nonpos_iff_eq_zero.mp hle

end MeasureToMeasure.Leaves
