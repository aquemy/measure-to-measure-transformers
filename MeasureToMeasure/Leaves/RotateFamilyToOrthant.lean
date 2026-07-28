import MeasureToMeasure.Leaves.OrthantRotationMeanField
import MeasureToMeasure.Leaves.SupportPushforward
import MeasureToMeasure.Leaves.ExtremalBoundaryPoint
import MeasureToMeasure.Statements.MidLevel

/-!
# `exists_disentangling_balls` leaf 1, wired to the whole family

`exists_twoPhase_attnMapsTo_orthant` (`OrthantRotationMeanField.lean`) gives a single schedule
rotating ANY sphere-supported probability measure missing a shared direction into the orthant,
and exposes the rotation as ONE shared injective map `R`. This file applies it ONCE to the WHOLE
family (via `SharedMissingDirection`), giving the induction's actual starting point: every member
becomes simultaneously sphere-AND-orthant supported, via the SAME schedule and the SAME map,
before the strong induction on `N` proper begins.

Three exports:

* `exists_rotate_family_to_orthant_map`: the shared-map form. One schedule `θ₀` and one map `R`
  (measurable, continuous, injective, sphere-preserving) with, for EVERY member `i`,
  `attnMeasureFlow θ₀ (μ₀ i) = (μ₀ i).map R` and the support-image identity
  `(attnMeasureFlow θ₀ (μ₀ i)).support = R '' (μ₀ i).support` (both directions from
  `SupportPushforward.lean`, compactness of a sphere-confined support from
  `ExtremalBoundaryPoint.lean`).
* `exclusiveSupportFamily_rotate_family_to_orthant`: the initial-data gate transports through the
  base. `ExclusiveSupportFamily` (each member's support has a point outside the union of the other
  supports) survives the base rotation for free, since an injective shared map preserves
  point-outside-the-union-of-other-supports through the support-image identity.
* `exists_rotate_family_to_orthant`: the original per-member form, re-derived from the shared-map
  form (each member's `Φ` is the same `R`), kept verbatim for existing consumers
  (`DisentangleInductionStep.lean`).

M3b/mid-level staging: consumed when `exists_disentangling_balls`'s full induction is assembled; see
`Statements/MainResults.lean` and the `exists-disentangling-balls-campaign` project notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure MeasureToMeasure.Statements
open scoped RealInnerProductSpace
open MeasureToMeasure.Foundations MeasureToMeasure.Axioms

variable {d : ℕ}

/-- **The induction's initial-data gate.** Every member's support has a witness point avoiding
every OTHER member's support: the family's supports are not mutually swallowed, so each member can
eventually be separated into its own ball. This is exactly the shape an injective shared
pushforward map transports (see `exclusiveSupportFamily_rotate_family_to_orthant`). -/
def ExclusiveSupportFamily {N : ℕ} (μ : Fin N → Measure (Eucl d)) : Prop :=
  ∀ i, ∃ x ∈ (μ i).support, ∀ j, j ≠ i → x ∉ (μ j).support

variable [NeZero d]

/-- **Leaf 1, wired to the whole family, shared-map form**: a shared missing direction gives ONE
schedule `θ₀` and ONE map `R` (measurable, continuous, injective, sphere-preserving) rotating
EVERY family member simultaneously into sphere-AND-orthant support, with each member's flowed
measure literally the pushforward of the original along that same `R`, and the support-image
identity `(attnMeasureFlow θ₀ (μ₀ i)).support = R '' (μ₀ i).support`. `SharedMissingDirection`'s
own `δ` need not satisfy `δ ≤ 1` (only `0 < δ`); clamped to `δ' := min δ 1` internally, since a
smaller cap-gap only WEAKENS the missing-cap containment (the family stays supported off the
enlarged cap too), matching `exists_twoPhase_attnMapsTo_orthant`'s own requirement. -/
theorem exists_rotate_family_to_orthant_map {N : ℕ} (μ₀ : Fin N → Measure (Eucl d))
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) (hd : 2 ≤ d)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hmiss : SharedMissingDirection μ₀)
    (T : ℝ) (hT : 0 < T) :
    ∃ θ₀ : AttnSchedule d, AttnSchedule.switches θ₀ = 2 ∧ AttnSchedule.durationSum θ₀ = 2 * T ∧
      ∃ R : Eucl d → Eucl d, Measurable R ∧ Continuous R ∧ Function.Injective R ∧
        Set.MapsTo R (sphere d) (sphere d) ∧
        ∀ i, supportedIn (attnMeasureFlow θ₀ (μ₀ i)) (sphere d) ∧
          supportedIn (attnMeasureFlow θ₀ (μ₀ i)) (orthant d) ∧
          attnMeasureFlow θ₀ (μ₀ i) = (μ₀ i).map R ∧
          (attnMeasureFlow θ₀ (μ₀ i)).support = R '' (μ₀ i).support := by
  obtain ⟨ω, hω, δ, hδ0, hmisscap⟩ := hmiss
  set δ' : ℝ := min δ 1 with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ0 one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'le : δ' ≤ δ := min_le_left _ _
  obtain ⟨θ₀, hsw, hdur, R, hRmeas, hRcont, hRinj, hRsphere, hRorth, hRmap⟩ :=
    exists_twoPhase_attnMapsTo_orthant hd hω hδ'0 hδ'1 hT
  refine ⟨θ₀, hsw, hdur, R, hRmeas, hRcont, hRinj, hRsphere, fun i => ?_⟩
  have hmap : attnMeasureFlow θ₀ (μ₀ i) = (μ₀ i).map R := hRmap (μ₀ i) (hμs i)
  refine ⟨?_, ?_, hmap, ?_⟩
  · rw [supportedIn, hmap]
    have hmscompl : MeasurableSet (sphere d)ᶜ := Metric.isClosed_sphere.measurableSet.compl
    rw [Measure.map_apply hRmeas hmscompl]
    refine measure_mono_null (fun x hx => ?_) (hμs i)
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
    exact fun hxs => hx (hRsphere hxs)
  · rw [supportedIn, hmap]
    have hmscompl : MeasurableSet (orthant d)ᶜ := by
      have heq : orthant d = ⋂ j : Fin d, {x : Eucl d | 0 < x j} := by
        ext x; simp only [orthant, Set.mem_setOf_eq, Set.mem_iInter]
      rw [heq]
      exact (MeasurableSet.iInter fun j => measurableSet_lt measurable_const (by fun_prop)).compl
    rw [Measure.map_apply hRmeas hmscompl]
    have hsub : R ⁻¹' (orthant d)ᶜ ⊆ (sphere d)ᶜ ∪ {x : Eucl d | (⟪ω, x⟫ : ℝ) ≤ 1 - δ}ᶜ := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_compl_iff] at hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
      obtain ⟨hxs, hxcap⟩ := hcon
      simp only [Set.mem_setOf_eq] at hxcap
      exact hx (hRorth x hxs (by linarith [hδ'le]))
    have hle : (μ₀ i) (R ⁻¹' (orthant d)ᶜ) ≤ 0 := by
      calc (μ₀ i) (R ⁻¹' (orthant d)ᶜ)
          ≤ (μ₀ i) ((sphere d)ᶜ ∪ {x : Eucl d | (⟪ω, x⟫ : ℝ) ≤ 1 - δ}ᶜ) := measure_mono hsub
        _ ≤ (μ₀ i) (sphere d)ᶜ + (μ₀ i) {x : Eucl d | (⟪ω, x⟫ : ℝ) ≤ 1 - δ}ᶜ := measure_union_le _ _
        _ = 0 := by rw [hμs i, hmisscap i]; simp
    exact nonpos_iff_eq_zero.mp hle
  · rw [hmap]
    apply Set.Subset.antisymm
    · exact support_map_subset_image_of_continuous hRmeas hRcont (isCompact_support (hμs i))
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_support_map_of_continuous hRmeas hRcont hx

/-- **The initial-data gate transports through the base rotation for free.** If every member's
support has a point outside the union of the other supports (`ExclusiveSupportFamily`), the
rotated family keeps that property: the shared map `R` is injective, so through the support-image
identity `(attnMeasureFlow θ₀ (μ₀ i)).support = R '' (μ₀ i).support` the image of each member's
witness point stays outside the image of every other support. -/
theorem exclusiveSupportFamily_rotate_family_to_orthant {N : ℕ}
    (μ₀ : Fin N → Measure (Eucl d))
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) (hd : 2 ≤ d)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hmiss : SharedMissingDirection μ₀)
    (hexcl : ExclusiveSupportFamily μ₀) (T : ℝ) (hT : 0 < T) :
    ∃ θ₀ : AttnSchedule d, AttnSchedule.switches θ₀ = 2 ∧ AttnSchedule.durationSum θ₀ = 2 * T ∧
      (∀ i, supportedIn (attnMeasureFlow θ₀ (μ₀ i)) (sphere d) ∧
        supportedIn (attnMeasureFlow θ₀ (μ₀ i)) (orthant d)) ∧
      ExclusiveSupportFamily (fun i => attnMeasureFlow θ₀ (μ₀ i)) := by
  obtain ⟨θ₀, hsw, hdur, R, _hRmeas, _hRcont, hRinj, _hRsphere, hall⟩ :=
    exists_rotate_family_to_orthant_map μ₀ hμ hd hμs hmiss T hT
  refine ⟨θ₀, hsw, hdur, fun i => ⟨(hall i).1, (hall i).2.1⟩, fun i => ?_⟩
  obtain ⟨x, hx, hout⟩ := hexcl i
  refine ⟨R x, ?_, fun j hj hmem => hout j hj ?_⟩
  · show R x ∈ (attnMeasureFlow θ₀ (μ₀ i)).support
    rw [(hall i).2.2.2]
    exact ⟨x, hx, rfl⟩
  · have hmem' : R x ∈ (attnMeasureFlow θ₀ (μ₀ j)).support := hmem
    rw [(hall j).2.2.2] at hmem'
    obtain ⟨y, hy, hyx⟩ := hmem'
    rwa [← hRinj hyx]

/-- **Leaf 1, wired to the whole family** (original per-member form, re-derived from the
shared-map `exists_rotate_family_to_orthant_map`: each member's `Φ` is the same `R`): a shared
missing direction gives ONE schedule that rotates EVERY family member simultaneously into
sphere-AND-orthant support -- the induction's starting point, before the strong induction on `N`
proper begins. -/
theorem exists_rotate_family_to_orthant {N : ℕ} (μ₀ : Fin N → Measure (Eucl d))
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) (hd : 2 ≤ d)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hmiss : SharedMissingDirection μ₀)
    (T : ℝ) (hT : 0 < T) :
    ∃ θ₀ : AttnSchedule d, AttnSchedule.switches θ₀ = 2 ∧ AttnSchedule.durationSum θ₀ = 2 * T ∧
      ∀ i, supportedIn (attnMeasureFlow θ₀ (μ₀ i)) (sphere d) ∧
        supportedIn (attnMeasureFlow θ₀ (μ₀ i)) (orthant d) ∧
        ∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ₀ (μ₀ i) = (μ₀ i).map Φ ∧
          Set.MapsTo Φ (sphere d) (sphere d) := by
  obtain ⟨θ₀, hsw, hdur, R, hRmeas, _hRcont, _hRinj, hRsphere, hall⟩ :=
    exists_rotate_family_to_orthant_map μ₀ hμ hd hμs hmiss T hT
  exact ⟨θ₀, hsw, hdur, fun i =>
    ⟨(hall i).1, (hall i).2.1, R, hRmeas, (hall i).2.2.1, hRsphere⟩⟩

end MeasureToMeasure.Leaves
