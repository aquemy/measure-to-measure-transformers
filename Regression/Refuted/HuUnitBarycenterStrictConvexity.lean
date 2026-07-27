import MeasureToMeasure.Leaves.UnitSphereIntrinsicInterior
import MeasureToMeasure.Leaves.ExtremalBoundaryPoint
import MeasureToMeasure.Leaves.GeodesicHullConvex
import MeasureToMeasure.Statements.SupportedIn

/-!
# `lemma_3_4_part2`'s `_hu` hypothesis is unsatisfiable (finding F25)

The G1 kernel gate of the `lemma_3_4_part2` non-vacuous re-discharge campaign. F22
(`HgenRestUnconditionallyFalse.lean`) showed the 2026-07-19 discharge (PR #260) was vacuous
because its `hgenRest` hypothesis is kernel-unsatisfiable. This file shows the vacuity was
DOUBLY determined: the `_hu` hypothesis, footnote 7's non-degeneracy condition as formalized by
the retractability sub-campaign (the normalized barycenter direction lying in Mathlib's
`intrinsicInterior` of the AMBIENT `convexHull` of the shared support), is ALSO unsatisfiable
in conjunction with the rest of the bundle, for every measure pair and every dimension. Even
the pre-F22 hypothesis list, before `hgenRest` was ever added, could never be invoked.

The reason is strict convexity, not measure theory: sphere-plus-orthant support makes the
barycenter nonzero (`norm_barycenter_pos_of_orthant`), so `u := ‖ℰμ‖⁻¹ • ℰμ` is UNIT-norm; the
support sits on the sphere, hence inside the closed unit ball; and a unit-norm point in the
intrinsic interior of a ball-confined convex hull forces the hull to be the singleton `{u}`
(`Leaves.convexHull_eq_singleton_of_unitNorm_mem_intrinsicInterior`: any second hull point
would place `u` strictly between two hull points, and the closed unit ball of an inner-product
space is strictly convex, so `u` would fall in the OPEN ball). A probability measure whose
support collapses to `{u}` is `dirac u`; with `μ.support = ν.support` BOTH measures are
`dirac u`, contradicting `μ ≠ ν`. Note the proof deliberately does NOT use `NoAtoms`, so it
refutes the OLD (pre-F22) bundle as well as the current one.

What this does and does not refute: the paper's footnote 7 (p.34, arXiv:2411.04551v3) states
its non-degeneracy for `conv_g`, the GEODESIC hull inside the sphere, whose relative interior
is a sphere-intrinsic notion. The unsatisfiable object is OUR transcription of it through
Mathlib's ambient `convexHull` + `intrinsicInterior` (introduced with PR #260's hypothesis
realignment, see the `mean-field-axioms-retractability` notes): the ambient intrinsic interior
of a hull of sphere points can only reach the sphere at a degenerate singleton hull, so the
transcription can never hold for the measures in scope. A formalization erratum (F25), not a
paper gap. Consequence for the re-discharge: the replacement signature must NOT carry `_hu` in
this form; footnote 7's condition needs a sphere-intrinsic transcription (or none at all,
where the asymmetric-cap route does not consume it).

Like `HgenRestUnconditionallyFalse.lean`, this is a bookkeeping record of a live-hypothesis
refutation, not a `Regression/OldStatements.lean` Sig transcription: `_hu` is a hypothesis of
a currently-standing theorem, not a rejected axiom draft, so there is no `Refutations/`
must-fail adapter to pair with it.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Leaves MeasureToMeasure.Statements
open scoped RealInnerProductSpace

/-- A probability measure vanishing off a singleton is the Dirac mass there. Support step for
the F25 refutation; stated for a general measurable space with measurable singletons. -/
theorem prob_eq_dirac_of_compl_singleton_null {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] {u : α}
    (h : μ {u}ᶜ = 0) : μ = Measure.dirac u := by
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases hus : u ∈ s
  · have h1 : μ {u} = 1 := (prob_compl_eq_zero_iff (MeasurableSet.singleton u)).mp h
    have hsu : μ s = μ (s ∩ {u}) + μ (s \ {u}) :=
      (measure_inter_add_sdiff s (MeasurableSet.singleton u)).symm
    have hd0 : μ (s \ {u}) = 0 := measure_mono_null (fun x hx => hx.2) h
    have hcap : s ∩ {u} = {u} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hus, rfl⟩, fun x hx => hx.2⟩
    rw [hsu, hd0, add_zero, hcap, h1, Set.indicator_of_mem hus]
    rfl
  · rw [Set.indicator_of_notMem hus]
    refine measure_mono_null (fun x hx => ?_) h
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hus hx

/-- **The `_hu` hypothesis bundle is unsatisfiable** (finding F25). For every dimension and
every pair of sphere- and orthant-supported probability measures with equal supports, footnote
7's non-degeneracy condition as `lemma_3_4_part2` carries it (`u := ‖ℰμ‖⁻¹ • ℰμ` in the
ambient `intrinsicInterior` of `convexHull ℝ μ.support`) forces `μ = ν = dirac u`,
contradicting `μ ≠ ν`. Deliberately `NoAtoms`-free, so the refutation covers the pre-F22
hypothesis list too. The sphere hypotheses of both measures and the orthant hypothesis of `ν`
are consumed only through the paper's scope (kept per the repo's underscore convention where
unused); the proof needs `hμs`, `hμ`, `hsupp`, `hu`, and `hne`. -/
theorem lemma_3_4_part2_hu_unsatisfiable {d : ℕ}
    (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (_hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (_hν : supportedIn ν (orthant d))
    (hsupp : μ.support = ν.support)
    (hu : (‖barycenter μ‖⁻¹ • barycenter μ) ∈ intrinsicInterior ℝ (convexHull ℝ μ.support)) :
    False := by
  have hint : Integrable (fun x : Eucl d => x) μ := integrable_id_of_sphere_support hμs
  have hpos : 0 < ‖barycenter μ‖ := norm_barycenter_pos_of_orthant hμs hint hμ
  set u : Eucl d := ‖barycenter μ‖⁻¹ • barycenter μ with hudef
  have hu1 : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hpos)]
  have hsub : μ.support ⊆ Metric.closedBall 0 1 := fun x hx =>
    Metric.sphere_subset_closedBall (support_subset_sphere hμs hx)
  have hhull : convexHull ℝ μ.support = {u} :=
    convexHull_eq_singleton_of_unitNorm_mem_intrinsicInterior hsub hu1 hu
  have hμsub : μ.support ⊆ ({u} : Set (Eucl d)) := hhull ▸ subset_convexHull ℝ _
  have hμnull : μ μ.supportᶜ = 0 := mem_ae_iff.mp (Measure.support_mem_ae (μ := μ))
  have hμc : μ {u}ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr hμsub) hμnull
  have hνsub : ν.support ⊆ ({u} : Set (Eucl d)) := hsupp ▸ hμsub
  have hνnull : ν ν.supportᶜ = 0 := mem_ae_iff.mp (Measure.support_mem_ae (μ := ν))
  have hνc : ν {u}ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr hνsub) hνnull
  exact hne ((prob_eq_dirac_of_compl_singleton_null μ hμc).trans
    (prob_eq_dirac_of_compl_singleton_null ν hνc).symm)

/-- **The pre-F22 `lemma_3_4_part2` hypothesis list is unsatisfiable** (finding F25).
Companion specializing `lemma_3_4_part2_hu_unsatisfiable` to the EXACT hypothesis list of
`Statements/MidLevel.lean`'s `lemma_3_4_part2` up to (and excluding) `hgenRest`: the schedule
data `T`, `hT` and the colinearity `_hcol` are carried verbatim but unused, exactly as the
theorem carries them. So even before `hgenRest` existed (the PR #260 discharge added it), the
statement's hypothesis bundle already had no instances: F22's vacuity was doubly determined,
and any re-discharge keeping `_hu` in this ambient-hull form would be vacuous again. -/
theorem lemma_3_4_part2_pre_F22_bundle_unsatisfiable {d : ℕ}
    (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (_T : ℝ) (_hT : 0 < _T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (_hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ barycenter μ = γ • barycenter ν)
    (hsupp : μ.support = ν.support)
    (hu : (‖barycenter μ‖⁻¹ • barycenter μ) ∈ intrinsicInterior ℝ (convexHull ℝ μ.support)) :
    False :=
  lemma_3_4_part2_hu_unsatisfiable μ ν hne hμs hνs hμ hν hsupp hu

end Regression.Refuted
