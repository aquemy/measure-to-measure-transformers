import MeasureToMeasure.Foundations.SphereMeasureCompletion

/-!
# The sphere subtype–measure bridge (M3b existence, leaf S1)

First leaf of the Wasserstein completeness sub-campaign toward discharging `exists_meanFieldFlow`
(M3b existence). The mean-field field's `W₁` moduli (`MeanFieldWellPosed.norm_field_sub_measure_W1_le`
etc.) live on **sphere-supported probability measures on `Eucl d`** (`Measure (Eucl d)` with
`IsProbabilityMeasure` and `μ (sphere d)ᶜ = 0`), whereas the **completeness** we need for the Picard
fixed point is the one banked in `SphereMeasureCompletion` on `ProbabilityMeasure ↥(sphere d)` (the
Lévy–Prokhorov / weak topology, complete because the sphere is compact). To transport that
completeness to the `W₁` side we first need the two carriers to be the same object.

This leaf establishes that correspondence, `sphereProbEquiv`, from Mathlib's measurable-embedding
plumbing (`Metric.sphere` is closed, hence a measurable set, so `Subtype.val : ↥(sphere d) → Eucl d`
is a measurable embedding): restriction `μ ↦ μ.comap Subtype.val` and push-forward
`ν ↦ ν.map Subtype.val` are mutually inverse between

* `SphereProb d := {μ : Measure (Eucl d) // IsProbabilityMeasure μ ∧ μ (sphere d)ᶜ = 0}` and
* `ProbabilityMeasure ↥(sphere d)`,

with the round-trips `MeasurableEmbedding.comap_map` (`comap ∘ map = id`) and `map_comap_subtype_coe`
(`map ∘ comap = restrict`, which equals the identity on a sphere-supported measure). This is the
carrier identification; the genuinely new analytic content (comparing `W₁` with the weak/Lévy–
Prokhorov metric) is the following leaves.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace MeasureToMeasure

variable {d : ℕ}

/-- The unit sphere is a measurable set (it is closed). -/
theorem measurableSet_sphere (d : ℕ) : MeasurableSet (sphere d) := by
  rw [sphere]; exact (Metric.isClosed_sphere).measurableSet

/-- The subtype coercion `↥(sphere d) → Eucl d` is a measurable embedding. -/
theorem measurableEmbedding_sphere_val :
    MeasurableEmbedding (Subtype.val : ↥(sphere d) → Eucl d) :=
  MeasurableEmbedding.subtype_coe (measurableSet_sphere d)

/-- **Sphere-supported probability measures** on `Eucl d`: the carrier of the mean-field field's `W₁`
moduli. A subtype of `Measure (Eucl d)` cut out by `IsProbabilityMeasure` and sphere-support. -/
def SphereProb (d : ℕ) : Type :=
  {μ : Measure (Eucl d) // IsProbabilityMeasure μ ∧ μ (sphere d)ᶜ = 0}

namespace SphereProb

/-- Restrict a sphere-supported probability measure to a probability measure on the sphere subtype. -/
noncomputable def toSub (μ : SphereProb d) : ProbabilityMeasure ↥(sphere d) :=
  haveI : IsProbabilityMeasure μ.val := μ.property.1
  haveI hprob : IsProbabilityMeasure (μ.val.comap (Subtype.val : ↥(sphere d) → Eucl d)) :=
    measurableEmbedding_sphere_val.isProbabilityMeasure_comap
      (by rw [Subtype.range_coe, ae_iff]; exact μ.property.2)
  ⟨μ.val.comap Subtype.val, hprob⟩

/-- Push a probability measure on the sphere subtype forward to a sphere-supported probability measure
on `Eucl d`. -/
noncomputable def ofSub (ν : ProbabilityMeasure ↥(sphere d)) : SphereProb d :=
  ⟨(ν : Measure ↥(sphere d)).map Subtype.val, by
    refine ⟨Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable, ?_⟩
    rw [Measure.map_apply measurable_subtype_coe (measurableSet_sphere d).compl,
      Set.preimage_compl, Subtype.coe_preimage_self, Set.compl_univ, measure_empty]⟩

@[simp] theorem toSub_toMeasure (μ : SphereProb d) :
    (μ.toSub : Measure ↥(sphere d)) = μ.val.comap Subtype.val := rfl

@[simp] theorem ofSub_val (ν : ProbabilityMeasure ↥(sphere d)) :
    (ofSub ν).val = (ν : Measure ↥(sphere d)).map Subtype.val := rfl

/-- Round-trip `map ∘ comap = id` on a sphere-supported measure (restriction to the sphere is the
identity there). -/
theorem ofSub_toSub (μ : SphereProb d) : ofSub (toSub μ) = μ := by
  apply Subtype.ext
  rw [ofSub_val, toSub_toMeasure, map_comap_subtype_coe (measurableSet_sphere d)]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]; exact μ.property.2

/-- Round-trip `comap ∘ map = id` (the measurable-embedding identity). -/
theorem toSub_ofSub (ν : ProbabilityMeasure ↥(sphere d)) : toSub (ofSub ν) = ν := by
  apply Subtype.ext
  show (ofSub ν).val.comap Subtype.val = (ν : Measure ↥(sphere d))
  rw [ofSub_val, measurableEmbedding_sphere_val.comap_map]

end SphereProb

/-- **The sphere subtype–measure bridge.** Sphere-supported probability measures on `Eucl d`
correspond to probability measures on the sphere subtype, via restriction (`comap Subtype.val`) and
push-forward (`map Subtype.val`). This carries the Lévy–Prokhorov completeness banked on
`ProbabilityMeasure ↥(sphere d)` over to the `W₁` field moduli's carrier. -/
noncomputable def sphereProbEquiv : SphereProb d ≃ ProbabilityMeasure ↥(sphere d) where
  toFun := SphereProb.toSub
  invFun := SphereProb.ofSub
  left_inv := SphereProb.ofSub_toSub
  right_inv := SphereProb.toSub_ofSub

end MeasureToMeasure
