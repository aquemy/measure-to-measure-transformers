import MeasureToMeasure.Foundations.SphereProbSeqCompact
import MeasureToMeasure.Foundations.SphereProbMetric
import MeasureToMeasure.Foundations.WeakToW1

/-!
# The `W₁` space of sphere-supported probability measures is complete (M3b existence, leaf S4)

The completeness the McKean–Vlasov Picard fixed point needs, assembled from the sub-campaign's
banked pieces. `SphereProb d` carries the `W₁` pseudometric (`SphereProb.dist_eq`, leaf S2); this
leaf proves it is a `CompleteSpace`.

* `instance : CompleteSpace (SphereProb d)`.

Proof (compactness + Cauchy promotion — sidesteps any `W₁`↔Lévy–Prokhorov uniform equivalence). Given
a `W₁`-Cauchy sequence `f`, the sphere-subtype images `SphereProb.toSub (f n)` have a weakly convergent
subsequence `→ ν` (leaf S4a, Prokhorov compactness). Pushing forward by the inclusion `↥sphere → Eucl d`
(`ProbabilityMeasure.continuous_map`) transports that weak convergence to `Eucl d`, where
`tendsto_W1_of_tendsto` (the crux, leaf S3b) upgrades it to `W1 (f (φ k)).val (ofSub ν).val → 0`, i.e.
the subsequence converges in `W₁`. A Cauchy sequence with a convergent subsequence converges
(`tendsto_nhds_of_cauchySeq_of_subseq`), so the whole sequence tends to `ofSub ν`.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Filter Topology

namespace MeasureToMeasure

variable {d : ℕ}

/-- **`SphereProb d` is complete in the `W₁` pseudometric.** The ambient complete space for the
McKean–Vlasov Picard fixed point, on the field moduli's own carrier (sphere-supported probability
measures on `Eucl d`), rather than the Lévy–Prokhorov type. -/
noncomputable instance instCompleteSpaceSphereProb : CompleteSpace (SphereProb d) := by
  refine Metric.complete_of_cauchySeq_tendsto (fun f hf => ?_)
  -- A weakly convergent subsequence of the sphere-subtype images (Prokhorov compactness).
  obtain ⟨ν, φ, hφ, hφlim⟩ :=
    exists_subseq_tendsto_probabilityMeasure_sphere (fun n => SphereProb.toSub (f n))
  set L : SphereProb d := SphereProb.ofSub ν with hL
  refine ⟨L, tendsto_nhds_of_cauchySeq_of_subseq hf hφ.tendsto_atTop ?_⟩
  -- The push-forward `↥sphere → Eucl d` of a sphere-supported probability recovers the measure.
  have hval_eq : ∀ μ : SphereProb d,
      (ProbabilityMeasure.map (SphereProb.toSub μ)
        continuous_subtype_val.measurable.aemeasurable).toMeasure = μ.val := by
    intro μ
    have h := congrArg Subtype.val (SphereProb.ofSub_toSub μ)
    rw [SphereProb.ofSub_val, SphereProb.toSub_toMeasure] at h
    rw [ProbabilityMeasure.toMeasure_map, SphereProb.toSub_toMeasure]
    exact h
  have hFν : (ProbabilityMeasure.map ν continuous_subtype_val.measurable.aemeasurable).toMeasure
      = L.val := by
    rw [hL, SphereProb.ofSub_val, ProbabilityMeasure.toMeasure_map]
  -- Weak convergence pushes forward from the sphere subtype to `Eucl d`.
  have hweak : Tendsto (fun k => ProbabilityMeasure.map (SphereProb.toSub (f (φ k)))
      continuous_subtype_val.measurable.aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map ν continuous_subtype_val.measurable.aemeasurable)) :=
    ((ProbabilityMeasure.continuous_map continuous_subtype_val).tendsto ν).comp hφlim
  -- The crux: weak convergence ⇒ `W₁` convergence.
  have hW1 : Tendsto (fun k => W1 (f (φ k)).val L.val) atTop (𝓝 0) := by
    have h := tendsto_W1_of_tendsto (fun k => by rw [hval_eq]; exact (f (φ k)).property.2)
      (by rw [hFν]; exact L.property.2) hweak
    simpa only [hval_eq, hFν] using h
  -- Conclude convergence of the subsequence in the `W₁` pseudometric.
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Function.comp_apply, SphereProb.dist_eq]
  have := ((ENNReal.continuousAt_toReal (by simp)).tendsto).comp hW1
  simpa [Function.comp_def] using this

end MeasureToMeasure
