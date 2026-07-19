import MeasureToMeasure.Foundations.FlowMap
import MeasureToMeasure.Axioms.ContinuityEquation
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# `orthant`, `supportedIn` — shared vocabulary, split out to avoid a circular import

These definitions used to live in `Statements/MidLevel.lean` directly. Several `Leaves` files
(`Lemma34Part1MeanField.lean`, `DistinctDim.lean`, `OrthantBoundaryGap.lean`) need only THIS small
slice of `MidLevel.lean`, not anything else in it — but `MidLevel.lean` itself needs to import
`Lemma34Part1MeanField.lean` to discharge `lemma_3_4_part2` in place (mirroring how `lemma_3_2` is
proved in place using `Leaves.OrthantRotation`). Importing `MidLevel.lean` from those `Leaves` files
would make that import cycle: `MidLevel → Lemma34Part1MeanField → MidLevel`. Splitting this slice
into its own file (importing only the low-level `Foundations.FlowMap`) lets both sides import this
file directly instead, breaking the cycle. Kept in the SAME `MeasureToMeasure.Statements` namespace
so every existing qualified reference is unaffected.
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms

variable {d : ℕ}

/-- The open positive orthant `Q₁^{d-1} = 𝕊^{d-1} ∩ (ℝ_{>0})^d`, as a subset of `ℝ^d`. -/
def orthant (d : ℕ) : Set (Eucl d) := {x | ∀ i, 0 < x i}

/-- "The support of `μ` is contained in `S`", expressed measure-theoretically as `μ(Sᶜ) = 0` (no mass
outside `S`). Avoids the (absent) packaged measure-support API while staying faithful. -/
def supportedIn (μ : Measure (Eucl d)) (S : Set (Eucl d)) : Prop := μ Sᶜ = 0

/-- The linear-layer flow of a sphere-supported measure stays sphere-supported. -/
theorem measureFlow_supportedIn_sphere (θ : Params d) {T : ℝ} (hT : 0 ≤ T)
    {ν : Measure (Eucl d)} (h : supportedIn ν (sphere d)) :
    supportedIn (measureFlow θ T ν) (sphere d) := by
  show (ν.map (flowMap θ T)) (sphere d)ᶜ = 0
  have hms : MeasurableSet (sphere d)ᶜ := (Metric.isClosed_sphere.measurableSet).compl
  rw [Measure.map_apply (measurable_flowMap θ hT) hms]
  refine measure_mono_null (fun x hx => ?_) h
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
  exact fun hxs => hx (flowMap_mem_sphere θ hT hxs)

end MeasureToMeasure.Statements
