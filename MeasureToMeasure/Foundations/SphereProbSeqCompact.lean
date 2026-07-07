import MeasureToMeasure.Foundations.SphereMeasureCompletion
import Mathlib.Topology.Sequences

/-!
# Probability measures on the sphere are sequentially compact (M3b existence, leaf S4a)

Toward `CompleteSpace (SphereProb d)` (leaf S4, the completeness the McKean–Vlasov Picard fixed point
needs). `ProbabilityMeasure ↥(sphere d)` is a `CompactSpace` (E1, Prokhorov) but its weak topology is
not registered as first-countable, so `CompactSpace.tendsto_subseq` does not apply directly. It *is*
metrizable via the Lévy–Prokhorov homeomorphism (E1's `sphereProbHomeomorphLP`), and the metric LP
type is compact + first-countable, so the subsequence extraction runs there and transfers back.

* `exists_subseq_tendsto_probabilityMeasure_sphere` — every sequence in `ProbabilityMeasure ↥(sphere d)`
  has a weakly convergent subsequence.

This is what the completeness proof uses to promote a `W₁`-Cauchy sequence to a convergent one:
compactness supplies the limit of a subsequence, and `tendsto_W1_of_tendsto` (the crux) upgrades weak
subsequential convergence to `W₁`, after which Cauchyness gives full convergence.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Filter Topology

namespace MeasureToMeasure

variable {d : ℕ}

/-- **Sequential compactness of `ProbabilityMeasure ↥(sphere d)`.** Every sequence has a weakly
convergent subsequence — extracted in the metric Lévy–Prokhorov type (compact + first-countable) and
transferred back across the metrization homeomorphism `sphereProbHomeomorphLP`. -/
theorem exists_subseq_tendsto_probabilityMeasure_sphere
    (g : ℕ → ProbabilityMeasure ↥(sphere d)) :
    ∃ (ν : ProbabilityMeasure ↥(sphere d)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (g ∘ φ) atTop (𝓝 ν) := by
  obtain ⟨aLP, φ, hφ, hlim⟩ :=
    CompactSpace.tendsto_subseq (fun n => sphereProbHomeomorphLP d (g n))
  refine ⟨(sphereProbHomeomorphLP d).symm aLP, φ, hφ, ?_⟩
  have hcont := ((sphereProbHomeomorphLP d).symm.continuous.tendsto aLP).comp hlim
  simpa [Function.comp_def] using hcont

end MeasureToMeasure
