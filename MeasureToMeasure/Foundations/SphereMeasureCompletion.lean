import MeasureToMeasure.Foundations.Wasserstein
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Probability measures on the sphere form a compact, complete metric space

Foundation for discharging `exists_meanFieldFlow` (milestone **M3b existence**). The McKean–Vlasov
existence proof is a Picard / Banach fixed point of the map `μ ↦ (Φ_·)_# μ₀` (push the initial
measure along the flow that solves the characteristic ODE at the *current* measure). That fixed
point needs a **complete** metric space of probability measures to live in. On the compact sphere
subtype `↥(sphere d)`, Mathlib `v4.31.0` already supplies the whole substrate:

* **Prokhorov** (`instCompactSpaceProbabilityMeasure`, `Mathlib.MeasureTheory.Measure.Prokhorov`):
  `ProbabilityMeasure ↥(sphere d)` is a `CompactSpace` in the weak (narrow-convergence) topology,
  *because the sphere is compact*.
* **Lévy–Prokhorov metrization** (`LevyProkhorov.probabilityMeasureHomeomorph`): on the separable
  sphere subtype, that weak topology equals the Lévy–Prokhorov metric topology.
* A compact metric space is complete.

So `LevyProkhorov (ProbabilityMeasure ↥(sphere d))` is a compact, complete metric space — the
ambient space in which the fixed point will be taken.

This file banks *only* that substrate, kernel-clean. The remaining campaign work (NOT here) is
(a) the bridge between sphere-supported `Measure (Eucl d)` and `ProbabilityMeasure ↥(sphere d)`,
and (b) comparing the project's coupling `W₁`/`W₂` (`Foundations.Wasserstein`) to this weak
topology, so the banked field moduli (`Foundations.MeanFieldWellPosed`) drive the contraction.

`-- ForMathlib candidate:` the compact/complete packaging of `LevyProkhorov (ProbabilityMeasure X)`
for a compact metric base `X` is generic (no dependence on the sphere).
-/

open MeasureTheory

namespace MeasureToMeasure

variable (d : ℕ)

/-- The unit sphere subtype is compact — a closed, bounded set in the finite-dimensional space
`Eucl d` (proper space). -/
instance instCompactSpaceSphere : CompactSpace ↥(sphere d) := by
  rw [sphere]; exact Metric.sphere.compactSpace _ _

/-- **Prokhorov on the sphere.** Probability measures on the compact sphere form a compact space in
the weak topology. -/
theorem compactSpace_probabilityMeasure_sphere :
    CompactSpace (ProbabilityMeasure ↥(sphere d)) := inferInstance

/-- On the separable sphere subtype, the weak topology on `ProbabilityMeasure ↥(sphere d)` is the
Lévy–Prokhorov metric topology (Mathlib's `probabilityMeasureHomeomorph`). -/
noncomputable def sphereProbHomeomorphLP :
    ProbabilityMeasure ↥(sphere d) ≃ₜ LevyProkhorov (ProbabilityMeasure ↥(sphere d)) :=
  LevyProkhorov.probabilityMeasureHomeomorph

/-- The Lévy–Prokhorov metric space of probability measures on the sphere is compact (transport
`compactSpace_probabilityMeasure_sphere` across the metrization homeomorphism). -/
instance instCompactSpaceLevyProkhorovSphere :
    CompactSpace (LevyProkhorov (ProbabilityMeasure ↥(sphere d))) :=
  LevyProkhorov.probabilityMeasureHomeomorph.compactSpace

/-- **The M3b-existence substrate.** `LevyProkhorov (ProbabilityMeasure ↥(sphere d))` is a
`CompleteSpace`: it is a compact metric space, and a compact (uniform) space is complete. This is
the ambient complete metric space for the McKean–Vlasov Picard fixed point. -/
instance instCompleteSpaceLevyProkhorovSphere :
    CompleteSpace (LevyProkhorov (ProbabilityMeasure ↥(sphere d))) :=
  completeSpace_of_isComplete_univ isCompact_univ.isComplete

end MeasureToMeasure
