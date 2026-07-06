import MeasureToMeasure.Foundations.WassersteinFinite
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Finite `μ`-continuity-set ball cover of the sphere (M3b existence, leaf S3b-iv-cover)

The topological foundation of the cell-rounding partition in the `weak ⇒ W₁` crux (leaf S3b, toward
`exists_meanFieldFlow`). To build a finite partition of the sphere into small cells whose *boundaries*
carry no `μ`-mass — so that portmanteau (`tendsto_measure_of_null_frontier_of_tendsto`) delivers
cell-mass convergence under weak convergence — one first covers the compact sphere by open balls of
radius `< ε` whose frontiers are `μ`-null, then takes a finite subcover.

* `exists_finite_null_frontier_ball_cover` — for a finite measure `μ` and `ε > 0`, a finite set `F` of
  centres and a radius assignment `rr` with every `rr x ∈ (0, ε)`, every ball `Metric.ball x (rr x)`
  having `μ`-null frontier, and `⋃ x ∈ F, ball x (rr x)` covering the sphere.

The `μ`-null-frontier radius at each centre comes from Mathlib's `exists_null_frontier_thickening`
(`thickening r {x} = ball x r`), which encodes that only countably many radii give a positive-measure
sphere; the finite subcover from `isCompact_sphere` (`Eucl d` is a proper space).
-/

open MeasureTheory Metric

namespace MeasureToMeasure

variable {d : ℕ}

/-- **Finite `μ`-null-frontier ball cover of the sphere.** For a finite measure `μ` and `ε > 0`, the
compact sphere is covered by finitely many open balls of radius `< ε` whose frontiers are `μ`-null.
Each centre gets a radius in `(0, ε)` avoiding the countably many positive-`μ`-mass sphere radii
(`exists_null_frontier_thickening`); `isCompact_sphere` then extracts a finite subcover. -/
theorem exists_finite_null_frontier_ball_cover (μ : Measure (Eucl d)) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset (Eucl d)) (rr : Eucl d → ℝ),
      (∀ x, 0 < rr x) ∧ (∀ x, rr x < ε) ∧
      (∀ x, μ (frontier (Metric.ball x (rr x))) = 0) ∧
      sphere d ⊆ ⋃ x ∈ F, Metric.ball x (rr x) := by
  have hchoose : ∀ x : Eucl d,
      ∃ r, r ∈ Set.Ioo 0 ε ∧ μ (frontier (Metric.ball x r)) = 0 := fun x => by
    obtain ⟨r, hr, hrf⟩ := exists_null_frontier_thickening μ ({x} : Set (Eucl d)) hε
    rw [Metric.thickening_singleton] at hrf
    exact ⟨r, hr, hrf⟩
  choose rr hrrIoo hrrf using hchoose
  obtain ⟨F, hF⟩ := (isCompact_sphere (0 : Eucl d) 1).elim_finite_subcover
    (fun x => Metric.ball x (rr x)) (fun _ => Metric.isOpen_ball)
    (fun y _ => Set.mem_iUnion.2 ⟨y, Metric.mem_ball_self (hrrIoo y).1⟩)
  exact ⟨F, rr, fun x => (hrrIoo x).1, fun x => (hrrIoo x).2, hrrf, hF⟩

end MeasureToMeasure
