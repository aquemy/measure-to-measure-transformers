import MeasureToMeasure.Leaves.UniformRadiusPacking
import MeasureToMeasure.Foundations.Sphere

/-!
# Leaf 5, Phase-4 packaging, unit-sphere specialization

`exists_uniform_radius_of_pairwise_ne` (`UniformRadiusPacking.lean`) is proved over an ABSTRACT
`[MetricSpace E]`, deliberately in a file with no `Eucl d`-touching imports (`Eucl d`'s `MetricSpace`
instance is definitionally heavy enough to time out the SAME proof if elaborated with it in scope).
This file only APPLIES that already-proven theorem to the unit-sphere case
`exists_disentangling_balls`'s Phase 4 actually needs -- a cheap term-mode instantiation, not a
re-elaboration, so it stays fast even with `Eucl d` in scope.
-/

namespace MeasureToMeasure.Leaves

open Metric MeasureToMeasure

variable {d : ℕ}

/-- **Phase-4 packaging, specialized to unit vectors**: a family of pairwise-distinct unit vectors
(directions on the sphere) admits a uniform `r ∈ (0,1)` with pairwise distance `≥ 2r` -- unit vectors
always satisfy the abstract lemma's boundedness hypothesis (`dist ≤ ‖·‖+‖·‖ = 2`) via the triangle
inequality. -/
theorem exists_uniform_radius_of_pairwise_ne_unit {ι : Type*} [Fintype ι] [Nonempty ι]
    (α : ι → Eucl d) (hunit : ∀ i, ‖α i‖ = 1) (hne : Pairwise fun i j => α i ≠ α j) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i j, i ≠ j → 2 * r ≤ dist (α i) (α j) :=
  exists_uniform_radius_of_pairwise_ne α
    (fun i j => (dist_le_norm_add_norm (α i) (α j)).trans (by rw [hunit, hunit]; norm_num)) hne

end MeasureToMeasure.Leaves
