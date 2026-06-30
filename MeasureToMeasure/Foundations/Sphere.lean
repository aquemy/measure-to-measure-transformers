import Mathlib

/-!
# The sphere `𝕊^{d-1}` as the ambient space

This file fixes the ambient geometry used throughout the formalization of
Geshkovski-Rigollet-Ruiz-Balet, *Measure-to-measure interpolation using Transformers*
(arXiv:2411.04551). The paper works on the unit sphere `𝕊^{d-1} ⊆ ℝ^d`.

We model `ℝ^d` as `EuclideanSpace ℝ (Fin d)` and the sphere as the metric sphere of
radius `1` centered at the origin. Membership `x ∈ sphere d` is definitionally
`‖x‖ = 1`, which is the only fact most downstream lemmas need.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

/-- The ambient Euclidean space `ℝ^d`. -/
abbrev Eucl (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The unit sphere `𝕊^{d-1} ⊆ ℝ^d`, as a set, defined as `{x : ‖x‖ = 1}`. -/
def sphere (d : ℕ) : Set (Eucl d) := Metric.sphere (0 : Eucl d) 1

/-- A point of the unit sphere has unit norm. -/
theorem norm_eq_one_of_mem_sphere {d : ℕ} {x : Eucl d} (hx : x ∈ sphere d) :
    ‖x‖ = 1 := by
  simpa [sphere, dist_eq_norm] using hx

/-- A point of the unit sphere has unit self-inner-product. -/
theorem inner_self_eq_one_of_mem_sphere {d : ℕ} {x : Eucl d} (hx : x ∈ sphere d) :
    ⟪x, x⟫ = 1 := by
  have h : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  rw [real_inner_self_eq_norm_sq, h]; ring

end MeasureToMeasure
