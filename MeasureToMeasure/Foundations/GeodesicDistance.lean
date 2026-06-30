import MeasureToMeasure.Foundations.Sphere

/-!
# Geodesic distance on `𝕊^{d-1}`

The paper uses the geodesic (great-circle) distance `d_g(x, y) = arccos⟪x, y⟫`. Mathlib does not
package this as the Riemannian distance of the sphere, but the function `arccos⟪·,·⟫` is exactly
what every estimate in the paper manipulates, so we take it as the definition and record the two
facts the separating-hyperplane arguments need:

* `⟪x, y⟫ ∈ [-1, 1]` for unit vectors (Cauchy-Schwarz), so `arccos` is in range;
* `cos (d_g x y) = ⟪x, y⟫`, turning inner-product comparisons into angle comparisons.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- Geodesic distance on the unit sphere: `d_g(x, y) = arccos⟪x, y⟫`. -/
noncomputable def geodesicDist (x y : Eucl d) : ℝ := Real.arccos (⟪x, y⟫)

/-- For unit vectors the inner product lies in `[-1, 1]` (Cauchy-Schwarz). -/
theorem inner_le_one {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    ⟪x, y⟫ ≤ 1 := by
  have hb : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
  rw [norm_eq_one_of_mem_sphere hx, norm_eq_one_of_mem_sphere hy, mul_one] at hb
  exact (abs_le.mp hb).2

/-- For unit vectors the inner product is at least `-1` (Cauchy-Schwarz). -/
theorem neg_one_le_inner {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    (-1 : ℝ) ≤ ⟪x, y⟫ := by
  have hb : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
  rw [norm_eq_one_of_mem_sphere hx, norm_eq_one_of_mem_sphere hy, mul_one] at hb
  exact (abs_le.mp hb).1

/-- `cos (d_g x y) = ⟪x, y⟫`: the cosine of the geodesic distance is the inner product. -/
theorem cos_geodesicDist {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    Real.cos (geodesicDist x y) = ⟪x, y⟫ :=
  Real.cos_arccos (neg_one_le_inner hx hy) (inner_le_one hx hy)

/-- The geodesic distance is nonnegative and at most `π`. -/
theorem geodesicDist_mem_Icc (x y : Eucl d) :
    geodesicDist x y ∈ Set.Icc (0 : ℝ) Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

end MeasureToMeasure
