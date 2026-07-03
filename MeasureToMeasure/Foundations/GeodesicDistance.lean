import ForMathlib.UnitSphereGeodesic
import MeasureToMeasure.Foundations.Sphere
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

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

-- ForMathlib candidate (general spherical-geometry leaf): stage + readiness-check via
-- lean-math:mathlib-ready before any upstreaming (a human decision, not automated).
/-- Geodesic distance on the unit sphere: `d_g(x, y) = arccos⟪x, y⟫`. -/
noncomputable def geodesicDist (x y : Eucl d) : ℝ := Real.arccos (⟪x, y⟫)

/-- For unit vectors the inner product lies in `[-1, 1]` (Cauchy-Schwarz). -/
theorem inner_le_one {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    ⟪x, y⟫ ≤ 1 :=
  InnerProductGeometry.inner_le_one_of_norm_eq_one
    (norm_eq_one_of_mem_sphere hx) (norm_eq_one_of_mem_sphere hy)

/-- For unit vectors the inner product is at least `-1` (Cauchy-Schwarz). -/
theorem neg_one_le_inner {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    (-1 : ℝ) ≤ ⟪x, y⟫ :=
  InnerProductGeometry.neg_one_le_inner_of_norm_eq_one
    (norm_eq_one_of_mem_sphere hx) (norm_eq_one_of_mem_sphere hy)

/-- `cos (d_g x y) = ⟪x, y⟫`: the cosine of the geodesic distance is the inner product. -/
theorem cos_geodesicDist {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    Real.cos (geodesicDist x y) = ⟪x, y⟫ :=
  Real.cos_arccos (neg_one_le_inner hx hy) (inner_le_one hx hy)

/-- The geodesic distance is nonnegative and at most `π`. -/
theorem geodesicDist_mem_Icc (x y : Eucl d) :
    geodesicDist x y ∈ Set.Icc (0 : ℝ) Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- **Strict Cauchy-Schwarz on the sphere.** For distinct unit vectors (`x ≠ ω` and `x ≠ -ω`) the
inner product lies in the *open* interval `(-1, 1)`. This is the range hypothesis the logistic
reaching estimate (`logistic_flow_reach`) needs: `u = ⟪x, ω⟫` never hits the ODE's fixed points `±1`
as long as `x` avoids the poles `±ω`. -/
theorem inner_mem_Ioo_of_ne {x ω : Eucl d} (hx : x ∈ sphere d) (hω : ω ∈ sphere d)
    (hne : x ≠ ω) (hne' : x ≠ -ω) : (⟪x, ω⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hnx : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hnω : ‖ω‖ = 1 := norm_eq_one_of_mem_sphere hω
  refine ⟨?_, ?_⟩
  · have h := (inner_lt_norm_mul_iff_real (x := x) (y := -ω)).mpr ?_
    · rw [inner_neg_right, hnx, norm_neg, hnω, mul_one] at h; linarith
    · rw [hnx, norm_neg, hnω, one_smul, one_smul]; exact hne'
  · have h := (inner_lt_norm_mul_iff_real (x := x) (y := ω)).mpr ?_
    · rwa [hnx, hnω, mul_one] at h
    · rw [hnx, hnω, one_smul, one_smul]; exact hne

/-- The open **geodesic ball** (spherical cap) `B(z, R) = {x ∈ 𝕊^{d-1} | d_g(z, x) < R}`. This is
the object Appendix B transports mass between; membership carries `x ∈ sphere d`. -/
def geodesicBall (z : Eucl d) (R : ℝ) : Set (Eucl d) := {x | x ∈ sphere d ∧ geodesicDist z x < R}

/-- Points of a geodesic ball lie on the sphere. -/
theorem geodesicBall_subset_sphere (z : Eucl d) (R : ℝ) : geodesicBall z R ⊆ sphere d :=
  fun _ hx => hx.1

/-- The geodesic distance is symmetric. -/
theorem geodesicDist_comm (x y : Eucl d) : geodesicDist x y = geodesicDist y x := by
  rw [geodesicDist, geodesicDist, real_inner_comm]

/-- For unit vectors the geodesic distance is Mathlib's unoriented angle
(`InnerProductGeometry.angle`), via the ForMathlib bridge. -/
theorem geodesicDist_eq_angle {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    geodesicDist x y = InnerProductGeometry.angle x y :=
  (InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one
    (norm_eq_one_of_mem_sphere hx) (norm_eq_one_of_mem_sphere hy)).symm

/-- **Triangle inequality for the geodesic distance**, from Mathlib's unoriented-angle triangle
inequality. This is what turns "`ω` is inside both caps" into containments between caps. -/
theorem geodesicDist_triangle {x y z : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d)
    (hz : z ∈ sphere d) : geodesicDist x z ≤ geodesicDist x y + geodesicDist y z := by
  rw [geodesicDist_eq_angle hx hz, geodesicDist_eq_angle hx hy, geodesicDist_eq_angle hy hz]
  exact InnerProductGeometry.angle_le_angle_add_angle x y z

/-- Distance-to-inner conversion: within geodesic distance `r ≤ π` of `z`, the inner product is
at least `cos r` (anti-monotonicity of `cos` on `[0, π]`). -/
theorem cos_le_inner_of_geodesicDist_le {z x : Eucl d} (hz : z ∈ sphere d) (hx : x ∈ sphere d)
    {r : ℝ} (hr : r ≤ Real.pi) (h : geodesicDist z x ≤ r) : Real.cos r ≤ (⟪z, x⟫ : ℝ) := by
  rw [← cos_geodesicDist hz hx]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _) hr h

/-- Inner-to-distance conversion: inner product at least `cos r` (`0 ≤ r`) puts the point within
geodesic distance `r` of `z`. -/
theorem geodesicDist_le_of_cos_le_inner {z x : Eucl d} {r : ℝ}
    (hr : 0 ≤ r) (h : Real.cos r ≤ (⟪z, x⟫ : ℝ)) : geodesicDist z x ≤ r := by
  rcases le_or_gt r Real.pi with hrπ | hrπ
  · calc geodesicDist z x = Real.arccos (⟪z, x⟫ : ℝ) := rfl
      _ ≤ Real.arccos (Real.cos r) := Real.arccos_le_arccos h
      _ = r := Real.arccos_cos hr hrπ
  · exact (geodesicDist_mem_Icc z x).2.trans hrπ.le

/-- The geodesic distance from a fixed centre is continuous. -/
theorem continuous_geodesicDist (z : Eucl d) :
    Continuous fun x : Eucl d => geodesicDist z x :=
  Real.continuous_arccos.comp (continuous_const.inner continuous_id)

/-- Geodesic balls are measurable: the sphere is closed and the distance sublevel is open. -/
theorem measurableSet_geodesicBall (z : Eucl d) (R : ℝ) :
    MeasurableSet (geodesicBall z R) := by
  have h1 : MeasurableSet (sphere d) := Metric.isClosed_sphere.measurableSet
  have h2 : MeasurableSet {x : Eucl d | geodesicDist z x < R} :=
    (isOpen_lt (continuous_geodesicDist z) continuous_const).measurableSet
  rw [geodesicBall, Set.setOf_and]
  exact (Set.setOf_mem_eq (s := sphere d) ▸ h1).inter h2

end MeasureToMeasure

