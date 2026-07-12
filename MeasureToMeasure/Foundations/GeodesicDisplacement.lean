import MeasureToMeasure.Foundations.GeodesicDistance
import MeasureToMeasure.Axioms.ContinuityEquation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Geodesic ball growth under an unconditional displacement bound

`flowMap_dist_self_le` (`Foundations/FlowMap.lean`) bounds how far ANY schedule can move a point,
in the AMBIENT (chord) metric, with no ball/region hypothesis at all. This file converts that into
a GEODESIC statement and combines it with mass monotonicity (`le_measureFlow_of_mapsTo`) to get: any
schedule can only ever GROW a geodesic ball's retained mass, into a slightly larger ball whose extra
radius is an explicit, computable, shrinkable quantity -- unconditionally, with no disjointness
hypothesis on the schedule at all.

**Motivation (prop_2_2 Stage 3/4 relay campaign, leaf 4 piece 3).** The connector/straddle junction
has a proven scale-invariant impossibility (see `prop-2-2-steps-2-3-campaign` project notes) when the
straddle hop is required to be geometrically DISJOINT from the connector chain's tail. This file's
`measureFlow_geodesicBall_grow` sidesteps that requirement entirely: composing the straddle switch
after the connector chain does not need to avoid the connector's retained ball at all -- it can only
ever ENLARGE it, by a margin computable purely from the straddle switch's own parameters, with no
reference to the connector chain's geometry whatsoever.

**The chord-to-arc conversion.** `dist x y = 2 sin(d_g(x,y)/2)` for unit vectors (half-angle chord
formula), and Jordan's inequality (`Real.mul_le_sin`, `(2/π)·t ≤ sin t` on `[0,π/2]`) gives
`d_g(x,y) ≤ (π/2) · dist x y` -- the constant is not optimized, only needs to be finite and fixed, so
any point moving little in the ambient metric also moves little geodesically.
-/

namespace MeasureToMeasure

open MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Half-angle chord formula.** For unit vectors, the squared ambient distance is
`4 sin²(d_g(x,y)/2)` -- the standard chord-length identity, via `‖x-y‖² = 2 - 2⟪x,y⟫` and the
double-angle cosine identity. -/
theorem dist_sq_eq_four_mul_sin_half_geodesicDist_sq {x y : Eucl d} (hx : x ∈ sphere d)
    (hy : y ∈ sphere d) :
    dist x y ^ 2 = 4 * Real.sin (geodesicDist x y / 2) ^ 2 := by
  have hnx : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hny : ‖y‖ = 1 := norm_eq_one_of_mem_sphere hy
  have h1 : dist x y ^ 2 = ‖x - y‖ ^ 2 := by rw [dist_eq_norm]
  rw [h1, @norm_sub_sq_real, hnx, hny]
  have hcos := cos_geodesicDist hx hy
  have hhalf := Real.cos_two_mul_eq_one_sub (geodesicDist x y / 2)
  rw [show 2 * (geodesicDist x y / 2) = geodesicDist x y by ring] at hhalf
  nlinarith [hcos, hhalf]

/-- **Ambient-to-geodesic displacement conversion.** For unit vectors, geodesic distance is bounded
by `(π/2)` times the ambient (chord) distance -- Jordan's inequality applied to the half-angle chord
formula. The constant `π/2` is not optimal, only finite and fixed: this is what turns
`flowMap_dist_self_le`'s ambient bound into a bound usable with `geodesicBall`. -/
theorem geodesicDist_le_pi_div_two_mul_dist {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    geodesicDist x y ≤ (Real.pi / 2) * dist x y := by
  have hmem := geodesicDist_mem_Icc x y
  have hhalf_mem : geodesicDist x y / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hjordan := Real.mul_le_sin hhalf_mem.1 hhalf_mem.2
  have hdistnn : 0 ≤ dist x y := dist_nonneg
  have hsinnn : 0 ≤ Real.sin (geodesicDist x y / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi hhalf_mem.1
    linarith [hhalf_mem.2, Real.pi_pos]
  have hsq := dist_sq_eq_four_mul_sin_half_geodesicDist_sq hx hy
  have hsin_eq : Real.sin (geodesicDist x y / 2) = dist x y / 2 := by
    nlinarith [hsq, hsinnn, hdistnn]
  rw [hsin_eq] at hjordan
  have hpine : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp at hjordan
  linarith [hjordan]

/-- **Geodesic ball growth under a displacement-bounded schedule.** ANY schedule can only ever GROW
a geodesic ball's retained mass, by switching in extra mass from a slightly larger ball -- no
disjointness hypothesis on `θ`, and no relationship at all between `θ` and `c`/`r`. The growth margin
`(π/2) · T · (sum of block bounds)` is `flowMap_dist_self_le`'s ambient bound converted to geodesic
terms. This is the tool for showing that composing a switch which overlaps an already-placed point's
target ball can only have pushed it into a slightly bigger ball, never lost it outright -- the
mass-level counterpart of the pointwise displacement bound. -/
theorem measureFlow_geodesicBall_grow (θ : Params d) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Eucl d)) (c : Eucl d) (hc : c ∈ sphere d) (r : ℝ) :
    μ (geodesicBall c r) ≤
      Axioms.measureFlow θ T μ
        (geodesicBall c (r + (Real.pi / 2) * (T * (θ.map Block.bound).sum))) := by
  apply Axioms.le_measureFlow_of_mapsTo θ hT μ (measurableSet_geodesicBall _ _)
  intro x hx
  obtain ⟨hxs, hxr⟩ := hx
  have hys : flowMap θ T x ∈ sphere d := flowMap_mem_sphere θ hT hxs
  refine ⟨hys, ?_⟩
  calc geodesicDist c (flowMap θ T x)
      ≤ geodesicDist c x + geodesicDist x (flowMap θ T x) := geodesicDist_triangle hc hxs hys
    _ < r + (Real.pi / 2) * (T * (θ.map Block.bound).sum) := by
        have hstep1 : geodesicDist x (flowMap θ T x) ≤ (Real.pi / 2) * dist x (flowMap θ T x) :=
          geodesicDist_le_pi_div_two_mul_dist hxs hys
        have hstep2 : dist x (flowMap θ T x) ≤ T * (θ.map Block.bound).sum := by
          rw [dist_comm]; exact flowMap_dist_self_le θ hT x
        nlinarith [hxr, hstep1, hstep2, Real.pi_pos]

end MeasureToMeasure
