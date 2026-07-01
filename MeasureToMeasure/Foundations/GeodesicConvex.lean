import MeasureToMeasure.Foundations.Sphere
import MeasureToMeasure.Foundations.GeodesicDistance

/-!
# Geodesic convexity on the sphere `𝕊^{d-1}`

Foundational layer for milestone **M5** of the formalization of Geshkovski-Rigollet-Ruiz-Balet,
*Measure-to-measure interpolation using Transformers* (arXiv:2411.04551). The paper repeatedly uses
"geodesic-convex" subsets of the sphere (Section 3.3 disentanglement, the orthant / hemisphere
confinement of Lemma 3.2). Mathlib has convexity, convex cones and `SameRay`, but **no** notion of
geodesic convexity on a sphere, so we build it here.

## The definition

On the unit sphere the (minimizing) geodesic arc between two non-antipodal points `x`, `y` is exactly
the set of *normalized positive combinations* `‖a • x + b • y‖⁻¹ • (a • x + b • y)` with `a, b > 0`:
these trace the minor great-circle arc joining `x` to `y`. We therefore define a subset `s` of the
sphere to be **geodesically convex** when it is closed under this normalized-chord operation. This is
the pure-inner-product characterization (no `arccos` or geodesic parametrization), which coincides with
the minimizing-arc definition on any open hemisphere -- the only regime the paper uses it.

## Main results

* `GeodesicConvex` -- the predicate.
* `geodesicConvex_open_hemisphere` -- an open spherical hemisphere `{x ∈ 𝕊 | 0 < ⟪e, x⟫}` is
  geodesically convex. This is the key fact the paper uses (a piece rotated into the orthant lies in
  such a hemisphere and stays there).
* `GeodesicConvex.inter`, `geodesicConvex_iInter` -- geodesic convexity is preserved by (arbitrary)
  intersections; in particular an orthant, being an intersection of hemispheres, is geodesically convex.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- A subset `s` of the unit sphere `𝕊^{d-1}` is **geodesically convex** when, for any two points
`x, y ∈ s` and positive weights `a, b`, the normalized chord `‖a • x + b • y‖⁻¹ • (a • x + b • y)`
again lies in `s`. On an open hemisphere these normalized chords are exactly the minimizing geodesic
arcs, so this is the faithful spherical analogue of ordinary convexity. -/
def GeodesicConvex (s : Set (Eucl d)) : Prop :=
  s ⊆ sphere d ∧
    ∀ x ∈ s, ∀ y ∈ s, ∀ a b : ℝ, 0 < a → 0 < b →
      ‖a • x + b • y‖⁻¹ • (a • x + b • y) ∈ s

/-- A geodesically convex set lies on the sphere. -/
theorem GeodesicConvex.subset_sphere {s : Set (Eucl d)} (hs : GeodesicConvex s) :
    s ⊆ sphere d := hs.1

/-- Normalizing a nonzero vector lands it on the unit sphere. -/
theorem normalize_mem_sphere {v : Eucl d} (hv : v ≠ 0) : ‖v‖⁻¹ • v ∈ sphere d := by
  rw [sphere, Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- **An open spherical hemisphere is geodesically convex.** For a direction `e`, the set of sphere
points strictly on `e`'s side, `{x ∈ 𝕊 | 0 < ⟪e, x⟫}`, is closed under normalized chords: positivity
of `⟪e, ·⟫` is preserved by positive combination and by normalization. -/
theorem geodesicConvex_open_hemisphere (e : Eucl d) :
    GeodesicConvex {x : Eucl d | x ∈ sphere d ∧ 0 < ⟪e, x⟫} := by
  refine ⟨fun x hx => hx.1, ?_⟩
  rintro x ⟨-, hx⟩ y ⟨-, hy⟩ a b ha hb
  -- The combination `v = a • x + b • y` has strictly positive `⟪e, v⟫`, hence is nonzero.
  have hev : 0 < ⟪e, a • x + b • y⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact add_pos (mul_pos ha hx) (mul_pos hb hy)
  have hv : a • x + b • y ≠ 0 := fun h => by simp [h] at hev
  refine ⟨normalize_mem_sphere hv, ?_⟩
  -- `⟪e, normalize v⟫ = ‖v‖⁻¹ * ⟪e, v⟫ > 0`.
  rw [real_inner_smul_right]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hv)) hev

/-- A single sphere point is geodesically convex: every normalized chord `‖a • x + b • x‖⁻¹ •
((a + b) • x)` collapses back to `x`. -/
theorem geodesicConvex_singleton {x : Eucl d} (hx : x ∈ sphere d) : GeodesicConvex {x} := by
  refine ⟨Set.singleton_subset_iff.mpr hx, ?_⟩
  intro p hp q hq a b ha hb
  rw [Set.mem_singleton_iff] at hp hq
  subst p; subst q
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hab : (0 : ℝ) < a + b := by positivity
  have hcomb : a • x + b • x = (a + b) • x := (add_smul a b x).symm
  rw [Set.mem_singleton_iff, hcomb, norm_smul, hxn, mul_one, Real.norm_eq_abs, abs_of_pos hab,
    smul_smul, inv_mul_cancel₀ (ne_of_gt hab), one_smul]

/-- Geodesic convexity is preserved under intersection. -/
theorem GeodesicConvex.inter {s t : Set (Eucl d)} (hs : GeodesicConvex s) (ht : GeodesicConvex t) :
    GeodesicConvex (s ∩ t) :=
  ⟨fun _ hx => hs.1 hx.1, fun x hx y hy a b ha hb =>
    ⟨hs.2 x hx.1 y hy.1 a b ha hb, ht.2 x hx.2 y hy.2 a b ha hb⟩⟩

/-- An arbitrary intersection of geodesically convex sets is geodesically convex, provided the index
family is nonempty (so the intersection lands on the sphere). In particular an orthant `{x ∈ 𝕊 |
∀ i, 0 < ⟪eᵢ, x⟫}`, being an intersection of hemispheres, is geodesically convex. -/
theorem geodesicConvex_iInter {ι : Type*} [Nonempty ι] {s : ι → Set (Eucl d)}
    (hs : ∀ i, GeodesicConvex (s i)) : GeodesicConvex (⋂ i, s i) := by
  refine ⟨fun x hx => (hs (Classical.arbitrary ι)).1 (Set.mem_iInter.mp hx _), ?_⟩
  intro x hx y hy a b ha hb
  rw [Set.mem_iInter] at hx hy ⊢
  exact fun i => (hs i).2 x (hx i) y (hy i) a b ha hb

end MeasureToMeasure
