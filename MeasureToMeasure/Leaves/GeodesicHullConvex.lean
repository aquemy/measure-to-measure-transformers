import MeasureToMeasure.Foundations.GeodesicConvex
import MeasureToMeasure.Leaves.BarycenterNonColinear

/-!
# The geodesic hull is geodesically convex (milestone M5, hull bridge)

Leaf L11 (`BarycenterNonColinear.lean`) models the geodesic-convex hull of a finite set `s` in an open
hemisphere as `geodesicHull s = cone(s) ∩ 𝕊^{d-1}`, and uses it purely as a container for barycenters.
This file connects that hull to the `GeodesicConvex` predicate of `Foundations/GeodesicConvex.lean`,
discharging the geometric content the paper asserts when it calls `conv_g` a *geodesic-convex* set:

* `geodesicConvex_geodesicHull` -- if every generator of `s` lies strictly on `e`'s side
  (`0 < ⟪e, p⟫`, i.e. `s` is in the open hemisphere of `e`), then `geodesicHull s` is geodesically
  convex. This is the "`hull = cone ∩ sphere` is geodesic-convex" characterization, now machine-checked.
* `geodesicHull_subset_hemisphere` -- and that hull sits inside the open hemisphere of `e`.

Together with `geodesicConvex_open_hemisphere` this says the geodesic hull of a hemispherical set is a
geodesically convex subset of a geodesically convex hemisphere -- the exact geometric picture behind the
Section 3.3 disentanglement (disjoint hulls inside a common hemisphere).

The two supporting facts `inConicalSpan.add` (the cone is closed under addition) and
`inner_pos_of_inConicalSpan` (a nonzero conical point in `e`'s hemisphere has `0 < ⟪e, ·⟫`) are proved
here as well. Everything is kernel-checked.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The conical span is closed under addition: add the coefficient functions pointwise. -/
theorem inConicalSpan.add {s : Finset (Eucl d)} {x y : Eucl d}
    (hx : inConicalSpan s x) (hy : inConicalSpan s y) : inConicalSpan s (x + y) := by
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨u, hu, hyu⟩ := hy
  refine ⟨fun p => t p + u p, fun p hp => add_nonneg (ht p hp) (hu p hp), ?_⟩
  rw [hxt, hyu, ← Finset.sum_add_distrib]
  simp_rw [add_smul]

/-- A nonzero conical combination of points that all lie strictly on `e`'s side has strictly positive
`⟪e, ·⟫`: every term `tₚ • ⟪e, p⟫` is nonnegative, and at least one coefficient is positive (else the
point would be `0`). -/
theorem inner_pos_of_inConicalSpan {s : Finset (Eucl d)} {e x : Eucl d}
    (hs : ∀ p ∈ s, 0 < ⟪e, p⟫) (hx : inConicalSpan s x) (hx0 : x ≠ 0) : 0 < ⟪e, x⟫ := by
  obtain ⟨t, ht, hxt⟩ := hx
  rw [hxt, inner_sum]
  simp_rw [real_inner_smul_right]
  refine Finset.sum_pos' (fun p hp => mul_nonneg (ht p hp) (hs p hp).le) ?_
  -- Some coefficient is positive, else `x = ∑ tₚ • p = 0`.
  have : ∃ p ∈ s, t p ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hx0 (by rw [hxt]; exact Finset.sum_eq_zero fun p hp => by rw [h p hp, zero_smul])
  obtain ⟨p, hp, htp⟩ := this
  exact ⟨p, hp, mul_pos (lt_of_le_of_ne (ht p hp) (Ne.symm htp)) (hs p hp)⟩

/-- The geodesic hull of a hemispherical set lies in that open hemisphere. -/
theorem geodesicHull_subset_hemisphere {s : Finset (Eucl d)} {e : Eucl d}
    (hs : ∀ p ∈ s, 0 < ⟪e, p⟫) :
    geodesicHull s ⊆ {x : Eucl d | x ∈ sphere d ∧ 0 < ⟪e, x⟫} := by
  intro x hx
  have hxne : x ≠ 0 := by rw [← norm_ne_zero_iff, hx.1]; norm_num
  exact ⟨by rw [sphere, Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx.1,
    inner_pos_of_inConicalSpan hs hx.2 hxne⟩

/-- **The geodesic hull is geodesically convex (in an open hemisphere).** If every generator of `s`
satisfies `0 < ⟪e, p⟫`, then `geodesicHull s = cone(s) ∩ 𝕊^{d-1}` is closed under normalized positive
chords: the chord `a • x + b • y` is again a conical combination, it is nonzero because `⟪e, ·⟫` stays
strictly positive, and normalizing keeps it on the sphere and in the cone. -/
theorem geodesicConvex_geodesicHull {s : Finset (Eucl d)} {e : Eucl d}
    (hs : ∀ p ∈ s, 0 < ⟪e, p⟫) : GeodesicConvex (geodesicHull s) := by
  refine ⟨fun x hx => by rw [sphere, Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx.1, ?_⟩
  intro x hx y hy a b ha hb
  have hxne : x ≠ 0 := by rw [← norm_ne_zero_iff, hx.1]; norm_num
  have hyne : y ≠ 0 := by rw [← norm_ne_zero_iff, hy.1]; norm_num
  have hcomb : inConicalSpan s (a • x + b • y) := (hx.2.smul ha.le).add (hy.2.smul hb.le)
  have hev : 0 < ⟪e, a • x + b • y⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact add_pos (mul_pos ha (inner_pos_of_inConicalSpan hs hx.2 hxne))
      (mul_pos hb (inner_pos_of_inConicalSpan hs hy.2 hyne))
  have hvne : a • x + b • y ≠ 0 := fun h => by simp [h] at hev
  exact mem_geodesicHull_normalize hcomb hvne

end MeasureToMeasure.Leaves
