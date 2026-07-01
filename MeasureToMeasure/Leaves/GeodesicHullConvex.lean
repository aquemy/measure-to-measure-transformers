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

/-!
## Nesting and minimality

The geodesic hull is monotone in its generating set, contains its (unit) generators, and is the
*smallest* geodesically convex set containing them -- the defining universal property of a hull.
-/

/-- The conical span is monotone in the generating set: extend the coefficients by zero. -/
theorem inConicalSpan.mono {s t : Finset (Eucl d)} (hst : s ⊆ t) {x : Eucl d}
    (hx : inConicalSpan s x) : inConicalSpan t x := by
  obtain ⟨c, hc, hxc⟩ := hx
  refine ⟨fun p => if p ∈ s then c p else 0, fun p _ => by by_cases h : p ∈ s <;> simp [h, hc], ?_⟩
  rw [hxc, ← Finset.sum_subset hst (fun q _ hqs => by simp [hqs])]
  exact Finset.sum_congr rfl (fun q hq => by simp [hq])

/-- The geodesic hull is monotone in its generating set. -/
theorem geodesicHull_mono {s t : Finset (Eucl d)} (hst : s ⊆ t) :
    geodesicHull s ⊆ geodesicHull t :=
  fun _ hx => ⟨hx.1, hx.2.mono hst⟩

/-- Each unit generator lies in the geodesic hull (take the indicator coefficient). -/
theorem mem_geodesicHull_self {s : Finset (Eucl d)} {p : Eucl d} (hp : p ∈ s)
    (hp1 : p ∈ sphere d) : p ∈ geodesicHull s := by
  refine ⟨norm_eq_one_of_mem_sphere hp1, fun q => if q = p then 1 else 0, ?_, ?_⟩
  · intro q _; by_cases h : q = p <;> simp [h]
  · rw [Finset.sum_eq_single p (fun q _ hqp => by simp [hqp]) (fun h => absurd hp h)]; simp

/-- Auxiliary induction: for a geodesically convex `C ⊇ s`, the normalization of any nonzero conical
combination of points of `s` lies in `C`. Proof by `Finset.induction`: split off one generator `p₀`;
the remaining sub-combination `u`, once nonzero, normalizes into `C` by the inductive hypothesis, and
`normalize (w • p₀ + u) = normalize (w • p₀ + ‖u‖ • normalize u)` is then a normalized positive chord
of `p₀ ∈ C` and `normalize u ∈ C`, hence in `C` by geodesic convexity. -/
theorem normalize_conical_mem {C : Set (Eucl d)} (hC : GeodesicConvex C) (s : Finset (Eucl d)) :
    ↑s ⊆ C → ∀ t : Eucl d → ℝ, (∀ p ∈ s, 0 ≤ t p) → (∑ p ∈ s, t p • p) ≠ 0 →
      ‖∑ p ∈ s, t p • p‖⁻¹ • (∑ p ∈ s, t p • p) ∈ C := by
  induction s using Finset.induction with
  | empty => intro _ t _ h; simp only [Finset.sum_empty, ne_eq, not_true_eq_false] at h
  | @insert p₀ s hp₀ IH =>
      intro hsub t ht hne
      rw [Finset.sum_insert hp₀] at hne ⊢
      set u := ∑ p ∈ s, t p • p with hu
      have hp₀C : p₀ ∈ C := hsub (Finset.mem_insert_self p₀ s)
      have hsubs : ↑s ⊆ C := fun q hq => hsub (Finset.mem_insert_of_mem hq)
      have hts : ∀ p ∈ s, 0 ≤ t p := fun p hp => ht p (Finset.mem_insert_of_mem hp)
      have hw0 : 0 ≤ t p₀ := ht p₀ (Finset.mem_insert_self p₀ s)
      by_cases hu0 : u = 0
      · rw [hu0, add_zero] at hne ⊢
        have hwpos : 0 < t p₀ :=
          hw0.lt_of_ne fun h => hne (by rw [← h, zero_smul])
        have hp₀1 : ‖p₀‖ = 1 := norm_eq_one_of_mem_sphere (hC.1 hp₀C)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hwpos, hp₀1, mul_one, smul_smul,
          inv_mul_cancel₀ (ne_of_gt hwpos), one_smul]
        exact hp₀C
      · have hunorm : ‖u‖⁻¹ • u ∈ C := IH hsubs t hts hu0
        have hunpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have huval : ‖u‖ • (‖u‖⁻¹ • u) = u := by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hunpos), one_smul]
        by_cases hwz : t p₀ = 0
        · rw [hwz, zero_smul, zero_add] at hne ⊢; exact hunorm
        · have hwpos : 0 < t p₀ := hw0.lt_of_ne (Ne.symm hwz)
          have hmem := hC.2 p₀ hp₀C (‖u‖⁻¹ • u) hunorm (t p₀) ‖u‖ hwpos hunpos
          rwa [huval] at hmem

/-- **The geodesic hull is the smallest geodesically convex set containing `s`.** If `C` is
geodesically convex and contains every point of `s`, then `geodesicHull s ⊆ C`. This is the universal
property that justifies calling `geodesicHull` a hull. -/
theorem geodesicHull_subset_of_geodesicConvex {s : Finset (Eucl d)} {C : Set (Eucl d)}
    (hC : GeodesicConvex C) (hsC : ↑s ⊆ C) : geodesicHull s ⊆ C := by
  rintro x ⟨hxnorm, t, ht, hxt⟩
  have hxne : x ≠ 0 := by rw [← norm_ne_zero_iff, hxnorm]; norm_num
  have hx0 : (∑ p ∈ s, t p • p) ≠ 0 := hxt ▸ hxne
  have hmem := normalize_conical_mem hC s hsC t ht hx0
  rwa [← hxt, hxnorm, inv_one, one_smul] at hmem

end MeasureToMeasure.Leaves
