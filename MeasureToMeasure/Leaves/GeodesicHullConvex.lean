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
here as well. The final section machine-checks the **Section 3.3 separation transfer** (milestone M5,
complete): clusters shrunk into `r`-balls around `2r`-separated unit directions have disjoint geodesic
hulls (`geodesicHull_disjoint_of_separated_balls`) and non-colinear barycenters
(`barycenter_not_sameRay_of_separated_balls`). Everything is kernel-checked.
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

/-!
## A separating-hyperplane criterion for hull disjointness

The disentanglement of Section 3.3 needs two clusters' geodesic hulls to be *disjoint*. A clean
sufficient condition: a single direction `e` that is strictly positive on one generating set and
strictly negative on the other separates the two hulls (they live in opposite open half-spaces of the
hyperplane `⟪e, ·⟫ = 0`). This feeds leaf L11 (`barycenter_noncolinear_of_disjoint_hull`).
-/

/-- Mirror of `inner_pos_of_inConicalSpan`: a nonzero conical point built from generators all strictly
on the *negative* side of `e` has `⟪e, ·⟫ < 0`. -/
theorem inner_neg_of_inConicalSpan {s : Finset (Eucl d)} {e x : Eucl d}
    (hs : ∀ p ∈ s, ⟪e, p⟫ < 0) (hx : inConicalSpan s x) (hx0 : x ≠ 0) : ⟪e, x⟫ < 0 := by
  have h := inner_pos_of_inConicalSpan (e := -e)
    (fun p hp => by rw [inner_neg_left]; exact neg_pos.mpr (hs p hp)) hx hx0
  rwa [inner_neg_left, neg_pos] at h

/-- **Separating-hyperplane criterion for hull disjointness.** If a direction `e` is strictly positive
on every generator of `s₁` and strictly negative on every generator of `s₂`, then the geodesic hulls of
`s₁` and `s₂` are disjoint: any common point would have `⟪e, ·⟫` both positive and negative. -/
theorem geodesicHull_disjoint_of_separated {s₁ s₂ : Finset (Eucl d)} {e : Eucl d}
    (h₁ : ∀ p ∈ s₁, 0 < ⟪e, p⟫) (h₂ : ∀ q ∈ s₂, ⟪e, q⟫ < 0) :
    Disjoint (geodesicHull s₁) (geodesicHull s₂) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hxne : x ≠ 0 := by rw [← norm_ne_zero_iff, hx₁.1]; norm_num
  exact absurd (inner_pos_of_inConicalSpan h₁ hx₁.2 hxne)
    (not_lt.mpr (inner_neg_of_inConicalSpan h₂ hx₂.2 hxne).le)

/-- **Corollary (feeds L11).** Two finite point sets separated by a hyperplane through the origin have
non-colinear empirical barycenters (with nonnegative weights and nonzero sums). -/
theorem barycenter_noncolinear_of_separated {s₁ s₂ : Finset (Eucl d)} {e : Eucl d}
    {w₁ w₂ : Eucl d → ℝ} (hw₁ : ∀ p ∈ s₁, 0 ≤ w₁ p) (hw₂ : ∀ p ∈ s₂, 0 ≤ w₂ p)
    (hb0 : (∑ p ∈ s₁, w₁ p • p) ≠ 0) (hc0 : (∑ p ∈ s₂, w₂ p • p) ≠ 0)
    (h₁ : ∀ p ∈ s₁, 0 < ⟪e, p⟫) (h₂ : ∀ q ∈ s₂, ⟪e, q⟫ < 0) :
    ¬ SameRay ℝ (∑ p ∈ s₁, w₁ p • p) (∑ p ∈ s₂, w₂ p • p) :=
  barycenter_noncolinear_of_disjoint_hull hw₁ hw₂ hb0 hc0
    (geodesicHull_disjoint_of_separated h₁ h₂)

/-!
## The Section 3.3 separation transfer (milestone M5, disentanglement geometry)

The paper's Section 3.3 induction shrinks each cluster into a small ball around a unit direction
(Lemma 3.3) and makes the directions pairwise separated (Lemma 3.4); it then uses, without proof,
that this yields pairwise-disjoint geodesic hulls and non-colinear barycenters ("choosing `ε` small
enough [...] the diameter of the convex hull is shrunk until achieving the separation", p. 17).
This section machine-checks that geometry: hull containment in strict spherical caps
(`geodesicHull_subset_inner_cap`), quantitative barycenter location for ball-supported measures
(`inner_barycenter_gt`, `norm_barycenter_le_one`), and the two headline transfers -
`geodesicHull_disjoint_of_separated_balls` (hull form) and
`barycenter_not_sameRay_of_separated_balls` (measure form). All kernel-clean.
-/

section SeparationTransfer

open MeasureTheory

/-- Hull-in-cap: if every generator lies in the strict inner cap `{x ∈ 𝕊 | c < ⟪α, x⟫}` (`c ≥ 0`),
so does the whole geodesic hull - the cap is geodesically convex and the hull is minimal. -/
theorem geodesicHull_subset_inner_cap {s : Finset (Eucl d)} {α : Eucl d} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ p ∈ s, p ∈ sphere d ∧ c < ⟪α, p⟫) :
    geodesicHull s ⊆ {x : Eucl d | x ∈ sphere d ∧ c < ⟪α, x⟫} :=
  geodesicHull_subset_of_geodesicConvex (geodesicConvex_inner_cap α hc) (fun p hp => hs p hp)

/-- **Separated small balls give disjoint geodesic hulls.** Two finite sets of sphere points inside
Euclidean balls of radius `r` around unit directions `2r` apart have disjoint geodesic hulls: each
hull lives in the strict inner cap at level `1 - r²/2`, and those caps share no sphere point. This
is the hull half of the Section 3.3 separation transfer. -/
theorem geodesicHull_disjoint_of_separated_balls {s₁ s₂ : Finset (Eucl d)} {α₁ α₂ : Eucl d}
    (hα₁ : ‖α₁‖ = 1) (hα₂ : ‖α₂‖ = 1) {r : ℝ} (hr : 0 < r) (hsep : 2 * r ≤ dist α₁ α₂)
    (hs₁ : ∀ p ∈ s₁, p ∈ sphere d ∧ dist p α₁ < r)
    (hs₂ : ∀ p ∈ s₂, p ∈ sphere d ∧ dist p α₂ < r) :
    Disjoint (geodesicHull s₁) (geodesicHull s₂) := by
  -- The level `c = 1 - r²/2` is nonnegative because `2r ≤ dist α₁ α₂ ≤ 2` forces `r ≤ 1`.
  have hd2 : dist α₁ α₂ ≤ 2 := by
    rw [dist_eq_norm]
    calc ‖α₁ - α₂‖ ≤ ‖α₁‖ + ‖α₂‖ := norm_sub_le _ _
      _ = 2 := by rw [hα₁, hα₂]; norm_num
  have hr1 : r ≤ 1 := by linarith
  have hc : (0 : ℝ) ≤ 1 - r ^ 2 / 2 := by nlinarith
  have hsub₁ := geodesicHull_subset_inner_cap hc
    (fun p hp => ⟨(hs₁ p hp).1, inner_cap_of_mem_ball hα₁ (hs₁ p hp).1 (hs₁ p hp).2⟩)
  have hsub₂ := geodesicHull_subset_inner_cap hc
    (fun p hp => ⟨(hs₂ p hp).1, inner_cap_of_mem_ball hα₂ (hs₂ p hp).1 (hs₂ p hp).2⟩)
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact not_mem_inner_caps_of_separated hα₁ hα₂ hr hsep (hsub₁ hx₁).1
    (hsub₁ hx₁).2 (hsub₂ hx₂).2.le

/-- A sphere-supported measure has an integrable identity map: the norm is a.e. `1 ≤ 1`. -/
theorem integrable_id_of_sphere_support {μ : Measure (Eucl d)} [IsProbabilityMeasure μ]
    (hs : μ (sphere d)ᶜ = 0) : Integrable (fun x : Eucl d => x) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) aestronglyMeasurable_id ?_
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hs
  simp only [Set.mem_setOf_eq, not_le] at hx
  simp only [sphere, Set.mem_compl_iff, Metric.mem_sphere, dist_zero_right]
  intro h1; rw [h1] at hx; linarith

/-- Barycenter level bound, non-strict form: full mass in the closed cap `{c ≤ ⟪α, ·⟫}` puts the
barycenter's `⟪α, ·⟫` at least at `c`. -/
theorem inner_barycenter_ge {μ : Measure (Eucl d)} [IsProbabilityMeasure μ] {α : Eucl d} {c : ℝ}
    (hint : Integrable (fun x : Eucl d => x) μ)
    (hsupp : μ {x : Eucl d | c ≤ ⟪α, x⟫}ᶜ = 0) : c ≤ ⟪α, barycenter μ⟫ := by
  have hae : ∀ᵐ x ∂μ, c ≤ ⟪α, x⟫ := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => by simpa using hx) hsupp
  have hii : Integrable (fun x : Eucl d => ⟪α, x⟫) μ := by
    simpa using (innerSL ℝ α).integrable_comp hint
  have hib : ∫ x, ⟪α, x⟫ ∂μ = ⟪α, barycenter μ⟫ := by
    simpa [barycenter] using (innerSL ℝ α).integral_comp_comm hint
  calc c = ∫ _, c ∂μ := by simp
    _ ≤ ∫ x, ⟪α, x⟫ ∂μ := integral_mono_ae (integrable_const c) hii hae
    _ = ⟪α, barycenter μ⟫ := hib

/-- Barycenter level bound, strict form: full mass in the *strict* cap `{c < ⟪α, ·⟫}` puts the
barycenter strictly above the level. If equality held, the nonnegative integrand
`⟪α, x⟫ - c` would have zero integral, hence vanish a.e., contradicting a.e. strictness on a
probability measure. -/
theorem inner_barycenter_gt {μ : Measure (Eucl d)} [IsProbabilityMeasure μ] {α : Eucl d} {c : ℝ}
    (hint : Integrable (fun x : Eucl d => x) μ)
    (hsupp : μ {x : Eucl d | c < ⟪α, x⟫}ᶜ = 0) : c < ⟪α, barycenter μ⟫ := by
  have haestrict : ∀ᵐ x ∂μ, c < ⟪α, x⟫ := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => by simpa using hx) hsupp
  have hge : c ≤ ⟪α, barycenter μ⟫ := by
    have hsub : {x : Eucl d | c ≤ ⟪α, x⟫}ᶜ ⊆ {x : Eucl d | c < ⟪α, x⟫}ᶜ :=
      Set.compl_subset_compl.mpr fun x hx => Set.mem_setOf.mpr (le_of_lt (Set.mem_setOf.mp hx))
    exact inner_barycenter_ge hint (measure_mono_null hsub hsupp)
  rcases eq_or_lt_of_le hge with heq | h
  · exfalso
    have hii : Integrable (fun x : Eucl d => ⟪α, x⟫) μ := by
      simpa using (innerSL ℝ α).integrable_comp hint
    have hib : ∫ x, ⟪α, x⟫ ∂μ = ⟪α, barycenter μ⟫ := by
      simpa [barycenter] using (innerSL ℝ α).integral_comp_comm hint
    have hzero : ∫ x, (⟪α, x⟫ - c) ∂μ = 0 := by
      rw [integral_sub hii (integrable_const c), hib, integral_const]
      simp [← heq]
    have hnn : 0 ≤ᵐ[μ] fun x : Eucl d => ⟪α, x⟫ - c :=
      haestrict.mono fun x hx => by simp only [Pi.zero_apply]; linarith
    have hvanish : (fun x : Eucl d => ⟪α, x⟫ - c) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn (hii.sub (integrable_const c))).mp hzero
    have hfalse : ∀ᵐ _x ∂μ, False := by
      filter_upwards [haestrict, hvanish] with x hx hv
      simp only [Pi.zero_apply] at hv
      linarith
    exact (IsProbabilityMeasure.ne_zero μ)
      (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse))
  · exact h

/-- A sphere-supported probability measure has barycenter of norm at most `1`. -/
theorem norm_barycenter_le_one {μ : Measure (Eucl d)} [IsProbabilityMeasure μ]
    (hs : μ (sphere d)ᶜ = 0) (hint : Integrable (fun x : Eucl d => x) μ) :
    ‖barycenter μ‖ ≤ 1 := by
  have hae : ∀ᵐ x ∂μ, ‖x‖ ≤ 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hs
    simp only [Set.mem_setOf_eq, not_le] at hx
    simp only [sphere, Set.mem_compl_iff, Metric.mem_sphere, dist_zero_right]
    intro h1; rw [h1] at hx; linarith
  calc ‖barycenter μ‖ ≤ ∫ x, ‖x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _, (1 : ℝ) ∂μ := integral_mono_ae hint.norm (integrable_const 1) hae
    _ = 1 := by simp

/-- **Separated small balls give non-colinear barycenters (measure form).** Two sphere-supported
probability measures carried by Euclidean balls of radius `r` around unit directions `2r` apart
have non-`SameRay` barycenters: each normalized barycenter is a sphere point strictly inside its
cap at level `1 - r²/2` (strict via `inner_barycenter_gt`, and normalization only increases the
level since `‖barycenter‖ ≤ 1`), and a common normalization would lie in both caps. This is the
measure half of the Section 3.3 separation transfer, the quantitative form of "shrink until the
barycenter directions separate". -/
theorem barycenter_not_sameRay_of_separated_balls {μ ν : Measure (Eucl d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {α₁ α₂ : Eucl d}
    (hα₁ : ‖α₁‖ = 1) (hα₂ : ‖α₂‖ = 1) {r : ℝ} (hr : 0 < r) (hsep : 2 * r ≤ dist α₁ α₂)
    (hμs : μ (sphere d)ᶜ = 0) (hνs : ν (sphere d)ᶜ = 0)
    (hμb : μ (Metric.ball α₁ r)ᶜ = 0) (hνb : ν (Metric.ball α₂ r)ᶜ = 0) :
    ¬ SameRay ℝ (barycenter μ) (barycenter ν) := by
  intro hray
  set c : ℝ := 1 - r ^ 2 / 2 with hcdef
  have hd2 : dist α₁ α₂ ≤ 2 := by
    rw [dist_eq_norm]
    calc ‖α₁ - α₂‖ ≤ ‖α₁‖ + ‖α₂‖ := norm_sub_le _ _
      _ = 2 := by rw [hα₁, hα₂]; norm_num
  have hr1 : r ≤ 1 := by linarith
  have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; nlinarith
  have hμint := integrable_id_of_sphere_support hμs
  have hνint := integrable_id_of_sphere_support hνs
  -- Full mass of each measure in its strict cap.
  have hμcap : μ {x : Eucl d | c < ⟪α₁, x⟫}ᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hμs hμb)
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hx
    by_contra hmem
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hmem
    exact absurd (inner_cap_of_mem_ball hα₁ hmem.1 (Metric.mem_ball.mp hmem.2)) (not_lt.mpr hx)
  have hνcap : ν {x : Eucl d | c < ⟪α₂, x⟫}ᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hνs hνb)
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hx
    by_contra hmem
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hmem
    exact absurd (inner_cap_of_mem_ball hα₂ hmem.1 (Metric.mem_ball.mp hmem.2)) (not_lt.mpr hx)
  -- Strict barycenter levels; in particular both barycenters are nonzero.
  have hbμ : c < ⟪α₁, barycenter μ⟫ := inner_barycenter_gt hμint hμcap
  have hbν : c < ⟪α₂, barycenter ν⟫ := inner_barycenter_gt hνint hνcap
  have hbμpos : 0 < ⟪α₁, barycenter μ⟫ := lt_of_le_of_lt hc0 hbμ
  have hbνpos : 0 < ⟪α₂, barycenter ν⟫ := lt_of_le_of_lt hc0 hbν
  have hbμ0 : barycenter μ ≠ 0 := fun h => by simp [h] at hbμpos
  have hbν0 : barycenter ν ≠ 0 := fun h => by simp [h] at hbνpos
  -- SameRay nonzero vectors share their normalization.
  have hnorm : ‖barycenter μ‖ • barycenter ν = ‖barycenter ν‖ • barycenter μ :=
    hray.norm_smul_eq
  set u : Eucl d := ‖barycenter μ‖⁻¹ • barycenter μ with hudef
  have hbμn : 0 < ‖barycenter μ‖ := norm_pos_iff.mpr hbμ0
  have hbνn : 0 < ‖barycenter ν‖ := norm_pos_iff.mpr hbν0
  have huv : u = ‖barycenter ν‖⁻¹ • barycenter ν := by
    have h2 := congrArg
      (fun w : Eucl d => (‖barycenter μ‖⁻¹ * ‖barycenter ν‖⁻¹) • w) hnorm
    simp only [smul_smul] at h2
    have e1 : ‖barycenter μ‖⁻¹ * ‖barycenter ν‖⁻¹ * ‖barycenter μ‖ = ‖barycenter ν‖⁻¹ := by
      field_simp
    have e2 : ‖barycenter μ‖⁻¹ * ‖barycenter ν‖⁻¹ * ‖barycenter ν‖ = ‖barycenter μ‖⁻¹ := by
      field_simp
    rw [e1, e2] at h2
    rw [hudef]
    exact h2.symm
  have husphere : u ∈ sphere d := normalize_mem_sphere hbμ0
  -- The common normalization clears both levels: `‖b‖ ≤ 1` so dividing only increases `⟪α, ·⟫`.
  have hle1μ : ‖barycenter μ‖ ≤ 1 := norm_barycenter_le_one hμs hμint
  have hle1ν : ‖barycenter ν‖ ≤ 1 := norm_barycenter_le_one hνs hνint
  have hu₁ : c < ⟪α₁, u⟫ := by
    rw [hudef, real_inner_smul_right]
    have hinv : (1 : ℝ) ≤ ‖barycenter μ‖⁻¹ := (one_le_inv₀ hbμn).mpr hle1μ
    nlinarith [mul_le_mul_of_nonneg_right hinv hbμpos.le]
  have hu₂ : c < ⟪α₂, u⟫ := by
    rw [huv, real_inner_smul_right]
    have hinv : (1 : ℝ) ≤ ‖barycenter ν‖⁻¹ := (one_le_inv₀ hbνn).mpr hle1ν
    nlinarith [mul_le_mul_of_nonneg_right hinv hbνpos.le]
  exact not_mem_inner_caps_of_separated hα₁ hα₂ hr hsep husphere hu₁ hu₂.le

end SeparationTransfer

end MeasureToMeasure.Leaves
