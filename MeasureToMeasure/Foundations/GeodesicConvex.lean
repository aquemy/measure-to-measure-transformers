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
* `geodesicConvex_inner_cap` -- a strict spherical cap `{x ∈ 𝕊 | c < ⟪α, x⟫}` at a level `c ≥ 0` is
  geodesically convex, with the polarization bridges `inner_cap_of_mem_ball` / `dist_le_of_inner_cap`
  between Euclidean `r`-balls and caps at level `1 - r²/2`, and the cap-disjointness criterion
  `not_mem_inner_caps_of_separated` for `2r`-separated unit directions (the Section 3.3 containers).
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

/-- **A strict spherical cap is geodesically convex.** For a direction `α` and a level `c ≥ 0`, the
set of sphere points with `c < ⟪α, x⟫` is closed under normalized positive chords: the chord
`v = a • x + b • y` has `⟪α, v⟫ > (a + b) c ≥ 0` (so `v ≠ 0`), and since `‖v‖ ≤ a + b` the
normalization keeps the level, `⟪α, ‖v‖⁻¹ • v⟫ > c`. The open hemisphere is the case `c = 0`; for
`c = cos r` with `0 < r ≤ π/2` this is the open geodesic cap of radius `r`. This is the Section 3.3
container: hulls of shrunk clusters live in such caps. -/
theorem geodesicConvex_inner_cap (α : Eucl d) {c : ℝ} (hc : 0 ≤ c) :
    GeodesicConvex {x : Eucl d | x ∈ sphere d ∧ c < ⟪α, x⟫} := by
  refine ⟨fun x hx => hx.1, ?_⟩
  rintro x ⟨hxs, hx⟩ y ⟨hys, hy⟩ a b ha hb
  set v := a • x + b • y with hv
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hxs
  have hyn : ‖y‖ = 1 := norm_eq_one_of_mem_sphere hys
  -- The chord clears the level before normalization.
  have hev : (a + b) * c < ⟪α, v⟫ := by
    rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, add_mul]
    exact add_lt_add (by nlinarith) (by nlinarith)
  have hev0 : 0 < ⟪α, v⟫ := lt_of_le_of_lt (by positivity) hev
  have hvne : v ≠ 0 := fun h => by simp [h] at hev0
  have hvnorm : ‖v‖ ≤ a + b := by
    calc ‖v‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a + b := by
          rw [norm_smul, norm_smul, hxn, hyn, mul_one, mul_one, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  refine ⟨normalize_mem_sphere hvne, ?_⟩
  -- `⟪α, ‖v‖⁻¹ • v⟫ = ‖v‖⁻¹ ⟪α, v⟫ > ‖v‖⁻¹ (a+b) c ≥ c`.
  rw [real_inner_smul_right]
  have h1 : ‖v‖⁻¹ * ((a + b) * c) < ‖v‖⁻¹ * ⟪α, v⟫ :=
    mul_lt_mul_of_pos_left hev (inv_pos.mpr hvpos)
  have h2 : c ≤ ‖v‖⁻¹ * ((a + b) * c) := by
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · simp [← hc0]
    · have hinv : (a + b)⁻¹ ≤ ‖v‖⁻¹ := by
        gcongr
      calc c = (a + b)⁻¹ * ((a + b) * c) := by
              field_simp
        _ ≤ ‖v‖⁻¹ * ((a + b) * c) := by
              apply mul_le_mul_of_nonneg_right hinv (by positivity)
  linarith

/-- **Ball-to-cap (polarization).** A sphere point within Euclidean distance `r` of a unit vector
`α` lies in the strict inner cap at level `1 - r²/2`: from `‖x - α‖² = 2 - 2⟪α, x⟫`. This converts
the `Metric.ball` carriers of the disentanglement output into the caps that geodesic convexity
speaks about. -/
theorem inner_cap_of_mem_ball {α x : Eucl d} (hα : ‖α‖ = 1) (hx : x ∈ sphere d)
    {r : ℝ} (hxr : dist x α < r) : 1 - r ^ 2 / 2 < ⟪α, x⟫ := by
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hpol : ‖x - α‖ ^ 2 = 2 - 2 * ⟪α, x⟫ := by
    rw [norm_sub_sq_real, hxn, hα, real_inner_comm]
    ring
  have hd0 : (0 : ℝ) ≤ dist x α := dist_nonneg
  have hsq : dist x α ^ 2 < r ^ 2 := by
    have hr0 : 0 < r := lt_of_le_of_lt hd0 hxr
    nlinarith
  rw [dist_eq_norm, hpol] at hsq
  linarith

/-- **Cap-to-ball (polarization, reverse direction).** A sphere point in the closed inner cap at
level `1 - r²/2` (for `r > 0`) is within Euclidean distance `r` of `α`. -/
theorem dist_le_of_inner_cap {α x : Eucl d} (hα : ‖α‖ = 1) (hx : x ∈ sphere d)
    {r : ℝ} (hr : 0 < r) (hc : 1 - r ^ 2 / 2 ≤ ⟪α, x⟫) : dist x α ≤ r := by
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hpol : ‖x - α‖ ^ 2 = 2 - 2 * ⟪α, x⟫ := by
    rw [norm_sub_sq_real, hxn, hα, real_inner_comm]
    ring
  have hsq : ‖x - α‖ ^ 2 ≤ r ^ 2 := by rw [hpol]; linarith
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - α)]

/-- **Cap disjointness from `2r`-separation.** No sphere point lies in both closed inner caps at
level `1 - r²/2` around unit directions at distance `≥ 2r` apart, unless it witnesses equality
throughout; with one strict cap membership the triangle inequality is strict and the point cannot
exist. Stated with one strict and one non-strict side so both the hull version (all strict) and
the barycenter version (strict via the a.e. argument) can consume it. -/
theorem not_mem_inner_caps_of_separated {α₁ α₂ : Eucl d} (hα₁ : ‖α₁‖ = 1) (hα₂ : ‖α₂‖ = 1)
    {r : ℝ} (hr : 0 < r) (hsep : 2 * r ≤ dist α₁ α₂) {x : Eucl d} (hx : x ∈ sphere d)
    (h₁ : 1 - r ^ 2 / 2 < ⟪α₁, x⟫) (h₂ : 1 - r ^ 2 / 2 ≤ ⟪α₂, x⟫) : False := by
  have hd₁ : dist x α₁ ≤ r := dist_le_of_inner_cap hα₁ hx hr h₁.le
  have hd₂ : dist x α₂ ≤ r := dist_le_of_inner_cap hα₂ hx hr h₂
  -- Strictness on the first side: `⟪α₁,x⟫ > 1 - r²/2` gives `dist x α₁ < r` strictly.
  have hd₁' : dist x α₁ < r := by
    have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
    have hpol : ‖x - α₁‖ ^ 2 = 2 - 2 * ⟪α₁, x⟫ := by
      rw [norm_sub_sq_real, hxn, hα₁, real_inner_comm]; ring
    have hsq : ‖x - α₁‖ ^ 2 < r ^ 2 := by rw [hpol]; linarith
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x - α₁)]
  have : dist α₁ α₂ < 2 * r := by
    calc dist α₁ α₂ ≤ dist α₁ x + dist x α₂ := dist_triangle _ _ _
      _ = dist x α₁ + dist x α₂ := by rw [dist_comm α₁ x]
      _ < r + r := by linarith
      _ = 2 * r := by ring
  linarith

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
