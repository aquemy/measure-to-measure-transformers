import MeasureToMeasure.Leaves.GeodesicHullConvex
import MeasureToMeasure.Statements.SupportedIn

/-!
# Set-based geodesic hull (`geodesicHullSet`)

`BarycenterNonColinear.lean` models the geodesic-convex hull `conv_g` of a *finite* set
`s : Finset (Eucl d)` as `geodesicHull s = cone(s) ∩ 𝕊^{d-1}`. The confined-bystanders gate for
`lemma_3_3` (paper Lemma 3.3, arXiv:2411.04551) needs the same hull for a general *set* of
generators — the supports of the acted measures are closed subsets of the sphere, not finsets.
This file provides the `Set`-based hull: a unit vector belongs to `geodesicHullSet s` when it is a
nonnegative conical combination of *finitely many* points of `s` (the finite-conical-combination
form validated by the campaign probe).

Basic vocabulary, all kernel-checked:

* `geodesicHull_subset_geodesicHullSet` — the `Finset` hull embeds whenever its generators lie in
  `s`, and `geodesicHullSet_coe` — on a finset coerced to a set the two hulls agree exactly.
* `mem_geodesicHullSet_self` — every unit generator lies in its own hull. This is the
  exclusion driver behind the gate: a support point of an acted measure is *inside* the hull, so a
  bystander confined away from the hull cannot sit on it (the F28 counterexample's collision).
* `geodesicHullSet_mono` — monotone in the generating set.
* `geodesicHullSet_subset_sphere` / `geodesicHullSet_subset_orthant` — the hull stays on the
  sphere, and inside the open orthant when its generators do (coordinatewise positivity survives
  nonzero conical combination).
* `normalize_smul_add_smul_mem_geodesicHullSet` — normalized positive chords of hull points stay
  in the hull, and the two packaged forms `geodesicConvex_geodesicHullSet_of_orthant` /
  `geodesicConvex_geodesicHullSet_of_hemisphere` — the hull is `GeodesicConvex` when the
  generators lie in the open orthant (resp. an open hemisphere `0 < ⟪e, ·⟫`). Within that
  hemisphere normalized chords are exactly the geodesic arcs, so this is the "corridors can thread
  inside the hull" fact the corridor construction consumes.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace
open MeasureToMeasure MeasureToMeasure.Statements

variable {d : ℕ}

/-- The geodesic-convex hull of a general set `s ⊆ ℝ^d`, modeled within a hemisphere as
`cone(s) ∩ 𝕊^{d-1}`: the unit vectors that are nonnegative conical combinations of finitely many
points of `s`. Mirrors the `Finset`-based `geodesicHull`; the two agree on finsets
(`geodesicHullSet_coe`). -/
def geodesicHullSet (s : Set (Eucl d)) : Set (Eucl d) :=
  {x | ‖x‖ = 1 ∧ ∃ t : Finset (Eucl d), ↑t ⊆ s ∧ inConicalSpan t x}

/-- The `Finset`-based hull embeds into the `Set`-based hull of any carrier of its generators. -/
theorem geodesicHull_subset_geodesicHullSet {s : Set (Eucl d)} {t : Finset (Eucl d)}
    (h : ↑t ⊆ s) : geodesicHull t ⊆ geodesicHullSet s :=
  fun _x hx => ⟨hx.1, t, h, hx.2⟩

/-- **Self-membership**: every unit-norm generator lies in its own geodesic hull. Sphere-support
points of an acted measure are therefore inside the hull — the exclusion driver for the
confined-bystanders gate. -/
theorem mem_geodesicHullSet_self {s : Set (Eucl d)} {p : Eucl d} (hp : p ∈ s) (hp1 : ‖p‖ = 1) :
    p ∈ geodesicHullSet s :=
  geodesicHull_subset_geodesicHullSet (by simpa using hp)
    (mem_geodesicHull_self (Finset.mem_singleton_self p)
      (by rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hp1))

/-- The `Set`-based hull is monotone in its generating set. -/
theorem geodesicHullSet_mono {s s' : Set (Eucl d)} (h : s ⊆ s') :
    geodesicHullSet s ⊆ geodesicHullSet s' := by
  rintro x ⟨hx1, t, hts, hct⟩
  exact ⟨hx1, t, hts.trans h, hct⟩

/-- On a coerced finset the `Set`-based hull agrees exactly with the `Finset`-based one. -/
theorem geodesicHullSet_coe (t : Finset (Eucl d)) :
    geodesicHullSet (↑t : Set (Eucl d)) = geodesicHull t := by
  ext x
  constructor
  · rintro ⟨hx1, u, hut, hcu⟩
    exact ⟨hx1, hcu.mono (Finset.coe_subset.mp hut)⟩
  · rintro ⟨hx1, hc⟩
    exact ⟨hx1, t, subset_rfl, hc⟩

/-- The `Set`-based hull lies on the unit sphere. -/
theorem geodesicHullSet_subset_sphere {s : Set (Eucl d)} :
    geodesicHullSet s ⊆ sphere d := fun _x hx => by
  rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hx.1

/-- Generators in the open orthant keep the whole hull in the open orthant: every coordinate of a
nonzero conical combination of coordinatewise-positive points is positive (via the inner product
against the corresponding standard basis vector). -/
theorem geodesicHullSet_subset_orthant {s : Set (Eucl d)} (hs : s ⊆ orthant d) :
    geodesicHullSet s ⊆ orthant d := by
  rintro x ⟨hx1, t, hts, hct⟩
  have hxne : x ≠ 0 := by rw [← norm_ne_zero_iff, hx1]; norm_num
  intro i
  have he : ∀ p ∈ t, 0 < ⟪EuclideanSpace.single i (1 : ℝ), p⟫ := by
    intro p hp
    have hpo := hs (hts hp) i
    rwa [EuclideanSpace.inner_single_left, starRingEnd_apply, star_one, one_mul]
  have hpos := inner_pos_of_inConicalSpan he hct hxne
  rwa [EuclideanSpace.inner_single_left, starRingEnd_apply, star_one, one_mul] at hpos

/-- Normalized nonnegative chords of hull points stay in the hull: the chord is a conical
combination over the union of the two witnessing finsets. -/
theorem normalize_smul_add_smul_mem_geodesicHullSet {s : Set (Eucl d)} {x y : Eucl d}
    (hx : x ∈ geodesicHullSet s) (hy : y ∈ geodesicHullSet s) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a • x + b • y ≠ 0) :
    ‖a • x + b • y‖⁻¹ • (a • x + b • y) ∈ geodesicHullSet s := by
  obtain ⟨_hx1, t₁, ht₁, hc₁⟩ := hx
  obtain ⟨_hy1, t₂, ht₂, hc₂⟩ := hy
  have hcomb : inConicalSpan (t₁ ∪ t₂) (a • x + b • y) :=
    ((hc₁.mono Finset.subset_union_left).smul ha).add
      ((hc₂.mono Finset.subset_union_right).smul hb)
  exact geodesicHull_subset_geodesicHullSet
    (by rw [Finset.coe_union]; exact Set.union_subset ht₁ ht₂)
    (mem_geodesicHull_normalize hcomb hne)

/-- **The `Set`-based hull of orthant generators is geodesically convex.** Both endpoints of a
positive chord lie in the open orthant (`geodesicHullSet_subset_orthant`), so the chord has a
strictly positive coordinate and cannot vanish; its normalization stays in the hull. Geodesic arcs
between hull points therefore stay inside the hull — corridors can thread within it. -/
theorem geodesicConvex_geodesicHullSet_of_orthant {s : Set (Eucl d)} (hs : s ⊆ orthant d) :
    GeodesicConvex (geodesicHullSet s) := by
  refine ⟨geodesicHullSet_subset_sphere, ?_⟩
  intro x hx y hy a b ha hb
  have hxo : x ∈ orthant d := geodesicHullSet_subset_orthant hs hx
  have hyo : y ∈ orthant d := geodesicHullSet_subset_orthant hs hy
  have hxne : x ≠ 0 := by rw [← norm_ne_zero_iff, hx.1]; norm_num
  have hne : a • x + b • y ≠ 0 := by
    intro h0
    obtain ⟨i, _hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hno
      exact hxne (by ext i; simpa using not_not.mp (not_exists.mp hno i))
    have hcoord : (a • x + b • y) i = 0 := by rw [h0]; rfl
    have hlt : 0 < a * x i + b * y i := by
      have hbb : 0 ≤ b * y i := mul_nonneg hb.le (hyo i).le
      nlinarith [mul_pos ha (hxo i)]
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul] at hcoord
    linarith
  exact normalize_smul_add_smul_mem_geodesicHullSet hx hy ha.le hb.le hne

/-- **The `Set`-based hull of hemispherical generators is geodesically convex.** The `Set`-based
sibling of `geodesicConvex_geodesicHull`: when every generator satisfies `0 < ⟪e, p⟫`, positive
chords keep `⟪e, ·⟫` strictly positive, hence cannot vanish, and normalize back into the hull. -/
theorem geodesicConvex_geodesicHullSet_of_hemisphere {s : Set (Eucl d)} {e : Eucl d}
    (hs : ∀ p ∈ s, 0 < ⟪e, p⟫) : GeodesicConvex (geodesicHullSet s) := by
  refine ⟨geodesicHullSet_subset_sphere, ?_⟩
  intro x hx y hy a b ha hb
  obtain ⟨hx1, t₁, ht₁, hc₁⟩ := hx
  obtain ⟨hy1, t₂, ht₂, hc₂⟩ := hy
  have hxne : x ≠ 0 := by rw [← norm_ne_zero_iff, hx1]; norm_num
  have hyne : y ≠ 0 := by rw [← norm_ne_zero_iff, hy1]; norm_num
  have hex : 0 < ⟪e, x⟫ := inner_pos_of_inConicalSpan (fun p hp => hs p (ht₁ hp)) hc₁ hxne
  have hey : 0 < ⟪e, y⟫ := inner_pos_of_inConicalSpan (fun p hp => hs p (ht₂ hp)) hc₂ hyne
  have hev : 0 < ⟪e, a • x + b • y⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact add_pos (mul_pos ha hex) (mul_pos hb hey)
  have hne : a • x + b • y ≠ 0 := fun h => by simp [h] at hev
  exact normalize_smul_add_smul_mem_geodesicHullSet ⟨hx1, t₁, ht₁, hc₁⟩ ⟨hy1, t₂, ht₂, hc₂⟩
    ha.le hb.le hne

end MeasureToMeasure.Leaves
