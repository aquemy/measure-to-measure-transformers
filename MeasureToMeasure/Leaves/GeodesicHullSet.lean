import MeasureToMeasure.Leaves.GeodesicHullConvex
import MeasureToMeasure.Statements.SupportedIn
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Thickening

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

Clearance and target membership (leaf `geodesicHullSet_clearance_and_target`):

* `isCompact_closure_geodesicHullSet` / `geodesicHullSet_clearance` — the closure of the hull is
  compact (closed subset of the sphere), so a closed set disjoint from that closure keeps a uniform
  positive margin `ε` from every hull point, and every `ε`-ball centered in the hull misses it: the
  radius margin all later cap/hop gates stay under.
* `mem_geodesicHullSet_normalize` (finitely-supported exact case),
  `exists_inConicalSpan_of_mem_convexHull` (convex-hull points are finite conical combinations),
  and `normalize_barycenter_mem_closure_geodesicHullSet` — the normalized barycenter of a
  probability measure supported in `S` lies in the **closure** of `geodesicHullSet S`. For a
  general (not finitely supported) measure the barycenter is a limit of conical combinations
  without necessarily being one, so closure membership is the honest general conclusion; the
  gate can consume it, or use the exact-membership fallback
  `mem_geodesicHullSet_union_singleton` (the target direction is in the hull once listed among
  the generators, faithful to the paper's `conv_g` of the acted pair in (3.3)).
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace
open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements

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

/-!
## Clearance and target membership

The confined-bystanders gate needs two more facts about the `Set`-based hull. **Clearance**: a
closed set disjoint from the (compact) closure of the hull keeps a uniform positive margin from
every hull point, the radius budget all later cap/hop constructions stay under. **Target
membership**: the normalized barycenter of a probability measure supported in `S` lies in the
closure of `geodesicHullSet S`; for measures that are not finitely supported the barycenter is a
limit of conical combinations without necessarily being one, so closure membership is the honest
general statement (the finitely-supported exact case is `mem_geodesicHullSet_normalize`, and
`mem_geodesicHullSet_union_singleton` provides the exact-membership fallback for a gate stated
over generators that include the target direction).
-/

/-- Finitely-supported exact target membership: the normalization of a nonzero conical
combination of points of `s` lies in the `Set`-based hull of `s`. -/
theorem mem_geodesicHullSet_normalize {s : Set (Eucl d)} {u : Finset (Eucl d)} {x : Eucl d}
    (hu : ↑u ⊆ s) (hx : inConicalSpan u x) (hx0 : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ geodesicHullSet s :=
  geodesicHull_subset_geodesicHullSet hu (mem_geodesicHull_normalize hx hx0)

/-- Every point of the convex hull of `S` is a finite conical combination of points of `S`:
unpack `convexHull_eq`'s finite convex combination and collapse repeated points fiberwise onto
the image finset. -/
theorem exists_inConicalSpan_of_mem_convexHull {S : Set (Eucl d)} {x : Eucl d}
    (hx : x ∈ convexHull ℝ S) : ∃ u : Finset (Eucl d), ↑u ⊆ S ∧ inConicalSpan u x := by
  rw [convexHull_eq] at hx
  obtain ⟨ι, u, w, z, hw0, hw1, hz, hcm⟩ := hx
  refine ⟨u.image z, ?_, ?_⟩
  · intro p hp
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact hz i hi
  · refine ⟨fun p => ∑ i ∈ u.filter (fun i => z i = p), w i,
      fun p _ => Finset.sum_nonneg fun i hi => hw0 i (Finset.mem_filter.mp hi).1, ?_⟩
    have hxsum : x = ∑ i ∈ u, w i • z i := by
      rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    rw [hxsum,
      ← Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem z hi)
        (fun i => w i • z i)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

/-- Normalization passes from the closed convex hull to the closed geodesic hull: a nonzero
limit of conical combinations normalizes into the closure of the `Set`-based hull (the
normalization map is continuous away from `0`). -/
theorem normalize_mem_closure_geodesicHullSet {S : Set (Eucl d)} {b : Eucl d}
    (hb : b ∈ closure (convexHull ℝ S)) (hb0 : b ≠ 0) :
    ‖b‖⁻¹ • b ∈ closure (geodesicHullSet S) := by
  have hb' : b ∈ closure {x : Eucl d | ∃ u : Finset (Eucl d), ↑u ⊆ S ∧ inConicalSpan u x} :=
    closure_mono (fun x hx => exists_inConicalSpan_of_mem_convexHull hx) hb
  obtain ⟨x, hxA, hxlim⟩ := mem_closure_iff_seq_limit.mp hb'
  have hnb : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb0
  have hnorm : Filter.Tendsto (fun n => ‖x n‖) Filter.atTop (nhds ‖b‖) :=
    (continuous_norm.tendsto b).comp hxlim
  have hlim : Filter.Tendsto (fun n => ‖x n‖⁻¹ • x n) Filter.atTop (nhds (‖b‖⁻¹ • b)) :=
    (hnorm.inv₀ (ne_of_gt hnb)).smul hxlim
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [hxlim.eventually_ne hb0] with n hn
  obtain ⟨u, hus, hcu⟩ := hxA n
  exact mem_geodesicHullSet_normalize hus hcu hn

/-- **Target membership.** The normalized barycenter of a probability measure supported in `S`
lies in the closure of `geodesicHullSet S`: the barycenter lies in the closed convex hull of `S`
(`Convex.integral_mem` via `barycenter_mem_of_supportedIn`), and normalization passes to the
limit. -/
theorem normalize_barycenter_mem_closure_geodesicHullSet {S : Set (Eucl d)}
    {μ : Measure (Eucl d)} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : Eucl d => x) μ) (hμS : supportedIn μ S)
    (hb0 : barycenter μ ≠ 0) :
    ‖barycenter μ‖⁻¹ • barycenter μ ∈ closure (geodesicHullSet S) := by
  refine normalize_mem_closure_geodesicHullSet ?_ hb0
  refine barycenter_mem_of_supportedIn hint ((convex_convexHull ℝ S).closure)
    isClosed_closure ?_
  exact measure_mono_null
    (Set.compl_subset_compl.mpr ((subset_convexHull ℝ S).trans subset_closure)) hμS

/-- Exact-membership fallback for the gate: a unit target direction belongs to the hull once it
is listed among the generators. Faithful to the paper's `conv_g` of the acted pair in (3.3). -/
theorem mem_geodesicHullSet_union_singleton {S : Set (Eucl d)} {ω : Eucl d} (hω : ‖ω‖ = 1) :
    ω ∈ geodesicHullSet (S ∪ {ω}) :=
  mem_geodesicHullSet_self (Set.mem_union_right S rfl) hω

/-- The closure of the `Set`-based hull is compact: it is a closed subset of the (compact)
unit sphere of `Eucl d`. -/
theorem isCompact_closure_geodesicHullSet (S : Set (Eucl d)) :
    IsCompact (closure (geodesicHullSet S)) :=
  IsCompact.of_isClosed_subset (isCompact_sphere (0 : Eucl d) 1) isClosed_closure
    (closure_minimal geodesicHullSet_subset_sphere Metric.isClosed_sphere)

/-- **Clearance.** A closed set `F` disjoint from the closure of the hull keeps a uniform
positive margin `ε` from every hull point, and every `ε`-ball centered in the hull misses `F`:
the radius budget all later cap/hop gates stay under (via `Disjoint.exists_thickenings` on the
compact closed hull). -/
theorem geodesicHullSet_clearance {S F : Set (Eucl d)} (hF : IsClosed F)
    (hdisj : Disjoint (closure (geodesicHullSet S)) F) :
    ∃ ε > 0, (∀ x ∈ geodesicHullSet S, ∀ y ∈ F, ε ≤ dist x y) ∧
      ∀ x ∈ geodesicHullSet S, Disjoint (Metric.ball x ε) F := by
  obtain ⟨δ, hδ, hthick⟩ := hdisj.exists_thickenings (isCompact_closure_geodesicHullSet S) hF
  have hdist : ∀ x ∈ geodesicHullSet S, ∀ y ∈ F, δ ≤ dist x y := by
    intro x hx y hy
    refine not_lt.mp fun hlt => ?_
    exact Set.disjoint_left.mp hthick
      (Metric.mem_thickening_iff.mpr ⟨x, subset_closure hx, by rwa [dist_comm]⟩)
      (Metric.self_subset_thickening hδ F hy)
  refine ⟨δ, hδ, hdist, fun x hx => Set.disjoint_left.mpr fun z hz hzF => ?_⟩
  exact absurd (Metric.mem_ball.mp hz) (not_lt.mpr (by rw [dist_comm]; exact hdist x hx z hzF))

end MeasureToMeasure.Leaves
