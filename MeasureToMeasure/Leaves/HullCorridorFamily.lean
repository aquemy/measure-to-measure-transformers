import MeasureToMeasure.Leaves.ArcHopCorridor
import MeasureToMeasure.Leaves.GeodesicHullSet

/-!
# Hull-confined corridor families to a common target (lemma 3.3, hull-gate geometry)

The confined-bystanders gate for `lemma_3_3` (paper Lemma 3.3, arXiv:2411.04551) relocates
finitely many staged balls to a common target direction `ω` while a bystander measure, supported
on a closed set `F` disjoint from the (closure of the) geodesic hull of the acted supports, must
be fixed exactly. The relocation engine (`exists_merge_tolerant_relocation`) consumes corridors as
data; this file builds that data with every hop gate confined near the hull, so the gates clear
`F` by the hull clearance alone.

**Construction.** Each corridor is the direct geodesic arc from its start `x i` to `ω`, truncated
at a landing point and subdivided into short hops:

* *Hull confinement*: the hull of orthant generators is geodesically convex
  (`geodesicConvex_geodesicHullSet_of_orthant`), so every arc point stays inside the hull, and
  `geodesicHullSet_clearance` keeps every gate ball of radius below the clearance margin off `F`.
  This replaces `exists_arc_hop_corridor`'s free waypoint (which may leave the hull) by the direct
  arc, which convexity confines.
* *Radial staggering*: chain `i` lands at chord distance exactly `r i = i * s` from `ω` (an
  intermediate-value choice along its arc), and the chord distance to `ω` is monotone along the
  arc (`dist_geodesicArc_target_anti`), so every gate of chain `i` stays at distance `≥ r i` from
  `ω` while every earlier landing ball sits at distance `r j ≤ r i - s`: gates clear all
  already-placed landing balls by the triangle inequality, with no extra avoidance construction.
* *Sorted starts*: the starts are indexed by nondecreasing chord distance to `ω`. The chord
  distance strictly drops once an arc moves off its base (`dist_geodesicArc_target_lt`), so a
  later start `x j` (`j > i`, hence at least as far from `ω`) can never lie on chain `i`'s arc;
  compactness (`exists_arc_clearance`) turns this into a uniform gate clearance from all
  not-yet-moved source balls.

The conclusion is exactly the corridor bundle `exists_merge_tolerant_relocation` consumes
(`hcap`/`hab`/`hb2`/`hgate_src`/`hgate_land`/`hland`), plus hull membership of every chain point
and gate-vs-`F` disjointness for the bystander-fixing clause.
-/

set_option autoImplicit false

namespace MeasureToMeasure.Leaves

open MeasureToMeasure MeasureToMeasure.Statements Set
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- Two points of the open orthant are never antipodal: the first coordinate of `q` is positive
while that of `-p` is negative. -/
theorem ne_neg_of_mem_orthant (hd : 1 ≤ d) {p q : Eucl d} (hp : p ∈ orthant d)
    (hq : q ∈ orthant d) : q ≠ -p := by
  intro h
  have h0 : (0 : ℕ) < d := hd
  have hq0 := hq ⟨0, h0⟩
  have hp0 := hp ⟨0, h0⟩
  rw [h] at hq0
  have hval : (-p) ⟨0, h0⟩ = -(p ⟨0, h0⟩) := rfl
  rw [hval] at hq0
  linarith

/-- Geodesic distance from a unit vector to itself is zero. -/
theorem geodesicDist_self_of_mem_sphere {p : Eucl d} (hp : p ∈ sphere d) :
    geodesicDist p p = 0 := by
  rw [geodesicDist, real_inner_self_eq_norm_sq, norm_eq_one_of_mem_sphere hp]
  norm_num [Real.arccos_one]

/-- Squared chord distance from an arc point to the arc's target: `2 - 2 cos (Θ - θ)` where
`Θ := geodesicDist p q`. -/
theorem dist_geodesicArc_target_sq {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) (θ : ℝ) :
    dist (geodesicArc p q θ) q ^ 2 = 2 - 2 * Real.cos (geodesicDist p q - θ) := by
  have harcq : geodesicArc p q (geodesicDist p q) = q := geodesicArc_geodesicDist hp hq hne hne'
  have hinner : (⟪geodesicArc p q θ, q⟫ : ℝ) = Real.cos (geodesicDist p q - θ) := by
    calc (⟪geodesicArc p q θ, q⟫ : ℝ)
        = ⟪geodesicArc p q θ, geodesicArc p q (geodesicDist p q)⟫ := by rw [harcq]
      _ = Real.cos (geodesicDist p q - θ) :=
          inner_geodesicArc_geodesicArc hp hq hne hne' θ (geodesicDist p q)
  have hn1 : ‖geodesicArc p q θ‖ = 1 :=
    norm_eq_one_of_mem_sphere (geodesicArc_mem_sphere hp hq hne hne' θ)
  have hn2 : ‖q‖ = 1 := norm_eq_one_of_mem_sphere hq
  rw [dist_eq_norm, norm_sub_sq_real, hn1, hn2, hinner]
  ring

/-- **Chord distance to the target is non-increasing along the arc**: on `[0, Θ]` the angle to
the target shrinks, and `cos` is anti-monotone on `[0, π]`. -/
theorem dist_geodesicArc_target_anti {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) {θ θ' : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ θ')
    (hΘ : θ' ≤ geodesicDist p q) :
    dist (geodesicArc p q θ') q ≤ dist (geodesicArc p q θ) q := by
  have hπ := (geodesicDist_mem_Icc p q).2
  have hcos : Real.cos (geodesicDist p q - θ) ≤ Real.cos (geodesicDist p q - θ') :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have h1 := dist_geodesicArc_target_sq hp hq hne hne' θ
  have h2 := dist_geodesicArc_target_sq hp hq hne hne' θ'
  calc dist (geodesicArc p q θ') q
      = Real.sqrt (dist (geodesicArc p q θ') q ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ ≤ Real.sqrt (dist (geodesicArc p q θ) q ^ 2) := by
        rw [h1, h2]; exact Real.sqrt_le_sqrt (by linarith)
    _ = dist (geodesicArc p q θ) q := Real.sqrt_sq dist_nonneg

/-- **Chord distance to the target strictly drops once the arc moves off its base**: the sorted-
starts exclusion driver (a point at least as far from the target as the base is never an interior
arc point). -/
theorem dist_geodesicArc_target_lt {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) {θ : ℝ} (h0 : 0 < θ) (hΘ : θ ≤ geodesicDist p q) :
    dist (geodesicArc p q θ) q < dist p q := by
  have hπ := (geodesicDist_mem_Icc p q).2
  have hcos : Real.cos (geodesicDist p q) < Real.cos (geodesicDist p q - θ) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have h1 := dist_geodesicArc_target_sq hp hq hne hne' θ
  have h2 := dist_geodesicArc_target_sq hp hq hne hne' 0
  rw [geodesicArc_zero, sub_zero] at h2
  calc dist (geodesicArc p q θ) q
      = Real.sqrt (dist (geodesicArc p q θ) q ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ < Real.sqrt (dist p q ^ 2) := by
        rw [h1, h2]
        exact Real.sqrt_lt_sqrt
          (by nlinarith [Real.neg_one_le_cos (geodesicDist p q - θ)]) (by linarith)
    _ = dist p q := Real.sqrt_sq dist_nonneg

/-- **Hull-confined corridor family to a common target.** For starts `x i` inside the geodesic
hull of a set `A ⊆ 𝕊^{d-1} ∩ orthant`, pairwise distinct and sorted by chord distance to a hull
target `ω`, and a closed set `F` disjoint from the closure of the hull, there are a radius
`ρ ∈ (0, δ]` and per-start hop chains `w i` on the sphere, entirely inside the hull, with capture
radii `a` and gate radii `b` satisfying every bound `exists_merge_tolerant_relocation` demands:
`w i 0 = x i`, `dist + ρ ≤ a < b ≤ 2` per hop, gates clear every later source ball
(`ball (x j) ρ`, `j > i`) and every earlier landing ball, every landing ball lands inside
`ball ω δ`, and every gate ball is disjoint from `F` (so a bystander supported on `F` is fixed
exactly by the engine's fixing clause). -/
theorem exists_hull_corridor_family (hd : 3 ≤ d) {A : Set (Eucl d)}
    (hA : A ⊆ sphere d ∩ orthant d) {ω : Eucl d} (hω : ω ∈ geodesicHullSet A)
    {N : ℕ} {x : Fin N → Eucl d} (hx : ∀ i, x i ∈ geodesicHullSet A)
    (hinj : Function.Injective x)
    (hsort : ∀ i j : Fin N, i ≤ j → dist (x i) ω ≤ dist (x j) ω)
    {F : Set (Eucl d)} (hF : IsClosed F)
    (hdisj : Disjoint (closure (geodesicHullSet A)) F)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ ∧ ∃ (Mc : Fin N → ℕ) (w : ∀ i, Fin (Mc i + 1) → Eucl d)
      (a b : ∀ i, Fin (Mc i) → ℝ),
      (∀ i t, w i t ∈ sphere d) ∧
      (∀ i t, w i t ∈ geodesicHullSet A) ∧
      (∀ i, w i 0 = x i) ∧
      (∀ i (t : Fin (Mc i)), dist (w i t.succ) (w i t.castSucc) + ρ ≤ a i t) ∧
      (∀ i t, a i t < b i t) ∧
      (∀ i t, b i t ≤ 2) ∧
      (∀ i j : Fin N, i < j → ∀ t : Fin (Mc i),
        Disjoint (Metric.ball (w i t.succ) (b i t)) (Metric.ball (x j) ρ)) ∧
      (∀ i j : Fin N, j < i → ∀ t : Fin (Mc i),
        Disjoint (Metric.ball (w i t.succ) (b i t))
          (Metric.ball (w j (Fin.last (Mc j))) ρ)) ∧
      (∀ j, Metric.ball (w j (Fin.last (Mc j))) ρ ⊆ Metric.ball ω δ) ∧
      (∀ i (t : Fin (Mc i)), Disjoint F (Metric.ball (w i t.succ) (b i t))) := by
  classical
  have hAo : A ⊆ orthant d := fun p hp => (hA hp).2
  have hKs : geodesicHullSet A ⊆ sphere d := geodesicHullSet_subset_sphere
  have hKo : geodesicHullSet A ⊆ orthant d := geodesicHullSet_subset_orthant hAo
  have hconv : GeodesicConvex (geodesicHullSet A) :=
    geodesicConvex_geodesicHullSet_of_orthant hAo
  have hωs : ω ∈ sphere d := hKs hω
  have hxs : ∀ i, x i ∈ sphere d := fun i => hKs (hx i)
  have hωo : ω ∈ orthant d := hKo hω
  have hxo : ∀ i, x i ∈ orthant d := fun i => hKo (hx i)
  have hnegx : ∀ i, ω ≠ -(x i) := fun i =>
    ne_neg_of_mem_orthant (by omega) (hxo i) hωo
  obtain ⟨ε0, hε0pos, _hε0dist, hε0ball⟩ := geodesicHullSet_clearance hF hdisj
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    exact ⟨min 1 δ, lt_min one_pos hδ, min_le_right _ _,
      Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun j => j.elim0, fun i => i.elim0⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  have hune : (Finset.univ : Finset (Fin N)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  -- distances to the target are positive off index zero (injectivity + sortedness)
  have hDpos : ∀ i : Fin N, (i : ℕ) ≠ 0 → 0 < dist (x i) ω := by
    intro i hi
    rcases (dist_nonneg (x := x i) (y := ω)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hxiω : x i = ω := by rw [← dist_eq_zero]; exact heq.symm
      have h0 : dist (x 0) ω ≤ 0 :=
        calc dist (x 0) ω ≤ dist (x i) ω := hsort 0 i (Fin.zero_le i)
          _ = 0 := heq.symm
      have hx0ω : x 0 = ω := by
        rw [← dist_eq_zero]; exact le_antisymm h0 dist_nonneg
      have heq0 : (0 : Fin N) = i := hinj (hx0ω.trans hxiω.symm)
      apply hi
      rw [← heq0]
      rfl
  -- the landing-spacing budget `s`
  set s1 : ℝ := Finset.univ.inf' hune
    (fun i : Fin N => if (i : ℕ) = 0 then δ else dist (x i) ω / (i : ℕ)) with hs1def
  have hs1pos : 0 < s1 := by
    rw [hs1def]
    refine (Finset.lt_inf'_iff hune).mpr fun i _ => ?_
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0]; exact hδ
    · rw [if_neg h0]
      exact div_pos (hDpos i h0) (by exact_mod_cast Nat.pos_of_ne_zero h0)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set s : ℝ := min s1 (δ / (2 * N)) with hsdef
  have hspos : 0 < s := lt_min hs1pos (by positivity)
  have hsδ2N : s ≤ δ / (2 * N) := min_le_right _ _
  have hss1 : s ≤ s1 := min_le_left _ _
  have hsr : ∀ i : Fin N, ((i : ℕ) : ℝ) * s ≤ dist (x i) ω := by
    intro i
    by_cases h0 : (i : ℕ) = 0
    · rw [h0]; simp
    · have hinf : s1 ≤ dist (x i) ω / (i : ℕ) := by
        have hle := Finset.inf'_le
          (fun i : Fin N => if (i : ℕ) = 0 then δ else dist (x i) ω / (i : ℕ))
          (Finset.mem_univ i)
        rw [if_neg h0] at hle
        exact le_trans (le_of_eq hs1def) hle
      have hiR : (0 : ℝ) < ((i : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hmul : s * ((i : ℕ) : ℝ) ≤ dist (x i) ω :=
        (le_div_iff₀ hiR).mp (le_trans hss1 hinf)
      rw [mul_comm]
      exact hmul
  -- landing radii, staggered by `s`
  set r : Fin N → ℝ := fun i => ((i : ℕ) : ℝ) * s with hrdef
  have hrnn : ∀ i, 0 ≤ r i := fun i => mul_nonneg (Nat.cast_nonneg _) hspos.le
  -- `x i = ω` forces zero geodesic distance
  have hne_of_pos : ∀ i : Fin N, 0 < geodesicDist (x i) ω → x i ≠ ω := by
    intro i hpos hcon
    rw [hcon, geodesicDist_self_of_mem_sphere hωs] at hpos
    exact lt_irrefl _ hpos
  -- landing parameters: chord distance to the target exactly `r i` (intermediate value)
  have hτex : ∀ i : Fin N, ∃ τ : ℝ, τ ∈ Set.Icc 0 (geodesicDist (x i) ω) ∧
      dist (geodesicArc (x i) ω τ) ω = r i := by
    intro i
    by_cases hxiω : x i = ω
    · refine ⟨0, ⟨le_refl 0, (geodesicDist_mem_Icc _ _).1⟩, ?_⟩
      have hd0 : dist (x i) ω = 0 := by rw [hxiω, dist_self]
      have hri0 : r i = 0 := le_antisymm (hd0 ▸ hsr i) (hrnn i)
      rw [geodesicArc_zero, hxiω, dist_self, hri0]
    · have hne : ω ≠ x i := fun hcon => hxiω hcon.symm
      have hΘ := geodesicDist_mem_Icc (x i) ω
      have hcont : ContinuousOn (fun θ => dist (geodesicArc (x i) ω θ) ω)
          (Set.Icc 0 (geodesicDist (x i) ω)) :=
        ((continuous_geodesicArc _ _).dist continuous_const).continuousOn
      have hsub := intermediate_value_Icc' hΘ.1 hcont
      have hmem : r i ∈ Set.Icc (dist (geodesicArc (x i) ω (geodesicDist (x i) ω)) ω)
          (dist (geodesicArc (x i) ω 0) ω) := by
        rw [geodesicArc_geodesicDist (hxs i) hωs hne (hnegx i), dist_self, geodesicArc_zero]
        exact ⟨hrnn i, hsr i⟩
      obtain ⟨τ, hτIcc, hτeq⟩ := hsub hmem
      exact ⟨τ, hτIcc, hτeq⟩
  choose τ hτmem hτdist using hτex
  -- clearance of each truncated arc from every later source
  have hcex : ∀ i : Fin N, ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ Set.Icc 0 (τ i), ∀ j : Fin N, i < j →
      c ≤ dist (geodesicArc (x i) ω θ) (x j) := by
    intro i
    have havoid : ∀ (k : Fin (N - ((i : ℕ) + 1))), ∀ θ ∈ Set.Icc 0 (τ i),
        geodesicArc (x i) ω θ ≠
          x ⟨(i : ℕ) + 1 + (k : ℕ), by omega⟩ := by
      intro k θ hθ heq
      rcases eq_or_lt_of_le hθ.1 with hzero | hpos
      · rw [← hzero, geodesicArc_zero] at heq
        have hvals := congrArg Fin.val (hinj heq)
        simp only [] at hvals
        omega
      · have hθΘ : θ ≤ geodesicDist (x i) ω := hθ.2.trans (hτmem i).2
        have hΘpos : 0 < geodesicDist (x i) ω := lt_of_lt_of_le hpos hθΘ
        have hxiω : x i ≠ ω := hne_of_pos i hΘpos
        have hne : ω ≠ x i := fun hcon => hxiω hcon.symm
        have hlt : dist (geodesicArc (x i) ω θ) ω < dist (x i) ω :=
          dist_geodesicArc_target_lt (hxs i) hωs hne (hnegx i) hpos hθΘ
        have hij : i ≤ (⟨(i : ℕ) + 1 + (k : ℕ), by omega⟩ : Fin N) := by
          rw [Fin.le_def]; simp; omega
        have hs := hsort i _ hij
        rw [heq] at hlt
        exact absurd hs (not_le.mpr hlt)
    obtain ⟨c, hcpos, hc⟩ := exists_arc_clearance (continuous_geodesicArc (x i) ω)
      (hτmem i).1 (fun k : Fin (N - ((i : ℕ) + 1)) =>
        x ⟨(i : ℕ) + 1 + (k : ℕ), by omega⟩) havoid
    refine ⟨c, hcpos, fun θ hθ j hij => ?_⟩
    have hlt := Fin.lt_def.mp hij
    have hkin : (j : ℕ) - ((i : ℕ) + 1) < N - ((i : ℕ) + 1) := by
      have := j.isLt; omega
    have hcall := hc θ hθ ⟨(j : ℕ) - ((i : ℕ) + 1), hkin⟩
    convert hcall using 3
    apply Fin.ext
    simp
    omega
  choose c hcpos hcbound using hcex
  -- the global radius budget
  set c0 : ℝ := min (min ε0 s) (min 1 (Finset.univ.inf' hune c)) with hc0def
  have hcinf_pos : 0 < Finset.univ.inf' hune c :=
    (Finset.lt_inf'_iff hune).mpr fun i _ => hcpos i
  have hc0pos : 0 < c0 := lt_min (lt_min hε0pos hspos) (lt_min one_pos hcinf_pos)
  have hc0ε : c0 ≤ ε0 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc0s : c0 ≤ s := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc01 : c0 ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc0c : ∀ i, c0 ≤ c i := fun i => le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ i)))
  -- hop scale, subdivision counts, and chains
  set h0 : ℝ := c0 / 16 with hh0def
  have hh0pos : 0 < h0 := by positivity
  set Mc : Fin N → ℕ := fun i => ⌈τ i / h0⌉₊ with hMcdef
  set st : Fin N → ℝ := fun i => τ i / (Mc i : ℝ) with hstdef
  set w : ∀ i, Fin (Mc i + 1) → Eucl d :=
    fun i t => geodesicArc (x i) ω (((t : ℕ) : ℝ) * st i) with hwdef
  have hτnn : ∀ i, 0 ≤ τ i := fun i => (hτmem i).1
  have hMzero : ∀ i, Mc i = 0 → τ i = 0 := by
    intro i hMi
    have hle : τ i / h0 ≤ 0 := Nat.ceil_eq_zero.mp hMi
    have hτle : τ i ≤ 0 := by
      by_contra hpos
      exact absurd hle (not_le.mpr (div_pos (not_le.mp hpos) hh0pos))
    exact le_antisymm hτle (hτnn i)
  have hstnn : ∀ i, 0 ≤ st i := fun i => div_nonneg (hτnn i) (Nat.cast_nonneg _)
  have hMst : ∀ i, (Mc i : ℝ) * st i = τ i := by
    intro i
    rcases Nat.eq_zero_or_pos (Mc i) with hMi | hMi
    · rw [hMi, hMzero i hMi]; simp
    · have hMR : (0 : ℝ) < (Mc i : ℝ) := by exact_mod_cast hMi
      rw [hstdef]
      field_simp
  have hsth : ∀ i, st i ≤ h0 := by
    intro i
    rcases Nat.eq_zero_or_pos (Mc i) with hMi | hMi
    · rw [hstdef]
      simp only [hMzero i hMi, zero_div]
      exact hh0pos.le
    · have hMR : (0 : ℝ) < (Mc i : ℝ) := by exact_mod_cast hMi
      rw [hstdef, div_le_iff₀ hMR]
      have hceil := Nat.le_ceil (τ i / h0)
      calc τ i = (τ i / h0) * h0 := by field_simp
        _ ≤ (Mc i : ℝ) * h0 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hceil) hh0pos.le
        _ = h0 * (Mc i : ℝ) := mul_comm _ _
  have hθrange : ∀ i (t : Fin (Mc i + 1)), ((t : ℕ) : ℝ) * st i ∈ Set.Icc 0 (τ i) := by
    intro i t
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) (hstnn i)
    · calc ((t : ℕ) : ℝ) * st i ≤ (Mc i : ℝ) * st i :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Fin.is_le t) (hstnn i)
        _ = τ i := hMst i
  have hMpos_ne : ∀ i, 0 < Mc i → x i ≠ ω := by
    intro i hMi
    have hdivpos : 0 < τ i / h0 := Nat.ceil_pos.mp hMi
    have hτpos : 0 < τ i := by
      rcases div_pos_iff.mp hdivpos with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith
    exact hne_of_pos i (lt_of_lt_of_le hτpos (hτmem i).2)
  -- chain points stay inside the hull, hence on the sphere
  have harcK : ∀ i, ∀ θ ∈ Set.Icc 0 (τ i),
      geodesicArc (x i) ω θ ∈ geodesicHullSet A := by
    intro i θ hθ
    rcases eq_or_lt_of_le hθ.1 with hzero | hpos
    · rw [← hzero, geodesicArc_zero]; exact hx i
    · have hθΘ : θ ≤ geodesicDist (x i) ω := hθ.2.trans (hτmem i).2
      have hxiω : x i ≠ ω := hne_of_pos i (lt_of_lt_of_le hpos hθΘ)
      have hne : ω ≠ x i := fun hcon => hxiω hcon.symm
      rcases eq_or_lt_of_le hθΘ with hΘeq | hΘlt
      · rw [hΘeq, geodesicArc_geodesicDist (hxs i) hωs hne (hnegx i)]; exact hω
      · exact geodesicArc_mem_of_geodesicConvex hconv (hx i) hω hne (hnegx i) ⟨hpos, hΘlt⟩
  have hwK : ∀ i t, w i t ∈ geodesicHullSet A := fun i t => harcK i _ (hθrange i t)
  have hws : ∀ i t, w i t ∈ sphere d := fun i t => hKs (hwK i t)
  have hw0 : ∀ i, w i 0 = x i := by
    intro i
    show geodesicArc (x i) ω ((((0 : Fin (Mc i + 1)) : ℕ) : ℝ) * st i) = x i
    simp [geodesicArc_zero]
  have hwlast : ∀ j, w j (Fin.last (Mc j)) = geodesicArc (x j) ω (τ j) := by
    intro j
    show geodesicArc (x j) ω ((((Fin.last (Mc j)) : ℕ) : ℝ) * st j) = _
    rw [Fin.val_last, hMst j]
  have hlanddist : ∀ j, dist (w j (Fin.last (Mc j))) ω = r j := by
    intro j
    rw [hwlast j]
    exact hτdist j
  -- radial lower bound along each chain
  have hrad : ∀ i, ∀ θ ∈ Set.Icc 0 (τ i), r i ≤ dist (geodesicArc (x i) ω θ) ω := by
    intro i θ hθ
    rcases eq_or_lt_of_le (hτnn i) with hτ0 | hτpos
    · have hθ0 : θ = 0 := le_antisymm (hτ0 ▸ hθ.2) hθ.1
      have hτd := hτdist i
      rw [← hτ0] at hτd
      rw [hθ0]
      exact le_of_eq hτd.symm
    · have hxiω : x i ≠ ω := hne_of_pos i (lt_of_lt_of_le hτpos (hτmem i).2)
      have hne : ω ≠ x i := fun hcon => hxiω hcon.symm
      calc r i = dist (geodesicArc (x i) ω (τ i)) ω := (hτdist i).symm
        _ ≤ dist (geodesicArc (x i) ω θ) ω :=
          dist_geodesicArc_target_anti (hxs i) hωs hne (hnegx i) hθ.1 hθ.2 (hτmem i).2
  -- per-hop displacement bound
  have hhop : ∀ i (t : Fin (Mc i)), dist (w i t.succ) (w i t.castSucc) ≤ c0 / 8 := by
    intro i t
    have hMi : 0 < Mc i := t.pos
    have hxiω := hMpos_ne i hMi
    have hne : ω ≠ x i := fun hcon => hxiω hcon.symm
    have hsuccval : (t.succ : ℕ) = (t : ℕ) + 1 := rfl
    have hcastval : (t.castSucc : ℕ) = (t : ℕ) := rfl
    show dist (geodesicArc (x i) ω (((t.succ : ℕ) : ℝ) * st i))
        (geodesicArc (x i) ω (((t.castSucc : ℕ) : ℝ) * st i)) ≤ c0 / 8
    rw [hsuccval, hcastval]
    calc dist (geodesicArc (x i) ω ((((t : ℕ) + 1 : ℕ) : ℝ) * st i))
          (geodesicArc (x i) ω (((t : ℕ) : ℝ) * st i))
        ≤ 2 * |(((t : ℕ) + 1 : ℕ) : ℝ) * st i - ((t : ℕ) : ℝ) * st i| :=
          dist_geodesicArc_le (hxs i) hωs hne (hnegx i) _ _
      _ = 2 * st i := by
          rw [show (((t : ℕ) + 1 : ℕ) : ℝ) * st i - ((t : ℕ) : ℝ) * st i = st i by
            push_cast; ring]
          rw [abs_of_nonneg (hstnn i)]
      _ ≤ 2 * h0 := by linarith [hsth i]
      _ = c0 / 8 := by rw [hh0def]; ring
  -- assemble the bundle
  refine ⟨c0 / 4, by positivity, ?_, Mc, w, fun _ _ => 3 * c0 / 8, fun _ _ => c0 / 2,
    hws, hwK, hw0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ρ ≤ δ
    have hs2N : s * (2 * (N : ℝ)) ≤ δ := (le_div_iff₀ (by positivity)).mp hsδ2N
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [hc0s, hspos.le, mul_nonneg hspos.le (by linarith : (0 : ℝ) ≤ 2 * (N : ℝ) - 1)]
  · -- capture radii
    intro i t
    have := hhop i t
    linarith
  · -- capture < gate
    intro i t
    simp only []
    linarith
  · -- gate ≤ 2
    intro i t
    simp only []
    linarith
  · -- gates clear every later source ball
    intro i j hij t
    refine Metric.ball_disjoint_ball ?_
    have hclear := hcbound i _ (hθrange i t.succ) j hij
    calc c0 / 2 + c0 / 4 ≤ c0 := by linarith
      _ ≤ c i := hc0c i
      _ ≤ dist (w i t.succ) (x j) := hclear
  · -- gates clear every earlier landing ball
    intro i j hji t
    refine Metric.ball_disjoint_ball ?_
    have hgc : r i ≤ dist (w i t.succ) ω := hrad i _ (hθrange i t.succ)
    have htri := dist_triangle (w i t.succ) (w j (Fin.last (Mc j))) ω
    rw [hlanddist j] at htri
    have hji' : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp hji)
    have hrs : s ≤ r i - r j := by
      show s ≤ ((i : ℕ) : ℝ) * s - ((j : ℕ) : ℝ) * s
      nlinarith [hspos.le]
    linarith [hc0s]
  · -- landing balls land inside `ball ω δ`
    intro j z hz
    rw [Metric.mem_ball] at hz ⊢
    have h1 : dist z ω < c0 / 4 + r j :=
      calc dist z ω ≤ dist z (w j (Fin.last (Mc j))) + dist (w j (Fin.last (Mc j))) ω :=
            dist_triangle _ _ _
        _ < c0 / 4 + r j := by rw [hlanddist j]; linarith
    have hrj : r j ≤ ((N : ℝ) - 1) * s := by
      show ((j : ℕ) : ℝ) * s ≤ _
      have hjN : ((j : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast j.isLt
      nlinarith [hspos.le]
    have hs2N : s * (2 * (N : ℝ)) ≤ δ := (le_div_iff₀ (by positivity)).mp hsδ2N
    have h3 : s / 4 + ((N : ℝ) - 1) * s ≤ δ / 2 := by linarith [hspos.le]
    linarith [hc0s]
  · -- gates clear the bystander set `F`
    intro i t
    have hballs : Metric.ball (w i t.succ) (c0 / 2) ⊆ Metric.ball (w i t.succ) ε0 :=
      Metric.ball_subset_ball (by linarith [hc0ε])
    exact Set.disjoint_of_subset_right hballs (hε0ball _ (hwK i t.succ)).symm
