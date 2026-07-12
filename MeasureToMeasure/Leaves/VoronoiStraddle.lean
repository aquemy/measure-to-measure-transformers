import MeasureToMeasure.Leaves.VoronoiAdjacency
import MeasureToMeasure.Leaves.GeodesicArcChain

/-!
# A short chain crossing between two adjacent Voronoi cells (`prop_2_2` Stage 3, relay leaf 3)

Given `voronoiAdjacent x j k` (the cells' closures share a touching point `y`), build a chain
(via `exists_geodesicConvex_arc_chain`, now that PR #226 fixed its `hCopen` to be discharge-able)
from a point in `voronoiCell x j` to a point in `voronoiCell x k`, confined to a small geodesic
ball around `y` -- NOT the two-cell union, which is generally not geodesically convex.

**The needed bridge**: `geodesicBall z R` is geodesically convex, and RELATIVELY open in the
sphere, for `R ∈ (0, π/2]` -- via the exact identity `geodesicBall z R = sphere d ∩ {x | cos R <
⟪z, x⟫}` (from `cos_geodesicDist` plus `Real.cos`'s strict antitonicity on `[0, π]`), which
simultaneously supplies `geodesicConvex_inner_cap`'s cap shape (convexity) and an ambient-open `U`
(relative openness, `hCopen`'s witness).

M3b/mid-level staging: Stage 3 item 3 (Voronoi-adjacency relay) of the `prop_2_2` Steps 2-3
campaign; see project notes.
-/

namespace MeasureToMeasure.Leaves

open Set MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

private theorem cos_lt_cos_iff {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) Real.pi)
    (hb : b ∈ Set.Icc (0 : ℝ) Real.pi) : Real.cos b < Real.cos a ↔ a < b := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hge := Real.strictAntiOn_cos.antitoneOn hb ha hcon
    linarith
  · exact Real.strictAntiOn_cos ha hb

/-- **A geodesic ball is exactly a sphere-restricted inner-product cap**, for `R ∈ (0, π]`. -/
theorem geodesicBall_eq_inter {z : Eucl d} (hz : z ∈ sphere d) {R : ℝ}
    (hR : R ∈ Set.Ioc 0 Real.pi) :
    geodesicBall z R = sphere d ∩ {x : Eucl d | Real.cos R < ⟪z, x⟫} := by
  have hRIcc : R ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hR.1.le, hR.2⟩
  ext x
  simp only [geodesicBall, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hxs, hdist⟩
    refine ⟨hxs, ?_⟩
    rw [← cos_geodesicDist hz hxs]
    exact (cos_lt_cos_iff (geodesicDist_mem_Icc z x) hRIcc).mpr hdist
  · rintro ⟨hxs, hcos⟩
    refine ⟨hxs, ?_⟩
    rw [← cos_geodesicDist hz hxs] at hcos
    exact (cos_lt_cos_iff (geodesicDist_mem_Icc z x) hRIcc).mp hcos

/-- **A geodesic ball of radius `≤ π/2` is geodesically convex.** -/
theorem geodesicConvex_geodesicBall {z : Eucl d} (hz : z ∈ sphere d) {R : ℝ}
    (hR : R ∈ Set.Ioc 0 (Real.pi / 2)) : GeodesicConvex (geodesicBall z R) := by
  have hpi2 : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hRpi : R ∈ Set.Ioc (0 : ℝ) Real.pi := ⟨hR.1, hR.2.trans hpi2⟩
  rw [geodesicBall_eq_inter hz hRpi]
  have hc : (0 : ℝ) ≤ Real.cos R := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hR.1], hR.2⟩
  exact geodesicConvex_inner_cap z hc

/-- **A geodesic ball of radius `≤ π` is relatively open in the sphere.** -/
theorem exists_isOpen_inter_geodesicBall {z : Eucl d} (hz : z ∈ sphere d) {R : ℝ}
    (hR : R ∈ Set.Ioc 0 Real.pi) :
    ∃ U : Set (Eucl d), IsOpen U ∧ geodesicBall z R = sphere d ∩ U :=
  ⟨{x : Eucl d | Real.cos R < ⟪z, x⟫}, isOpen_lt continuous_const (by fun_prop),
    geodesicBall_eq_inter hz hR⟩

/-- **A geodesic ball of radius `< π` never covers the whole sphere.** -/
theorem sphere_diff_geodesicBall_nonempty {z : Eucl d} (hz : z ∈ sphere d) {R : ℝ}
    (hR : R < Real.pi) : (sphere d \ geodesicBall z R).Nonempty := by
  have hznegs : -z ∈ sphere d := by
    simp only [sphere, Metric.mem_sphere, dist_zero_right, norm_neg] at hz ⊢
    exact hz
  refine ⟨-z, ⟨hznegs, ?_⟩⟩
  intro hmem
  have hdist : geodesicDist z (-z) < R := hmem.2
  have hcos : Real.cos (geodesicDist z (-z)) = ⟪z, -z⟫ := cos_geodesicDist hz hznegs
  rw [inner_neg_right, real_inner_self_eq_norm_sq, norm_eq_one_of_mem_sphere hz, one_pow] at hcos
  have hpi : geodesicDist z (-z) = Real.pi := by
    have hle : geodesicDist z (-z) ≤ Real.pi := (geodesicDist_mem_Icc z (-z)).2
    by_contra hne
    have hlt : geodesicDist z (-z) < Real.pi := lt_of_le_of_ne hle hne
    have hcontra := (cos_lt_cos_iff (geodesicDist_mem_Icc z (-z)) ⟨Real.pi_pos.le, le_refl _⟩).mpr hlt
    rw [hcos, Real.cos_pi] at hcontra
    linarith
  rw [hpi] at hdist
  linarith

/-- **A short chain crossing between two adjacent Voronoi cells.** From a touching point `y`
of `voronoiCell x j` and `voronoiCell x k`, extract points `p, q` strictly inside each cell but
close enough to `y` (via `mem_closure_iff` with the ambient-open geodesic-distance neighborhoods
of `y`) that a uniform-radius ball around `y` of any target size `ρ0 < π/2` contains a whole
`exists_geodesicConvex_arc_chain` chain from `p` to `q`. -/
theorem exists_voronoiCell_straddle_chain {M : ℕ} (x : Fin M → Eucl d)
    {j k : Fin M} (hjkne : j ≠ k) (hadj : voronoiAdjacent x j k)
    {ρ0 : ℝ} (hρ0 : ρ0 ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∃ (y : Eucl d) (n : ℕ) (z : ℕ → Eucl d) (Rad : ℕ → ℝ),
      z 0 ∈ voronoiCell x j ∧ z n ∈ voronoiCell x k ∧
      0 < n ∧
      (∀ i, z i ∈ sphere d) ∧
      (∀ i, Rad i ∈ Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ i, geodesicBall (z i) (Rad i) ⊆ geodesicBall y ρ0) ∧
      (∀ i < n, (geodesicBall (z i) (Rad i) ∩ geodesicBall (z (i + 1)) (Rad (i + 1))).Nonempty) ∧
      (∀ a b, a + 2 ≤ b → b ≤ n →
        Disjoint (geodesicBall (z a) (Rad a)) (geodesicBall (z b) (Rad b))) := by
  obtain ⟨y, hyj, hyk⟩ := hadj
  have hys : y ∈ sphere d := by
    have hcl : y ∈ closure (Metric.sphere (0 : Eucl d) 1) :=
      closure_mono (voronoiCell_subset_sphere x j) hyj
    rwa [Metric.isClosed_sphere.closure_eq] at hcl
  set ρ : ℝ := min ρ0 (Real.pi / 4) with hρdef
  have hρpos : 0 < ρ := lt_min hρ0.1 (by linarith [Real.pi_pos])
  have hρlt : ρ < Real.pi / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hρle0 : ρ ≤ ρ0 := min_le_left _ _
  have hextract : ∀ (S : Set (Eucl d)) (_ : y ∈ closure S), ∃ z ∈ S, geodesicDist y z < ρ / 2 := by
    intro S hyS
    have hopen : IsOpen {x' : Eucl d | geodesicDist y x' < ρ / 2} :=
      isOpen_lt (continuous_geodesicDist y) continuous_const
    have hmemo : y ∈ {x' : Eucl d | geodesicDist y x' < ρ / 2} := by
      show geodesicDist y y < ρ / 2
      rw [geodesicDist, real_inner_self_eq_norm_sq, norm_eq_one_of_mem_sphere hys, one_pow,
        Real.arccos_one]
      linarith
    obtain ⟨z', hz'mem, hz'S⟩ := mem_closure_iff.mp hyS _ hopen hmemo
    exact ⟨z', hz'S, hz'mem⟩
  obtain ⟨p, hpj, hpdist⟩ := hextract (voronoiCell x j) hyj
  obtain ⟨q, hqk, hqdist⟩ := hextract (voronoiCell x k) hyk
  have hps : p ∈ sphere d := voronoiCell_subset_sphere x j hpj
  have hqs : q ∈ sphere d := voronoiCell_subset_sphere x k hqk
  have hpq_ne : p ≠ q := by
    intro heq
    exact (voronoiCell_disjoint x hjkne).ne_of_mem hpj (heq ▸ hqk) heq
  have hpqdist : geodesicDist p q < ρ := by
    calc geodesicDist p q ≤ geodesicDist p y + geodesicDist y q :=
          geodesicDist_triangle hps hys hqs
      _ = geodesicDist y p + geodesicDist y q := by rw [geodesicDist_comm p y]
      _ < ρ / 2 + ρ / 2 := by linarith
      _ = ρ := by ring
  have hpq_nane : q ≠ -p := by
    intro heq
    have : geodesicDist p q = Real.pi := by
      rw [heq, geodesicDist, inner_neg_right, real_inner_self_eq_norm_sq,
        norm_eq_one_of_mem_sphere hps, one_pow, show (-(1:ℝ)) = Real.cos Real.pi by
          rw [Real.cos_pi], Real.arccos_cos Real.pi_pos.le (le_refl Real.pi)]
    linarith [hpqdist]
  have hpB : p ∈ geodesicBall y ρ := ⟨hps, by linarith⟩
  have hqB : q ∈ geodesicBall y ρ := ⟨hqs, by linarith⟩
  obtain ⟨n, z, Rad, hnpos, hz0, hzn, hzmem, hRmem, hsub, hchain, hdisj⟩ :=
    exists_geodesicConvex_arc_chain (geodesicConvex_geodesicBall hys ⟨hρpos, hρlt.le⟩)
      (exists_isOpen_inter_geodesicBall hys ⟨hρpos, hρlt.le.trans (by linarith [Real.pi_pos])⟩)
      (sphere_diff_geodesicBall_nonempty hys (hρlt.trans (by linarith [Real.pi_pos])))
      hpB hqB hpq_ne.symm hpq_nane
  refine ⟨y, n, z, Rad, hz0 ▸ hpj, hzn ▸ hqk, hnpos, hzmem, hRmem, ?_, hchain, hdisj⟩
  intro i
  exact (hsub i).trans (fun a ha => ⟨ha.1, ha.2.trans_le hρle0⟩)

/-- **A short chain crossing between two adjacent Voronoi cells, from a GIVEN starting point.**
Leaf-4 sub-campaign piece 1: the multi-hop concatenation needs each straddle hop to continue from
wherever the PREVIOUS piece (a within-cell connector chain) left off, not from a fresh point this
lemma extracts itself -- so `p` is now a hypothesis (already known close to the touching point `y`,
e.g. because the caller just built a chain ending there), and only the far endpoint `q` is freshly
extracted. Same construction as `exists_voronoiCell_straddle_chain` otherwise; kept as a separate
theorem rather than refactoring that one in place, since the self-extracting form is still directly
useful as its own entry point. -/
theorem exists_voronoiCell_straddle_chain_of_given {M : ℕ} (x : Fin M → Eucl d)
    {j k : Fin M} (hjkne : j ≠ k) {y : Eucl d} (hyj : y ∈ closure (voronoiCell x j))
    (hyk : y ∈ closure (voronoiCell x k)) {ρ0 : ℝ} (hρ0 : ρ0 ∈ Set.Ioo 0 (Real.pi / 2))
    {p : Eucl d} (hpj : p ∈ voronoiCell x j) (hpdist : geodesicDist y p < ρ0 / 2) :
    ∃ (n : ℕ) (z : ℕ → Eucl d) (Rad : ℕ → ℝ),
      z 0 = p ∧ z n ∈ voronoiCell x k ∧
      0 < n ∧
      (∀ i, z i ∈ sphere d) ∧
      (∀ i, Rad i ∈ Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ i, geodesicBall (z i) (Rad i) ⊆ geodesicBall y ρ0) ∧
      (∀ i < n, (geodesicBall (z i) (Rad i) ∩ geodesicBall (z (i + 1)) (Rad (i + 1))).Nonempty) ∧
      (∀ a b, a + 2 ≤ b → b ≤ n →
        Disjoint (geodesicBall (z a) (Rad a)) (geodesicBall (z b) (Rad b))) := by
  have hys : y ∈ sphere d := by
    have hcl : y ∈ closure (Metric.sphere (0 : Eucl d) 1) :=
      closure_mono (voronoiCell_subset_sphere x j) hyj
    rwa [Metric.isClosed_sphere.closure_eq] at hcl
  have hextract : ∀ (S : Set (Eucl d)) (_ : y ∈ closure S), ∃ z ∈ S, geodesicDist y z < ρ0 / 2 := by
    intro S hyS
    have hopen : IsOpen {x' : Eucl d | geodesicDist y x' < ρ0 / 2} :=
      isOpen_lt (continuous_geodesicDist y) continuous_const
    have hmemo : y ∈ {x' : Eucl d | geodesicDist y x' < ρ0 / 2} := by
      show geodesicDist y y < ρ0 / 2
      rw [geodesicDist, real_inner_self_eq_norm_sq, norm_eq_one_of_mem_sphere hys, one_pow,
        Real.arccos_one]
      linarith [hρ0.1]
    obtain ⟨z', hz'mem, hz'S⟩ := mem_closure_iff.mp hyS _ hopen hmemo
    exact ⟨z', hz'S, hz'mem⟩
  obtain ⟨q, hqk, hqdist⟩ := hextract (voronoiCell x k) hyk
  have hps : p ∈ sphere d := voronoiCell_subset_sphere x j hpj
  have hqs : q ∈ sphere d := voronoiCell_subset_sphere x k hqk
  have hpq_ne : p ≠ q := by
    intro heq
    exact (voronoiCell_disjoint x hjkne).ne_of_mem hpj (heq ▸ hqk) heq
  have hpqdist : geodesicDist p q < ρ0 := by
    calc geodesicDist p q ≤ geodesicDist p y + geodesicDist y q :=
          geodesicDist_triangle hps hys hqs
      _ = geodesicDist y p + geodesicDist y q := by rw [geodesicDist_comm p y]
      _ < ρ0 / 2 + ρ0 / 2 := by linarith
      _ = ρ0 := by ring
  have hpq_nane : q ≠ -p := by
    intro heq
    have : geodesicDist p q = Real.pi := by
      rw [heq, geodesicDist, inner_neg_right, real_inner_self_eq_norm_sq,
        norm_eq_one_of_mem_sphere hps, one_pow, show (-(1:ℝ)) = Real.cos Real.pi by
          rw [Real.cos_pi], Real.arccos_cos Real.pi_pos.le (le_refl Real.pi)]
    linarith [hpqdist, hρ0.2, Real.pi_pos]
  have hpB : p ∈ geodesicBall y ρ0 := ⟨hps, by linarith [hρ0.1]⟩
  have hqB : q ∈ geodesicBall y ρ0 := ⟨hqs, by linarith [hρ0.1]⟩
  obtain ⟨n, z, Rad, hnpos, hz0, hzn, hzmem, hRmem, hsub, hchain, hdisj⟩ :=
    exists_geodesicConvex_arc_chain (geodesicConvex_geodesicBall hys ⟨hρ0.1, hρ0.2.le⟩)
      (exists_isOpen_inter_geodesicBall hys ⟨hρ0.1, hρ0.2.le.trans (by linarith [Real.pi_pos])⟩)
      (sphere_diff_geodesicBall_nonempty hys (hρ0.2.trans (by linarith [Real.pi_pos])))
      hpB hqB hpq_ne.symm hpq_nane
  exact ⟨n, z, Rad, hz0, hzn ▸ hqk, hnpos, hzmem, hRmem, hsub, hchain, hdisj⟩

end MeasureToMeasure.Leaves
