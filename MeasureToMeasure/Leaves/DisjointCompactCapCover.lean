import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Data.Fintype.Card

/-!
# Leaf (lemma 5.4 campaign, G4): cap covers of pairwise-disjoint compacts

Metric-space half of the compact-cores group. Pairwise-disjoint compacts `K i` (`i : Fin n`)
have a uniform positive gap `δ`: every point of `K i` is at distance `≥ δ` from every point of
`K j` for `j ≠ i`. Consequently, for any radius `r` with `0 < r` and `2 * r ≤ δ`, each `K i`
admits a finite cover by balls of radius `r` centred *in* `K i`, each such ball is disjoint
from every other core, and balls centred in distinct cores are disjoint from each other. This
is the cross-piece disjoint cap system the Phase-1 construction downstream gates on.

Deliberately stated over an ABSTRACT `[MetricSpace E]` in a file importing NO project-specific
`Eucl d`-touching content: `Eucl d`'s `PiLp`-derived instances are heavy enough to time out
generic unification inside tactic proofs (see `UniformRadiusPacking.lean` for the precedent).
The `Eucl d` instantiation lives in `CompactCore.lean` as a cheap term-mode application.
-/

namespace MeasureToMeasure.Leaves

open Metric

variable {E : Type*} [MetricSpace E] {n : ℕ}

/-- **Uniform gap.** Pairwise-disjoint compacts have a uniform positive separation: some
`δ > 0` bounds from below the distance between any point of `K i` and any point of `K j`,
`i ≠ j`. Via disjoint thickenings of a compact and a closed set, minimised over the finitely
many pairs. -/
theorem exists_pos_gap_of_pairwise_disjoint_isCompact
    {K : Fin n → Set E} (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise fun i j => Disjoint (K i) (K j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, δ ≤ dist x y := by
  classical
  have hsep : ∀ i j, i ≠ j → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K i, ∀ y ∈ K j, δ ≤ dist x y := by
    intro i j hij
    obtain ⟨δ, hδ, hd⟩ := (hdisj hij).exists_thickenings (hK i) (hK j).isClosed
    refine ⟨δ, hδ, fun x hx y hy => ?_⟩
    by_contra h
    rw [not_le] at h
    exact Set.disjoint_left.mp hd
      (mem_thickening_iff.mpr ⟨x, hx, by rwa [dist_comm]⟩)
      (self_subset_thickening hδ _ hy)
  set g : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 = p.2 then 1 else (hsep p.1 p.2 h).choose with hg
  have hgpos : ∀ p, 0 < g p := by
    intro p
    by_cases h : p.1 = p.2
    · simp [hg, h]
    · simpa [hg, h] using (hsep p.1 p.2 h).choose_spec.1
  have hgsep : ∀ i j (h : i ≠ j), ∀ x ∈ K i, ∀ y ∈ K j, g (i, j) ≤ dist x y := by
    intro i j h x hx y hy
    have := (hsep i j h).choose_spec.2 x hx y hy
    simpa [hg, h] using this
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun i => i.elim0⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hne : (Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
      Finset.univ_nonempty
    refine ⟨(Finset.univ ×ˢ Finset.univ).inf' hne g, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff hne).mpr fun p _ => hgpos p
    · intro i j hij x hx y hy
      exact le_trans (Finset.inf'_le g (by simp)) (hgsep i j hij x hx y hy)

/-- **Cap cover of one core.** Below the gap, each compact core has a finite cover by balls
of radius `r` centred in the core, and every such ball is disjoint from every other core. -/
theorem exists_finite_ball_cover_of_gap
    {K : Fin n → Set E} (hK : ∀ i, IsCompact (K i)) {δ r : ℝ} (hr : 0 < r) (hrδ : r ≤ δ)
    (hgap : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, δ ≤ dist x y) (i : Fin n) :
    ∃ t : Set E, t ⊆ K i ∧ t.Finite ∧ (K i ⊆ ⋃ c ∈ t, ball c r) ∧
      ∀ c ∈ t, ∀ j, j ≠ i → Disjoint (ball c r) (K j) := by
  obtain ⟨t, hts, htf, htc⟩ := (hK i).finite_cover_balls hr
  refine ⟨t, hts, htf, htc, fun c hc j hji => Set.disjoint_left.mpr fun y hyb hyK => ?_⟩
  have h1 : δ ≤ dist c y := hgap i j hji.symm c (hts hc) y hyK
  have h2 : dist y c < r := mem_ball.mp hyb
  rw [dist_comm] at h2
  linarith

/-- **Cross-core ball disjointness.** Balls of radius `r ≤ δ / 2` centred in distinct cores
are disjoint. -/
theorem ball_disjoint_ball_of_gap
    {K : Fin n → Set E} {δ r : ℝ} (hrδ : 2 * r ≤ δ)
    (hgap : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, δ ≤ dist x y)
    {i j : Fin n} (hij : i ≠ j) {c c' : E} (hc : c ∈ K i) (hc' : c' ∈ K j) :
    Disjoint (ball c r) (ball c' r) := by
  refine Set.disjoint_left.mpr fun z hz hz' => ?_
  have h1 : δ ≤ dist c c' := hgap i j hij c hc c' hc'
  have h2 : dist z c < r := mem_ball.mp hz
  have h3 : dist z c' < r := mem_ball.mp hz'
  have : dist c c' ≤ dist c z + dist z c' := dist_triangle c z c'
  rw [dist_comm z c] at h2
  linarith

/-- **Assembly: the cross-piece disjoint cap system.** Pairwise-disjoint compacts have a gap
`δ > 0` such that for every radius `r` with `0 < r` and `2 * r ≤ δ` there are finite centre
sets `t i ⊆ K i` whose radius-`r` balls cover `K i`, miss every other core, and are pairwise
disjoint across distinct cores. -/
theorem exists_disjoint_cap_system
    {K : Fin n → Set E} (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise fun i j => Disjoint (K i) (K j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → 2 * r ≤ δ →
      ∃ t : Fin n → Set E, (∀ i, t i ⊆ K i) ∧ (∀ i, (t i).Finite) ∧
        (∀ i, K i ⊆ ⋃ c ∈ t i, ball c r) ∧
        (∀ i j, j ≠ i → ∀ c ∈ t i, Disjoint (ball c r) (K j)) ∧
        (∀ i j, i ≠ j → ∀ c ∈ t i, ∀ c' ∈ t j, Disjoint (ball c r) (ball c' r)) := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_gap_of_pairwise_disjoint_isCompact hK hdisj
  refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
  have hrδ' : r ≤ δ := by linarith
  choose t hts htf htc htd using
    exists_finite_ball_cover_of_gap hK hr hrδ' hgap
  exact ⟨t, hts, htf, htc, fun i j hji c hc => htd i c hc j hji,
    fun i j hij c hc c' hc' =>
      ball_disjoint_ball_of_gap hrδ hgap hij (hts i hc) (hts j hc')⟩

end MeasureToMeasure.Leaves
