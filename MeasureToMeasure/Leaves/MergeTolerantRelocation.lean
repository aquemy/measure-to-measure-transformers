import MeasureToMeasure.Leaves.CellStagingInduction
import MeasureToMeasure.Leaves.PoleGeometry

/-!
# Leaves (lemma 5.4 campaign, G7): merge-tolerant relocation

Phase 2 of the `lemma_5_4` discharge moves each Phase-1 staging ball's mass into a small ball
around its own target `z (k i)`, where targets may REPEAT (several cells share one value of the
finite-range approximation). Merging dissolves into perturbed landing poles: each arriving ball
gets its own fresh landing site inside the target's `δ/2`-ball, disjoint from every ball already
placed there and from every staged ball not yet moved.

This file's first leaf, `exists_landing_pole_avoiding`, is that landing-site geometry: near any
sphere point `z` there is an on-sphere pole `z'` and a radius `r' > 0` with
`closedBall z' r' ⊆ ball z (δ/2)` clear of ANY finite pairwise-disjoint family of closed balls of
radius `< δ/8`. The proof rides a quarter-circle arc `b ↦ √(1-b²) • z + b • w` (`w ⊥ z` a unit
vector, the only consumer of `2 ≤ d`): the arc is connected, stays within `√2·δ/4 < δ/2` of `z`,
and its endpoints are `≥ δ/4` apart, so no single avoided ball (diameter `< δ/4`) contains it;
pairwise disjointness then makes a finite cover of the arc by the closed balls impossible, because
a preconnected set covered by two disjoint closed sets lies inside one of them. A free arc point
plus openness of the complement yields the landing ball.

Both smallness hypotheses are necessary, not artifacts. Without pairwise disjointness, many balls
of radius just under `δ/8` can tile the whole `δ/2`-cap. Without a bound like `δ ≤ 4`, a single
ball centered at the origin with radius `< δ/8` can swallow the entire sphere. Phase 2's consumers
control both: avoided balls are staging and landing balls whose radii shrink at will, and a large
`δ` target can always be shrunk before landing.

The second and third leaves are Phase 2's transport engine. `exists_relocation_hop_chain` moves a
single staged ball along a GIVEN chain of hop centres, one `exists_staging_collapse_step` block
per hop, exactly fixing everything disjoint from the hop gate balls; because the collapse is
support-level and exact, no retention budget accumulates between hops, which is precisely the
tension that blocked the prop_2_2 arc-chain machinery's multi-hop induction.
`exists_merge_tolerant_relocation` runs these chains for all staged balls in index order with the
avoid set growing by one landing ball per step: each chain's gates clear the not yet moved source
balls and the already placed landing balls, so every tracked unit is handled by exactly one clause
per step. Corridor data (the chains and their avoidance) enters as a HYPOTHESIS bundle: producing
it, i.e. hop chains between prescribed sphere points clearing finitely many shrinkable closed
balls, is the one remaining geometric obligation of the campaign and lives with the G8 assembly.
-/

set_option autoImplicit false

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **A fresh landing pole near `z`, avoiding finitely many pairwise-disjoint tiny balls.** For
`z ∈ 𝕊^{d-1}`, `0 < δ ≤ 4`, and closed balls `closedBall (p i) (r i)`, `i : Fin n`, pairwise
disjoint with `r i < δ/8`: there is an on-sphere pole `z'` and a radius `r' > 0` whose closed ball
sits inside `Metric.ball z (δ/2)` and misses every listed ball. Centers `p i` are arbitrary points
of the ambient space. The pole is found on the arc towards a unit `w ⊥ z` (whence `2 ≤ d`); a
finite pairwise-disjoint family of closed sets cannot cover a connected arc unless one member
contains it, and each ball is too small to do so. -/
theorem exists_landing_pole_avoiding (hd : 2 ≤ d) {z : Eucl d} (hz : z ∈ sphere d)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 4) {n : ℕ} (p : Fin n → Eucl d) (r : Fin n → ℝ)
    (hr : ∀ i, r i < δ / 8)
    (hdisj : ∀ i j : Fin n, i ≠ j →
      Disjoint (Metric.closedBall (p i) (r i)) (Metric.closedBall (p j) (r j))) :
    ∃ (z' : Eucl d) (r' : ℝ), z' ∈ sphere d ∧ 0 < r' ∧
      Metric.closedBall z' r' ⊆ Metric.ball z (δ / 2) ∧
      ∀ i, Disjoint (Metric.closedBall z' r') (Metric.closedBall (p i) (r i)) := by
  have hzn : ‖z‖ = 1 := norm_eq_one_of_mem_sphere hz
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hzn; exact zero_ne_one hzn
  obtain ⟨w, hzw, hw⟩ := exists_unit_orthogonal hd hz0
  set b0 : ℝ := δ / 4 with hb0def
  have hb0pos : 0 < b0 := by positivity
  have hb01 : b0 ≤ 1 := by rw [hb0def]; linarith
  set γ : ℝ → Eucl d := fun b => Real.sqrt (1 - b ^ 2) • z + b • w with hγdef
  -- pointwise arc facts: on the sphere, with chordal distance to `z` given by `2 - 2√(1-b²)`
  have harc : ∀ b : ℝ, 0 ≤ b → b ≤ b0 →
      γ b ∈ sphere d ∧ dist (γ b) z ^ 2 = 2 - 2 * Real.sqrt (1 - b ^ 2) := by
    intro b hb0' hbb0
    have hb1 : b ≤ 1 := le_trans hbb0 hb01
    have h1b : (0:ℝ) ≤ 1 - b ^ 2 := by nlinarith
    have hs : Real.sqrt (1 - b ^ 2) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt h1b
    have hsnn : 0 ≤ Real.sqrt (1 - b ^ 2) := Real.sqrt_nonneg _
    set s : ℝ := Real.sqrt (1 - b ^ 2) with hsdef
    have hγb : γ b = s • z + b • w := rfl
    have hnormsq : ‖γ b‖ ^ 2 = 1 := by
      rw [hγb, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hzw,
        norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hzn, hw]
      rw [abs_of_nonneg hsnn]
      nlinarith [abs_nonneg b, sq_abs b]
    have hmem : γ b ∈ sphere d := by
      have hn : ‖γ b‖ = 1 := by nlinarith [norm_nonneg (γ b)]
      simpa [MeasureToMeasure.sphere, Metric.mem_sphere, dist_zero_right] using hn
    refine ⟨hmem, ?_⟩
    have hdiff : γ b - z = (s - 1) • z + b • w := by
      rw [hγb, sub_smul, one_smul]; abel
    rw [dist_eq_norm, hdiff, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
      hzw, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hzn, hw]
    have habs : |s - 1| ^ 2 = (s - 1) ^ 2 := sq_abs _
    nlinarith [sq_abs b]
  have hcont : Continuous γ := by
    apply Continuous.add
    · exact (Real.continuous_sqrt.comp (by continuity)).smul continuous_const
    · exact continuous_id.smul continuous_const
  have hγ0 : γ 0 = z := by
    simp [hγdef, Real.sqrt_one]
  -- the arc: a preconnected subset of the sphere near `z`
  set A : Set (Eucl d) := γ '' Set.Icc 0 b0 with hAdef
  have hpre : IsPreconnected A := isPreconnected_Icc.image γ hcont.continuousOn
  have hzA : z ∈ A := ⟨0, ⟨le_rfl, hb0pos.le⟩, hγ0⟩
  -- the finitely many pairwise-disjoint tiny balls cannot cover the arc
  have hnotcov : ¬ (A ⊆ ⋃ i, Metric.closedBall (p i) (r i)) := by
    intro hcov
    obtain ⟨i0, hzi0⟩ := Set.mem_iUnion.mp (hcov hzA)
    set C1 : Set (Eucl d) := Metric.closedBall (p i0) (r i0) with hC1def
    set C2 : Set (Eucl d) := ⋃ i ∈ {i : Fin n | i ≠ i0}, Metric.closedBall (p i) (r i)
      with hC2def
    have hAC12 : A ⊆ C1 ∪ C2 := by
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov hx)
      by_cases hii0 : i = i0
      · subst hii0
        exact Or.inl hxi
      · exact Or.inr (Set.mem_biUnion hii0 hxi)
    have hC2closed : IsClosed C2 :=
      Set.Finite.isClosed_biUnion (Set.toFinite _) fun i _ => Metric.isClosed_closedBall
    have hU : IsOpen C2ᶜ := hC2closed.isOpen_compl
    have hV : IsOpen C1ᶜ := Metric.isClosed_closedBall.isOpen_compl
    have hsubUV : A ⊆ C2ᶜ ∪ C1ᶜ := by
      intro x hx
      by_cases hx2 : x ∈ C2
      · obtain ⟨i, hine, hxi⟩ := by
          simpa [hC2def, Set.mem_iUnion] using hx2
        refine Or.inr fun hx1 => ?_
        exact Set.disjoint_left.mp (hdisj i i0 hine) hxi hx1
      · exact Or.inl hx2
    have hinter : A ∩ (C2ᶜ ∩ C1ᶜ) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hxA, hx2, hx1⟩
      rcases hAC12 hxA with h | h
      · exact hx1 h
      · exact hx2 h
    have hnot : ¬((A ∩ C2ᶜ).Nonempty ∧ (A ∩ C1ᶜ).Nonempty) := by
      rintro ⟨h1, h2⟩
      have := hpre C2ᶜ C1ᶜ hU hV hsubUV h1 h2
      rw [hinter] at this
      exact Set.not_nonempty_empty this
    rcases not_and_or.mp hnot with h1 | h2
    · -- the arc lies in the other balls: `z` then sits in one of them AND in ball `i0`
      have hAC2 : A ⊆ C2 := by
        intro x hx
        by_contra hx2
        exact h1 ⟨x, hx, hx2⟩
      obtain ⟨i, hine, hzi⟩ := by
        simpa [hC2def, Set.mem_iUnion] using hAC2 hzA
      exact Set.disjoint_left.mp (hdisj i i0 hine) hzi hzi0
    · -- the arc lies in ball `i0`: both endpoints inside one tiny ball, yet `δ/4` apart
      have hAC1 : A ⊆ C1 := by
        intro x hx
        by_contra hx1
        exact h2 ⟨x, hx, hx1⟩
      have hb0A : γ b0 ∈ A := ⟨b0, ⟨hb0pos.le, le_rfl⟩, rfl⟩
      have hzC1 : z ∈ C1 := hAC1 hzA
      have hb0C1 : γ b0 ∈ C1 := hAC1 hb0A
      have hup : Real.sqrt (1 - b0 ^ 2) ≤ 1 - b0 ^ 2 / 2 := by
        have h1 : (1 - b0 ^ 2 : ℝ) ≤ (1 - b0 ^ 2 / 2) ^ 2 := by nlinarith
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by nlinarith)] at h2
      obtain ⟨_, hdistsq⟩ := harc b0 hb0pos.le le_rfl
      have hfar : b0 ≤ dist (γ b0) z := by
        nlinarith [dist_nonneg (x := γ b0) (y := z)]
      have hclose1 : dist (γ b0) (p i0) ≤ r i0 := Metric.mem_closedBall.mp hb0C1
      have hclose2 : dist (p i0) z ≤ r i0 := by
        rw [dist_comm]
        exact Metric.mem_closedBall.mp hzC1
      have htri := dist_triangle (γ b0) (p i0) z
      have := hr i0
      rw [hb0def] at hfar
      linarith
  obtain ⟨x0, hx0A, hx0free⟩ := Set.not_subset.mp hnotcov
  obtain ⟨b, hbmem, hbx⟩ := hx0A
  obtain ⟨hx0sphere, hx0distsq⟩ := by
    have := harc b hbmem.1 hbmem.2
    rwa [hbx] at this
  -- the free point is strictly within `δ/2` of `z`
  have hlow : 1 - b ^ 2 ≤ Real.sqrt (1 - b ^ 2) := by
    have hb1 : b ≤ 1 := le_trans hbmem.2 hb01
    have h1b : (0:ℝ) ≤ 1 - b ^ 2 := by nlinarith [hbmem.1]
    have h1 : ((1 - b ^ 2) : ℝ) ^ 2 ≤ 1 - b ^ 2 := by nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq h1b] at h2
  have hx0close : dist x0 z < δ / 2 := by
    have hb0b : b ≤ b0 := hbmem.2
    have hsq : dist x0 z ^ 2 ≤ 2 * b ^ 2 := by nlinarith
    by_contra hcon
    have hge : δ / 2 ≤ dist x0 z := not_lt.mp hcon
    rw [hb0def] at hb0b
    nlinarith [dist_nonneg (x := x0) (y := z), hbmem.1]
  -- an open ball around the free point clear of the closed union
  have hclosedU : IsClosed (⋃ i, Metric.closedBall (p i) (r i)) :=
    isClosed_iUnion_of_finite fun i => Metric.isClosed_closedBall
  obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp hclosedU.isOpen_compl x0 hx0free
  refine ⟨x0, min (ε / 2) ((δ / 2 - dist x0 z) / 2), hx0sphere, ?_, ?_, ?_⟩
  · exact lt_min (by positivity) (by linarith)
  · intro y hy
    have hyx0 : dist y x0 ≤ (δ / 2 - dist x0 z) / 2 :=
      le_trans (Metric.mem_closedBall.mp hy) (min_le_right _ _)
    have := dist_triangle y x0 z
    rw [Metric.mem_ball]
    linarith
  · intro i
    rw [Set.disjoint_left]
    intro y hy hyi
    have hyx0 : dist y x0 ≤ ε / 2 := le_trans (Metric.mem_closedBall.mp hy) (min_le_left _ _)
    have hyball : y ∈ Metric.ball x0 ε := by
      rw [Metric.mem_ball]
      linarith
    exact hεball hyball (Set.mem_iUnion.mpr ⟨i, hyi⟩)

variable [NeZero d]

/-- **Single-ball relocation along a given hop chain.** For on-sphere hop centres
`w 0, …, w M`, a staging radius `ρ > 0`, and per-hop capture/gate radii `a t < b t ≤ 2` with
`dist (w t.succ) (w t.castSucc) + ρ ≤ a t`, one staging-collapse block per hop yields a schedule
of duration exactly `M * τ` that drives every sphere probability measure carried by
`Metric.ball (w 0) ρ` into `Metric.ball (w (Fin.last M)) ρ`, while EXACTLY fixing every sphere
probability measure supported in a set disjoint from all the hop gate balls
`Metric.ball (w t.succ) (b t)`. Induction over the hop prefix: after `K` hops the tracked mass
occupies `Metric.ball (w K) ρ`, which the capture bound places inside the next hop's collapse
ball; `exists_staging_collapse_step` does one hop. There is NO tension between consecutive hops:
the support-level collapse is exact, so no retention budget accumulates (contrast the prop_2_2
arc-chain machinery, where exactly such a budget blocked the multi-hop induction). -/
theorem exists_relocation_hop_chain {M : ℕ} (w : Fin (M + 1) → Eucl d)
    (hw : ∀ t, w t ∈ sphere d) {ρ : ℝ} (hρ : 0 < ρ) (a b : Fin M → ℝ)
    (hcap : ∀ t : Fin M, dist (w t.succ) (w t.castSucc) + ρ ≤ a t)
    (hab : ∀ t, a t < b t) (hb2 : ∀ t, b t ≤ 2) {τ : ℝ} (hτ : 0 < τ) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = (M : ℝ) * τ ∧
      (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        supportedIn ν (Metric.ball (w 0) ρ) →
        supportedIn (attnMeasureFlow θ ν) (Metric.ball (w (Fin.last M)) ρ)) ∧
      (∀ F : Set (Eucl d), (∀ t : Fin M, Disjoint F (Metric.ball (w t.succ) (b t))) →
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        supportedIn ν F → attnMeasureFlow θ ν = ν) := by
  have key : ∀ K : ℕ, K ≤ M → ∃ θ : AttnSchedule d,
      AttnSchedule.durationSum θ = (K : ℝ) * τ ∧
      (∀ hK : K < M + 1, ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] →
        supportedIn ν (sphere d) → supportedIn ν (Metric.ball (w 0) ρ) →
        supportedIn (attnMeasureFlow θ ν) (Metric.ball (w ⟨K, hK⟩) ρ)) ∧
      (∀ F : Set (Eucl d), (∀ t : Fin M, (t : ℕ) < K → Disjoint F (Metric.ball (w t.succ) (b t))) →
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        supportedIn ν F → attnMeasureFlow θ ν = ν) := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨[], by simp, ?_, ?_⟩
      · intro hK ν _ _ hν0
        have h0 : (⟨0, hK⟩ : Fin (M + 1)) = 0 := rfl
        rw [h0]
        exact hν0
      · intro F _ ν _ _ _
        rfl
    | succ K ih =>
      intro hK1
      have hKM : K < M := hK1
      obtain ⟨θ, hθdur, hmove, hfix⟩ := ih (Nat.le_of_lt hKM)
      set t : Fin M := ⟨K, hKM⟩ with htdef
      have ha0 : 0 < a t := lt_of_lt_of_le (by positivity) (le_trans (by
        have := dist_nonneg (x := w t.succ) (y := w t.castSucc)
        linarith) (hcap t))
      obtain ⟨p, hpdur, hpcol, hpfix, hpfixF⟩ :=
        exists_staging_collapse_step (hw t.succ) ha0 (hab t) (hb2 t) hτ hρ
      refine ⟨θ ++ [p], ?_, ?_, ?_⟩
      · rw [AttnSchedule.durationSum_append, hθdur]
        have hsing : AttnSchedule.durationSum [p] = p.duration := by
          simp [AttnSchedule.durationSum]
        rw [hsing, hpdur]
        push_cast
        ring
      · -- move: capture the previous staging ball and collapse at the next centre
        intro hK ν _hprob hνs hν0
        haveI : IsProbabilityMeasure (attnMeasureFlow θ ν) :=
          isProbabilityMeasure_attnMeasureFlow θ ν hνs
        have hν's : supportedIn (attnMeasureFlow θ ν) (sphere d) :=
          attnMeasureFlow_supportedIn_sphere θ ν hνs
        have hprev : supportedIn (attnMeasureFlow θ ν) (Metric.ball (w ⟨K, by omega⟩) ρ) :=
          hmove (by omega) ν hνs hν0
        have hclosed : supportedIn (attnMeasureFlow θ ν)
            (Metric.closedBall (w t.succ) (a t)) := by
          refine supportedIn_mono (fun x hx => ?_) hprev
          rw [Metric.mem_ball] at hx
          rw [Metric.mem_closedBall]
          have hcast : w t.castSucc = w ⟨K, by omega⟩ := rfl
          have htri := dist_triangle x (w t.castSucc) (w t.succ)
          have hd2 := hcap t
          rw [dist_comm (w t.succ) (w t.castSucc)] at hd2
          rw [hcast] at htri hd2
          linarith
        rw [attnMeasureFlow_append]
        have hsucc : (⟨K + 1, hK⟩ : Fin (M + 1)) = t.succ := rfl
        rw [hsucc]
        exact hpcol (attnMeasureFlow θ ν) hν's hclosed
      · -- fixing: one more gate absorbed
        intro F hF ν _hprob hνs hνF
        have hfixed : attnMeasureFlow θ ν = ν :=
          hfix F (fun s hs => hF s (Nat.lt_succ_of_lt hs)) ν hνs hνF
        rw [attnMeasureFlow_append, hfixed]
        exact hpfixF F (hF t (Nat.lt_succ_self K)) ν hνs hνF
  obtain ⟨θ, hθdur, hmove, hfix⟩ := key M le_rfl
  refine ⟨θ, hθdur, ?_, ?_⟩
  · intro ν _hprob hνs hν0
    have hlast : (Fin.last M) = (⟨M, by omega⟩ : Fin (M + 1)) := rfl
    rw [hlast]
    exact hmove (by omega) ν hνs hν0
  · intro F hF ν _hprob hνs hνF
    exact hfix F (fun s _ => hF s) ν hνs hνF

/-- **The merge-tolerant relocation engine: all staged balls delivered, corridors given as
data.** Balls are processed in index order; ball `i` follows its own hop chain
`w i 0, …, w i (Mc i)` (`exists_relocation_hop_chain`), whose gate balls avoid every not yet
moved source ball (`hgate_src`) and every already placed landing ball (`hgate_land`), so at
every step each tracked unit is handled by exactly one clause: fixed at its source before its
turn, moved by its own chain on its turn, fixed at its landing ball afterwards. Targets `z j`
may REPEAT: the hypotheses force pairwise-disjoint landing balls even for equal targets, which
is exactly what `exists_landing_pole_avoiding` produces when the corridors are built. Total
duration is exactly `(∑ i, Mc i) * τ`; off-corridor mass is fixed EXACTLY.

The corridor data `w`, `a`, `b` with `hgate_src`/`hgate_land` is a HYPOTHESIS here, not a
construction: this leaf is the avoidance-composition engine, and the remaining (independent,
purely geometric) obligation of the G7 campaign is corridor EXISTENCE, i.e. producing hop
chains between prescribed endpoints on the sphere that clear finitely many shrinkable closed
balls. See the campaign notes in the pull request for the precise obligation shape. -/
theorem exists_merge_tolerant_relocation {N : ℕ}
    (Mc : Fin N → ℕ) (w : ∀ i, Fin (Mc i + 1) → Eucl d)
    (hw : ∀ i t, w i t ∈ sphere d) {ρ : ℝ} (hρ : 0 < ρ)
    (a b : ∀ i, Fin (Mc i) → ℝ)
    (hcap : ∀ i (t : Fin (Mc i)), dist (w i t.succ) (w i t.castSucc) + ρ ≤ a i t)
    (hab : ∀ i t, a i t < b i t) (hb2 : ∀ i t, b i t ≤ 2)
    (hgate_src : ∀ i j : Fin N, i < j → ∀ t : Fin (Mc i),
      Disjoint (Metric.ball (w i t.succ) (b i t)) (Metric.ball (w j 0) ρ))
    (hgate_land : ∀ i j : Fin N, j < i → ∀ t : Fin (Mc i),
      Disjoint (Metric.ball (w i t.succ) (b i t)) (Metric.ball (w j (Fin.last (Mc j))) ρ))
    (z : Fin N → Eucl d) {δ : ℝ}
    (hland : ∀ j, Metric.ball (w j (Fin.last (Mc j))) ρ ⊆ Metric.ball (z j) δ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = (∑ i, (Mc i : ℝ)) * τ ∧
      (∀ j, ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        supportedIn ν (Metric.ball (w j 0) ρ) →
        supportedIn (attnMeasureFlow θ ν) (Metric.ball (z j) δ)) ∧
      (∀ F : Set (Eucl d),
        (∀ i, ∀ t : Fin (Mc i), Disjoint F (Metric.ball (w i t.succ) (b i t))) →
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        supportedIn ν F → attnMeasureFlow θ ν = ν) := by
  set g : ℕ → ℝ := fun m => if h : m < N then (Mc ⟨m, h⟩ : ℝ) * τ else 0 with hgdef
  have key : ∀ K : ℕ, K ≤ N → ∃ θ : AttnSchedule d,
      AttnSchedule.durationSum θ = ∑ m ∈ Finset.range K, g m ∧
      (∀ j : Fin N, (j : ℕ) < K → ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] →
        supportedIn ν (sphere d) → supportedIn ν (Metric.ball (w j 0) ρ) →
        supportedIn (attnMeasureFlow θ ν) (Metric.ball (w j (Fin.last (Mc j))) ρ)) ∧
      (∀ F : Set (Eucl d),
        (∀ i : Fin N, (i : ℕ) < K → ∀ t : Fin (Mc i),
          Disjoint F (Metric.ball (w i t.succ) (b i t))) →
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        supportedIn ν F → attnMeasureFlow θ ν = ν) := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨[], by simp [AttnSchedule.durationSum], ?_, ?_⟩
      · intro j hj
        exact absurd hj (Nat.not_lt_zero _)
      · intro F _ ν _ _ _
        rfl
    | succ K ih =>
      intro hK1
      have hKN : K < N := hK1
      obtain ⟨θ, hθdur, hmove, hfix⟩ := ih (Nat.le_of_lt hKN)
      set iK : Fin N := ⟨K, hKN⟩ with hiKdef
      obtain ⟨θK, hθKdur, hKmove, hKfix⟩ := exists_relocation_hop_chain (w iK) (hw iK)
        hρ (a iK) (b iK) (hcap iK) (hab iK) (hb2 iK) hτ
      refine ⟨θ ++ θK, ?_, ?_, ?_⟩
      · rw [AttnSchedule.durationSum_append, hθdur, hθKdur, Finset.sum_range_succ]
        have hgK : g K = (Mc iK : ℝ) * τ := dif_pos hKN
        rw [hgK]
      · intro j hj ν _hprob hνs hν0
        haveI : IsProbabilityMeasure (attnMeasureFlow θ ν) :=
          isProbabilityMeasure_attnMeasureFlow θ ν hνs
        have hν's : supportedIn (attnMeasureFlow θ ν) (sphere d) :=
          attnMeasureFlow_supportedIn_sphere θ ν hνs
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjK | hjK
        · -- already placed: the fresh chain's gates avoid the landing ball
          have hplaced := hmove j hjK ν hνs hν0
          rw [attnMeasureFlow_append]
          rw [hKfix (Metric.ball (w j (Fin.last (Mc j))) ρ)
            (fun t => (hgate_land iK j (by rw [Fin.lt_def]; exact hjK) t).symm)
            (attnMeasureFlow θ ν) hν's hplaced]
          exact hplaced
        · -- the fresh ball: fixed so far, then moved by its own chain
          have hjeq : j = iK := Fin.ext hjK
          subst hjeq
          have hfixed : attnMeasureFlow θ ν = ν :=
            hfix (Metric.ball (w iK 0) ρ)
              (fun i hi t => (hgate_src i iK (by rw [Fin.lt_def]; exact hi) t).symm)
              ν hνs hν0
          rw [attnMeasureFlow_append, hfixed]
          exact hKmove ν hνs hν0
      · intro F hF ν _hprob hνs hνF
        have hfixed : attnMeasureFlow θ ν = ν :=
          hfix F (fun i hi t => hF i (Nat.lt_succ_of_lt hi) t) ν hνs hνF
        rw [attnMeasureFlow_append, hfixed]
        exact hKfix F (fun s => hF iK (Nat.lt_succ_self K) s) ν hνs hνF
  obtain ⟨θ, hθdur, hmove, hfix⟩ := key N le_rfl
  refine ⟨θ, ?_, ?_, ?_⟩
  · rw [hθdur, ← Fin.sum_univ_eq_sum_range g N, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgdef]
    simp only [i.isLt, dif_pos, Fin.eta]
  · intro j ν _hprob hνs hν0
    exact supportedIn_mono (hland j) (hmove j j.isLt ν hνs hν0)
  · intro F hF ν _hprob hνs hνF
    exact hfix F (fun i _ s => hF i s) ν hνs hνF

end MeasureToMeasure.Leaves
