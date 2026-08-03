import MeasureToMeasure.Leaves.CompactCore
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# The tuned cap system over disjoint compact cores (lemma 5.4, G8 Phase-1 instantiation)

`staged_prefix_of_separated_caps` demands cap data satisfying a hard separation dichotomy
(`hsep`): every earlier staging ball is either swallowed by a later cap's collapse ball with the
same label, or clears its gate ball. This file produces such data from any pairwise-disjoint
family of compact cores on the sphere, together with cells covering the cores up to a prescribed
mass budget.

**The tuning.** The G4 cap cover (`disjoint_compacts_cap_cover`) gives finitely many centres
per core whose radius-`r` balls cover the core; the point gap
(`exists_pos_gap_of_pairwise_disjoint_isCompact`) keeps distinct cores `δ`-apart, and `r` is
chosen below both thresholds. Three per-cap tunings then realize the dichotomy and the mass
bound simultaneously:

* the collapse radius `aR k` is picked in `(r, 3r/2)` OFF the finite set of centre distances
  `dist (c j) (c k)`, giving a positive margin `m k` around it, so every centre pair is
  decisively close (`≤ aR k - m k`, forcing same core since `aR k < 2r ≤ δ`) or far
  (`≥ aR k + m k`);
* the gate radius `bR k` is pinched into `(aR k, aR k + m k / 2]` so close pairs capture with a
  `ρ`-margin and far pairs clear the gate with one, uniformly for every staging radius
  `ρ ≤ ρ₀ := min over k of m k / 2`;
* `bR k` is additionally pinched by measure continuity from above so the thin annulus
  `{aR k < dist < bR k}` carries mass at most `η / (L + 1)`: the only mass the greedy cells
  `E k := (core ∩ closedBall (c k) (aR k)) \ earlier gates` can lose, so the cells cover the
  cores up to total mass `η`.
-/

set_option autoImplicit false

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- **The tuned cap system.** From pairwise-disjoint compact cores on the sphere and a mass
budget `η > 0`: finitely many caps (on-sphere centres `c k` in core `lab k`, collapse radii
`aR k`, gate radii `bR k`) and measurable cells `E k` inside their collapse balls, such that
cells avoid every earlier gate, the staging dichotomy holds for every staging radius `ρ ≤ ρ₀`,
centres are pairwise distinct, and the cells cover the cores up to mass `η`. -/
theorem exists_tuned_cap_system {n : ℕ} (μ : Measure (Eucl d)) [IsFiniteMeasure μ]
    {K : Fin n → Set (Eucl d)} (hK : ∀ i, IsCompact (K i)) (hKs : ∀ i, K i ⊆ sphere d)
    (hdisj : Pairwise fun i j => Disjoint (K i) (K j)) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ (L : ℕ) (c : Fin L → Eucl d) (lab : Fin L → Fin n) (aR bR : Fin L → ℝ)
      (E : Fin L → Set (Eucl d)) (ρ₀ : ℝ),
      0 < ρ₀ ∧
      (∀ k, c k ∈ K (lab k)) ∧
      (∀ k, c k ∈ sphere d) ∧
      (∀ j k : Fin L, j ≠ k → c j ≠ c k) ∧
      (∀ k, 0 < aR k) ∧ (∀ k, aR k < bR k) ∧ (∀ k, bR k ≤ 2) ∧
      (∀ k, MeasurableSet (E k)) ∧
      (∀ k, E k ⊆ K (lab k)) ∧
      (∀ k, E k ⊆ Metric.closedBall (c k) (aR k)) ∧
      (∀ j k : Fin L, j < k → Disjoint (E k) (Metric.ball (c j) (bR j))) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ j k : Fin L, j < k →
        (lab j = lab k ∧ dist (c j) (c k) + ρ ≤ aR k) ∨ bR k + ρ ≤ dist (c j) (c k)) ∧
      μ ((⋃ i, K i) \ ⋃ k, E k) ≤ η := by
  classical
  -- the point gap between distinct cores, and the cap-cover radius threshold
  obtain ⟨δg, hδgpos, hgap⟩ :=
    exists_pos_gap_of_pairwise_disjoint_isCompact (E := Eucl d) hK hdisj
  obtain ⟨δc, hδcpos, hcover⟩ := disjoint_compacts_cap_cover hK hdisj
  set r : ℝ := min (min (δc / 2) (δg / 2)) 1 with hrdef
  have hrpos : 0 < r := lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hr2δc : 2 * r ≤ δc := by
    have h1 : r ≤ δc / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hr2δg : 2 * r ≤ δg := by
    have h1 : r ≤ δg / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hr1 : r ≤ 1 := min_le_right _ _
  obtain ⟨t, hts, htf, htc, _htd, _htdd⟩ := hcover r hrpos hr2δc
  -- enumerate all caps across all cores
  haveI : ∀ i : Fin n, Fintype ((htf i).toFinset : Finset (Eucl d)) := fun _ =>
    FinsetCoe.fintype _
  set L : ℕ := Fintype.card (Σ i : Fin n, ((htf i).toFinset : Finset (Eucl d))) with hLdef
  set e : Fin L ≃ Σ i : Fin n, ((htf i).toFinset : Finset (Eucl d)) :=
    (Fintype.equivFin _).symm with hedef
  set lab : Fin L → Fin n := fun k => (e k).1 with hlabdef
  set c : Fin L → Eucl d := fun k => ((e k).2 : Eucl d) with hcdef
  have hct : ∀ k, c k ∈ t (lab k) := fun k => (htf (lab k)).mem_toFinset.mp (e k).2.2
  have hcK : ∀ k, c k ∈ K (lab k) := fun k => hts (lab k) (hct k)
  have hcs : ∀ k, c k ∈ sphere d := fun k => hKs (lab k) (hcK k)
  have hsigma_inj : ∀ σ τ : Σ i : Fin n, ((htf i).toFinset : Finset (Eucl d)),
      σ.1 = τ.1 → (σ.2 : Eucl d) = (τ.2 : Eucl d) → σ = τ := by
    rintro ⟨i₁, z₁⟩ ⟨i₂, z₂⟩ h1 h2
    dsimp at h1 h2
    subst h1
    exact congrArg _ (Subtype.ext h2)
  have hcne : ∀ j k : Fin L, j ≠ k → c j ≠ c k := by
    intro j k hjk hc
    by_cases hlab : lab j = lab k
    · exact hjk (e.injective (hsigma_inj (e j) (e k) hlab hc))
    · exact Set.disjoint_left.mp (hdisj hlab) (hcK j) (hc ▸ hcK k)
  -- collapse radii off the finite distance sets, with margins
  have haRex : ∀ k : Fin L, ∃ a : ℝ, a ∈ Set.Ioo r (3 / 2 * r) ∧
      ∀ j : Fin L, dist (c j) (c k) ≠ a := by
    intro k
    have hinf : (Set.Ioo r (3 / 2 * r)).Infinite := Set.Ioo_infinite (by linarith)
    obtain ⟨a, ha⟩ := (hinf.sdiff (Set.finite_range fun j => dist (c j) (c k))).nonempty
    exact ⟨a, ha.1, fun j hj => ha.2 ⟨j, hj⟩⟩
  choose aR haRmem haRoff using haRex
  have haRpos : ∀ k, 0 < aR k := fun k => lt_trans hrpos (haRmem k).1
  set m : Fin L → ℝ := fun k =>
    min (Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ fun j => |dist (c j) (c k) - aR k|) (r / 2)
    with hmdef
  have hmpos : ∀ k, 0 < m k := by
    intro k
    refine lt_min ((Finset.lt_inf'_iff _).mpr fun j _ => ?_) (by positivity)
    rw [abs_pos, sub_ne_zero]
    exact haRoff k j
  have hmr : ∀ k, m k ≤ r / 2 := fun k => min_le_right _ _
  have hmargin : ∀ j k : Fin L, m k ≤ |dist (c j) (c k) - aR k| := fun j k =>
    le_trans (min_le_left _ _) (Finset.inf'_le _ (Finset.mem_univ j))
  -- gate radii: pinched by the margin and by annulus-mass continuity from above
  have hbRex : ∀ k : Fin L, ∃ b : ℝ, aR k < b ∧ b ≤ aR k + m k / 2 ∧
      μ {z : Eucl d | aR k < dist z (c k) ∧ dist z (c k) < b} ≤ η / (L + 1) := by
    intro k
    have hmk := hmpos k
    set S : ℕ → Set (Eucl d) := fun N =>
      {z : Eucl d | aR k < dist z (c k) ∧ dist z (c k) < aR k + m k / 2 / (N + 1)} with hSdef
    have hSanti : Antitone S := by
      intro N₁ N₂ h12 z hz
      refine ⟨hz.1, lt_of_lt_of_le hz.2 ?_⟩
      have h2 : ((N₁ : ℝ) + 1) ≤ (N₂ : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h12
      gcongr
    have hSempty : ⋂ N, S N = ∅ := by
      ext z
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      by_cases hz : aR k < dist z (c k)
      · have hpos : 0 < dist z (c k) - aR k := by linarith
        obtain ⟨N, hN⟩ := exists_nat_gt (m k / 2 / (dist z (c k) - aR k))
        refine ⟨N, fun hmem => ?_⟩
        have h2 := hmem.2
        have hN1 : m k / 2 / (dist z (c k) - aR k) < (N : ℝ) + 1 := by linarith
        rw [div_lt_iff₀ hpos] at hN1
        have h3 : m k / 2 / ((N : ℝ) + 1) < dist z (c k) - aR k := by
          rw [div_lt_iff₀ (by positivity)]
          linarith
        linarith
      · exact ⟨0, fun hmem => hz hmem.1⟩
    have hSmeas : ∀ N, MeasurableSet (S N) := by
      intro N
      have h1 : Measurable fun z : Eucl d => dist z (c k) :=
        (continuous_id.dist continuous_const).measurable
      exact (measurableSet_lt measurable_const h1).inter (measurableSet_lt h1 measurable_const)
    have htend : Filter.Tendsto (fun N => μ (S N)) Filter.atTop (nhds (μ (⋂ N, S N))) :=
      tendsto_measure_iInter_atTop (fun N => (hSmeas N).nullMeasurableSet) hSanti
        ⟨0, measure_ne_top μ _⟩
    rw [hSempty, measure_empty] at htend
    have hqpos : 0 < η / ((L : ℝ≥0∞) + 1) := ENNReal.div_pos hη.ne' (by simp)
    obtain ⟨N, hN⟩ := (htend.eventually_lt_const hqpos).exists
    refine ⟨aR k + m k / 2 / (N + 1), ?_, ?_, ?_⟩
    · have hm2 : 0 < m k / 2 / ((N : ℝ) + 1) := by positivity
      linarith
    · have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      have h2 : m k / 2 / ((N : ℝ) + 1) ≤ m k / 2 := div_le_self (by positivity) h1
      linarith
    · exact hN.le
  choose bR hbR₁ hbR₂ hbR₃ using hbRex
  -- the cells: greedy within each core's collapse balls, avoiding every earlier gate
  set E : Fin L → Set (Eucl d) := fun k =>
    (K (lab k) ∩ Metric.closedBall (c k) (aR k)) \
      ⋃ j ∈ {j : Fin L | j < k}, Metric.ball (c j) (bR j) with hEdef
  have hEmeas : ∀ k, MeasurableSet (E k) := by
    intro k
    refine ((hK (lab k)).isClosed.measurableSet.inter measurableSet_closedBall).diff ?_
    exact MeasurableSet.biUnion (Set.to_countable _) fun j _ => measurableSet_ball
  have hEK : ∀ k, E k ⊆ K (lab k) := fun k z hz => hz.1.1
  have hEball : ∀ k, E k ⊆ Metric.closedBall (c k) (aR k) := fun k z hz => hz.1.2
  have hEavoid : ∀ j k : Fin L, j < k → Disjoint (E k) (Metric.ball (c j) (bR j)) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro z hz hzball
    exact hz.2 (Set.mem_biUnion hjk hzball)
  -- radius bookkeeping
  have haR32 : ∀ k, aR k < 3 / 2 * r := fun k => (haRmem k).2
  have hb2 : ∀ k, bR k ≤ 2 := by
    intro k
    have h1 := hbR₂ k
    have h2 := haR32 k
    have h3 := hmr k
    linarith [hr1]
  have hblt2r : ∀ k, bR k + r / 4 ≤ 2 * r := by
    intro k
    have h1 := hbR₂ k
    have h2 := haR32 k
    have h3 := hmr k
    linarith
  -- the uniform staging-radius threshold
  set ρ₀ : ℝ := if hL : Nonempty (Fin L) then
      Finset.univ.inf' (Finset.univ_nonempty_iff.mpr hL) (fun k => m k / 2) else 1 with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀def]
    split_ifs with hL
    · exact (Finset.lt_inf'_iff _).mpr fun k _ => by have := hmpos k; positivity
    · exact one_pos
  have hρ₀m : ∀ k : Fin L, ρ₀ ≤ m k / 2 := by
    intro k
    rw [hρ₀def, dif_pos ⟨k⟩]
    exact Finset.inf'_le _ (Finset.mem_univ k)
  -- the separation dichotomy, uniformly in the staging radius
  have hsep : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ j k : Fin L, j < k →
      (lab j = lab k ∧ dist (c j) (c k) + ρ ≤ aR k) ∨ bR k + ρ ≤ dist (c j) (c k) := by
    intro ρ hρpos hρle j k hjk
    have hmarg := hmargin j k
    have hρm : ρ ≤ m k / 2 := le_trans hρle (hρ₀m k)
    rcases lt_or_ge (dist (c j) (c k)) (aR k) with hlt | hge
    · left
      have habs : |dist (c j) (c k) - aR k| = aR k - dist (c j) (c k) := by
        rw [abs_of_neg (by linarith)]
        ring
      rw [habs] at hmarg
      constructor
      · by_contra hlab
        have hfar : δg ≤ dist (c j) (c k) :=
          hgap (lab j) (lab k) hlab (c j) (hcK j) (c k) (hcK k)
        have h2 := haR32 k
        linarith [hr2δg]
      · linarith
    · right
      have habs : |dist (c j) (c k) - aR k| = dist (c j) (c k) - aR k := by
        rw [abs_of_nonneg (by linarith)]
      rw [habs] at hmarg
      have := hbR₂ k
      linarith
  -- coverage: everything the cells miss sits in a thin annulus
  have hlost : (⋃ i, K i) \ (⋃ k, E k) ⊆
      ⋃ k, {z : Eucl d | aR k < dist z (c k) ∧ dist z (c k) < bR k} := by
    intro x hx
    obtain ⟨hxK, hxE⟩ := hx
    rw [Set.mem_iUnion] at hxK
    obtain ⟨i, hxi⟩ := hxK
    have hxcov := htc i hxi
    rw [Set.mem_iUnion₂] at hxcov
    obtain ⟨c₀, hc₀t, hc₀ball⟩ := hxcov
    have hk₀mem : c₀ ∈ (htf i).toFinset := (htf i).mem_toFinset.mpr hc₀t
    set k₀ : Fin L := e.symm ⟨i, ⟨c₀, hk₀mem⟩⟩ with hk₀def
    have hek₀ : e k₀ = ⟨i, ⟨c₀, hk₀mem⟩⟩ := e.apply_symm_apply _
    have hk₀lab : lab k₀ = i := by simp only [hlabdef]; rw [hek₀]
    have hk₀c : c k₀ = c₀ := by simp only [hcdef]; rw [hek₀]
    set F : Finset (Fin L) :=
      Finset.univ.filter (fun k => lab k = i ∧ x ∈ Metric.closedBall (c k) (aR k)) with hFdef
    have hk₀F : k₀ ∈ F := by
      rw [hFdef, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hk₀lab, ?_⟩
      rw [Metric.mem_closedBall, hk₀c]
      have h1 : dist x c₀ < r := Metric.mem_ball.mp hc₀ball
      have h2 : r < aR k₀ := (haRmem k₀).1
      linarith
    set kmin : Fin L := F.min' ⟨k₀, hk₀F⟩ with hkmindef
    have hkminF : kmin ∈ F := F.min'_mem _
    rw [hFdef, Finset.mem_filter] at hkminF
    obtain ⟨-, hkminlab, hkminball⟩ := hkminF
    rw [Set.mem_iUnion]
    by_contra hxann
    push_neg at hxann
    apply hxE
    rw [Set.mem_iUnion]
    refine ⟨kmin, ⟨⟨by rw [hkminlab]; exact hxi, hkminball⟩, ?_⟩⟩
    intro hmem
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
    obtain ⟨j, hjlt, hjball⟩ := hmem
    have hjdist : dist x (c j) < bR j := Metric.mem_ball.mp hjball
    by_cases hjlab : lab j = i
    · by_cases hjclose : x ∈ Metric.closedBall (c j) (aR j)
      · have hjF : j ∈ F := by
          rw [hFdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hjlab, hjclose⟩
        exact absurd (F.min'_le j hjF) (not_le.mpr hjlt)
      · rw [Metric.mem_closedBall, not_le] at hjclose
        exact hxann j ⟨hjclose, hjdist⟩
    · have hfar : δg ≤ dist x (c j) :=
        hgap i (lab j) (fun h => hjlab h.symm) x hxi (c j) (hcK j)
      have hb := hblt2r j
      linarith [hr2δg]
  -- the mass ledger
  have hmass : μ ((⋃ i, K i) \ ⋃ k, E k) ≤ η := by
    calc μ ((⋃ i, K i) \ ⋃ k, E k)
        ≤ μ (⋃ k, {z : Eucl d | aR k < dist z (c k) ∧ dist z (c k) < bR k}) :=
          measure_mono hlost
      _ ≤ ∑ k, μ {z : Eucl d | aR k < dist z (c k) ∧ dist z (c k) < bR k} := by
          refine le_trans (measure_iUnion_le _) ?_
          rw [tsum_fintype]
      _ ≤ ∑ _k : Fin L, η / (L + 1) := Finset.sum_le_sum fun k _ => hbR₃ k
      _ = (L : ℝ≥0∞) * (η / (L + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((L : ℝ≥0∞) + 1) * (η / ((L : ℝ≥0∞) + 1)) := by
          gcongr
          exact le_self_add
      _ ≤ η := ENNReal.mul_div_le
  exact ⟨L, c, lab, aR, bR, E, ρ₀, hρ₀pos, hcK, hcs, hcne, haRpos, hbR₁, hb2, hEmeas, hEK,
    hEball, hEavoid, hsep, hmass⟩

end MeasureToMeasure.Leaves
