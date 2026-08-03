import MeasureToMeasure.Leaves.CellStagingInduction
import MeasureToMeasure.Leaves.L2ErrorAssembly
import MeasureToMeasure.Leaves.MergeTolerantRelocation
import MeasureToMeasure.Leaves.UniversalFlowPointwise
import MeasureToMeasure.Leaves.TunedCapSystem
import MeasureToMeasure.Leaves.LandingPoleFamily
import MeasureToMeasure.Leaves.ArcHopCorridor

/-!
# Lemma 5.4 for finite-range targets: the machine-checked core (G8 assembly)

The finite-range core of the `lemma_5_4` discharge: any measurable transport map `ψ` taking
finitely many on-sphere values is approximated in `L²(μ)`, to any tolerance and within any exact
total duration `T`, by the transport map of an attention-flow schedule. The general `lemma_5_4`
follows by value rounding (`exists_finite_range_sphere_approx`) plus the `L²` triangle
inequality; see `MidLevel.lean`.

**The pipeline.** Preimage cells `ψ⁻¹ {zᵢ} ∩ 𝕊^{d-1}` → compact cores carrying all but an
`ε²`-budgeted sliver of each cell (`exists_compact_core_subset_sphere`) → the tuned cap system
(`exists_tuned_cap_system`: collapse/gate radii tuned off the finite centre-distance sets, cells
covering the cores up to budget) → Phase 1 staging (`staged_prefix_of_separated_caps`: each
cell's mass into a same-core staging ball) → landing poles (`exists_landing_pole_family`) and
arc hop corridors (`exists_arc_hop_corridor`: waypoint two-arc detours clearing all other
sources and landings) → Phase 2 relocation (`exists_merge_tolerant_relocation`: each staging
ball delivered into `ball (zᵢ, ε/4)`) → a parked pad block making the total duration exactly
`T`. Every engine block is `V = 0`, so the whole schedule has ONE transport map `ψε = f₂ ∘ f₁`
serving every sphere-supported probability measure at once; Dirac instantiation
(`flow_map_mem_of_universal`) turns the measure-level engine conclusions into the pointwise
estimate `‖ψ x - ψε x‖ < ε/2` on the good set, and the good/bad `L²` ledger
(`sqrtIntegral_le_of_good_bad`, diameter cost `2` on the `≤ ε²/8` bad mass) closes the bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace MeasureToMeasure.Statements

open MeasureTheory Set MeasureToMeasure.Foundations MeasureToMeasure.Leaves
open scoped ENNReal

variable {d : ℕ}

/-- **Lemma 5.4, finite-range core.** A measurable transport map with finitely many on-sphere
values is `L²(μ)`-approximated, to tolerance `ε` and within exact total duration `T`, by the
transport map of an attention schedule. This is the gated companion of `lemma_5_4`: the general
statement reduces to it by value rounding. -/
theorem lemma_5_4_of_finite_range (hd : 3 ≤ d) (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (ψ : Eucl d → Eucl d) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hμs : supportedIn μ (sphere d)) (hψm : Measurable ψ)
    (_hψs : ∀ᵐ x ∂μ, ψ x ∈ sphere d)
    (hrange : ∃ s : Finset (Eucl d), (∀ z ∈ s, z ∈ sphere d) ∧ ∀ x, ψ x ∈ s) :
    ∃ (θ : AttnSchedule d) (ψε : Eucl d → Eucl d),
      AttnSchedule.durationSum θ = T ∧
      attnMeasureFlow θ μ = μ.map ψε ∧ Measurable ψε ∧
      Integrable (fun x => ‖ψ x - ψε x‖ ^ 2) μ ∧
      Real.sqrt (∫ x, ‖ψ x - ψε x‖ ^ 2 ∂μ) ≤ ε := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨s, hs_sphere, hs_range⟩ := hrange
  -- the finitely many targets
  set n : ℕ := s.card with hndef
  set zt : Fin n → Eucl d := fun i => (s.equivFin.symm i : Eucl d) with hztdef
  have hzt_mem : ∀ i, zt i ∈ s := fun i => (s.equivFin.symm i).2
  have hzt_s : ∀ i, zt i ∈ sphere d := fun i => hs_sphere _ (hzt_mem i)
  -- the preimage cells on the sphere
  set A : Fin n → Set (Eucl d) := fun i => ψ ⁻¹' {zt i} ∩ sphere d with hAdef
  have hA_meas : ∀ i, MeasurableSet (A i) :=
    fun i => (hψm (measurableSet_singleton _)).inter (measurableSet_sphere d)
  have hA_disj : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨hxi, -⟩ ⟨hxj, -⟩
    apply hij
    apply s.equivFin.symm.injective
    apply Subtype.ext
    show zt i = zt j
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hxi hxj
    rw [← hxi, ← hxj]
  have hA_cover : sphere d ⊆ ⋃ i, A i := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨s.equivFin ⟨ψ x, hs_range x⟩, ?_⟩
    simp only [hAdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, hztdef,
      Equiv.symm_apply_apply]
    exact ⟨by trivial, hx⟩
  -- the total error budget
  set η : ℝ≥0∞ := ENNReal.ofReal (ε ^ 2 / 8) with hηdef
  have hη : 0 < η := ENNReal.ofReal_pos.mpr (by positivity)
  have hη2 : 0 < η / 2 := ENNReal.div_pos hη.ne' (by norm_num)
  have hηcell : 0 < η / 2 / (n + 1) := ENNReal.div_pos hη2.ne' (by simp)
  -- compact cores of the cells
  have hcore : ∀ i, ∃ Kc : Set (Eucl d), IsCompact Kc ∧ Kc ⊆ A i ∧ Kc ⊆ sphere d ∧
      μ (A i \ Kc) < η / 2 / (n + 1) := by
    intro i
    obtain ⟨Kc, h1, h2, h3, h4⟩ := exists_compact_core_subset_sphere μ (A i) (hA_meas i)
      (fun x hx => hx.2) _ hηcell
    exact ⟨Kc, h1, h2, h3, h4⟩
  choose Kc hKc_comp hKc_sub hKc_sph hKc_mass using hcore
  have hKc_disj : Pairwise fun i j => Disjoint (Kc i) (Kc j) := fun i j hij =>
    ((hA_disj hij).mono (hKc_sub i) (hKc_sub j))
  -- the tuned cap system at budget `η/2`
  obtain ⟨L, c, lab, aR, bR, E, ρ₀, hρ₀pos, hcK, hcs, hcne, haRpos, haRbR, hbR2, hEmeas,
    hEK, hEball, hEavoid, hsep, hEmass⟩ :=
    exists_tuned_cap_system μ hKc_comp hKc_sph hKc_disj hη2
  -- minimum centre separation
  obtain ⟨dm, hdm, hdmin⟩ : ∃ dm : ℝ, 0 < dm ∧
      ∀ j k : Fin L, j ≠ k → dm ≤ dist (c j) (c k) := by
    by_cases h2 : ∃ p : Fin L × Fin L, p.1 ≠ p.2
    · obtain ⟨p₀, hp₀⟩ := h2
      have hne : (Finset.univ.filter fun p : Fin L × Fin L => p.1 ≠ p.2).Nonempty :=
        ⟨p₀, by simp [hp₀]⟩
      refine ⟨(Finset.univ.filter fun p : Fin L × Fin L => p.1 ≠ p.2).inf' hne
        (fun p => dist (c p.1) (c p.2)), ?_, ?_⟩
      · refine (Finset.lt_inf'_iff _).mpr fun p hp => ?_
        rw [Finset.mem_filter] at hp
        exact dist_pos.mpr (hcne _ _ hp.2)
      · intro j k hjk
        have hmem : ((j, k) : Fin L × Fin L) ∈
            Finset.univ.filter fun p : Fin L × Fin L => p.1 ≠ p.2 :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩
        exact Finset.inf'_le _ hmem
    · exact ⟨1, one_pos, fun j k hjk => absurd ⟨(j, k), hjk⟩ h2⟩
  -- landing radius scale and pole-placement source radius
  set δl : ℝ := min (ε / 2) 4 with hδldef
  have hδl : 0 < δl := lt_min (by positivity) (by norm_num)
  have hδl4 : δl ≤ 4 := min_le_right _ _
  have hδlε : δl ≤ ε / 2 := min_le_left _ _
  set σr : ℝ := min (min (dm / 4) (δl / 16)) ρ₀ with hσrdef
  have hσr : 0 < σr := lt_min (lt_min (by positivity) (by positivity)) hρ₀pos
  have hσrδ : σr < δl / 8 := by
    have h1 : σr ≤ δl / 16 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hσrdm : σr ≤ dm / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hσrρ₀ : σr ≤ ρ₀ := min_le_right _ _
  have hsrcdisj : ∀ j k : Fin L, j ≠ k →
      Disjoint (Metric.closedBall (c j) σr) (Metric.closedBall (c k) σr) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro z hzj hzk
    rw [Metric.mem_closedBall] at hzj hzk
    have h1 := hdmin j k hjk
    have h2 := dist_triangle (c j) z (c k)
    rw [dist_comm (c j) z] at h2
    linarith
  -- the landing poles
  obtain ⟨z', r', hz's, hr'pos, hr'lt, hz'sub, hz'disj, hz'src⟩ :=
    exists_landing_pole_family (by omega : 2 ≤ d) (fun k => zt (lab k))
      (fun k => hzt_s (lab k)) hδl hδl4 c hσr hσrδ hsrcdisj
  -- landing poles are distinct from all sources and from each other
  have hz'ne_c : ∀ j i : Fin L, z' j ≠ c i := by
    intro j i heq
    have hdisj := hz'src j i
    rw [Set.disjoint_left] at hdisj
    exact hdisj (Metric.mem_closedBall_self (hr'pos j).le)
      (by rw [← heq]; exact Metric.mem_closedBall_self hσr.le)
  have hz'ne : ∀ j k : Fin L, j ≠ k → z' j ≠ z' k := by
    intro j k hjk heq
    have hdisj := hz'disj j k hjk
    rw [Set.disjoint_left] at hdisj
    exact hdisj (Metric.mem_closedBall_self (hr'pos j).le)
      (by rw [← heq]; exact Metric.mem_closedBall_self (hr'pos k).le)
  -- per-cap obstacle sets: every other source centre and landing pole
  set Q : Fin L → Finset (Eucl d) := fun k =>
    ((Finset.univ.image c ∪ Finset.univ.image z').erase (c k)).erase (z' k) with hQdef
  have hQ_sphere : ∀ k, ∀ q ∈ Q k, q ∈ sphere d := by
    intro k q hq
    have h1 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq)
    rw [Finset.mem_union] at h1
    rcases h1 with h1 | h1 <;> obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h1
    · exact hcs j
    · exact hz's j
  have hQ_ne_c : ∀ k, ∀ q ∈ Q k, q ≠ c k := by
    intro k q hq
    exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq)
  have hQ_ne_z' : ∀ k, ∀ q ∈ Q k, q ≠ z' k := fun k q hq => Finset.ne_of_mem_erase hq
  have hQc : ∀ k j : Fin L, j ≠ k → c j ∈ Q k := by
    intro k j hjk
    rw [hQdef]
    refine Finset.mem_erase.mpr ⟨(hz'ne_c k j).symm, ?_⟩
    refine Finset.mem_erase.mpr ⟨hcne j k hjk, ?_⟩
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem c (Finset.mem_univ j))
  have hQz' : ∀ k j : Fin L, j ≠ k → z' j ∈ Q k := by
    intro k j hjk
    rw [hQdef]
    refine Finset.mem_erase.mpr ⟨hz'ne j k hjk, ?_⟩
    refine Finset.mem_erase.mpr ⟨hz'ne_c j k, ?_⟩
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem z' (Finset.mem_univ j))
  -- the corridors
  have hcorr : ∀ k : Fin L, ∃ (cl : ℝ) (M : ℕ) (w : Fin (M + 1) → Eucl d)
      (wa wb : Fin M → ℝ), 0 < cl ∧ w 0 = c k ∧ w (Fin.last M) = z' k ∧
      (∀ t, w t ∈ sphere d) ∧
      (∀ t : Fin M, dist (w t.succ) (w t.castSucc) + cl ≤ wa t) ∧
      (∀ t, wa t < wb t) ∧ (∀ t, wb t ≤ 2) ∧
      (∀ (t : Fin M), ∀ q ∈ Q k,
        Disjoint (Metric.ball (w t.succ) (wb t)) (Metric.closedBall q cl)) := by
    intro k
    set qf : Fin (Q k).card → Eucl d := fun p => ((Q k).equivFin.symm p : Eucl d) with hqfdef
    have hqf_mem : ∀ p, qf p ∈ Q k := fun p => ((Q k).equivFin.symm p).2
    obtain ⟨cl, hclpos, M, w, wa, wb, hw0, hwlast, hws, hcap, hab, hb2, hgates⟩ :=
      exists_arc_hop_corridor hd (hcs k) (hz's k) qf
        (fun p => hQ_sphere k _ (hqf_mem p))
        (fun p => hQ_ne_c k _ (hqf_mem p))
        (fun p => hQ_ne_z' k _ (hqf_mem p))
    refine ⟨cl, M, w, wa, wb, hclpos, hw0, hwlast, hws, hcap, hab, hb2, ?_⟩
    intro t q hq
    have h1 := hgates t ((Q k).equivFin ⟨q, hq⟩)
    rw [hqfdef] at h1
    simp only [Equiv.symm_apply_apply] at h1
    exact h1
  choose cl Mc w wa wb hclpos hw0 hwlast hws hcapcl hab' hb2' hgates using hcorr
  -- the global staging radius
  obtain ⟨cm, hcm, hcmle⟩ : ∃ cm : ℝ, 0 < cm ∧ ∀ k, cm ≤ cl k := by
    rcases isEmpty_or_nonempty (Fin L) with hLE | hLN
    · exact ⟨1, one_pos, fun k => (hLE.false k).elim⟩
    · exact ⟨Finset.univ.inf' Finset.univ_nonempty cl,
        (Finset.lt_inf'_iff _).mpr fun k _ => hclpos k,
        fun k => Finset.inf'_le _ (Finset.mem_univ k)⟩
  obtain ⟨rm, hrm, hrmle⟩ : ∃ rm : ℝ, 0 < rm ∧ ∀ k, rm ≤ r' k := by
    rcases isEmpty_or_nonempty (Fin L) with hLE | hLN
    · exact ⟨1, one_pos, fun k => (hLE.false k).elim⟩
    · exact ⟨Finset.univ.inf' Finset.univ_nonempty r',
        (Finset.lt_inf'_iff _).mpr fun k _ => hr'pos k,
        fun k => Finset.inf'_le _ (Finset.mem_univ k)⟩
  set ρ : ℝ := min (min σr cm) rm with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min hσr hcm) hrm
  have hρσr : ρ ≤ σr := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρρ₀ : ρ ≤ ρ₀ := le_trans hρσr hσrρ₀
  have hρcl : ∀ k, ρ ≤ cl k := fun k =>
    le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (hcmle k)
  have hρr' : ∀ k, ρ ≤ r' k := fun k => le_trans (min_le_right _ _) (hrmle k)
  -- the shared block duration and the pad
  set B : ℕ := L + ∑ k, Mc k with hBdef
  set τ : ℝ := if B = 0 then 1 else T / 2 / B with hτdef
  have hτpos : 0 < τ := by
    rw [hτdef]
    split_ifs with hB
    · exact one_pos
    · have : (0 : ℝ) < (B : ℝ) := by
        have := Nat.pos_of_ne_zero hB
        exact_mod_cast this
      positivity
  have hengines : (L : ℝ) * τ + (∑ k, (Mc k : ℝ)) * τ = (B : ℝ) * τ := by
    rw [hBdef]
    push_cast
    ring
  have hBτ : (B : ℝ) * τ ≤ T := by
    rw [hτdef]
    split_ifs with hB
    · rw [hB]
      simp
      linarith
    · have hBpos : (0 : ℝ) < (B : ℝ) := by
        have := Nat.pos_of_ne_zero hB
        exact_mod_cast this
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hBpos.ne', mul_one]
      linarith
  -- Phase 1: staging
  obtain ⟨θ₁, hθ₁dur, hθ₁move, _hθ₁fix, f₁, hf₁m, hf₁to, hf₁map⟩ :=
    staged_prefix_of_separated_caps c hcs lab aR bR haRpos haRbR hbR2 E hEball hEavoid
      hρpos (hsep ρ hρpos hρρ₀) hτpos
  -- Phase 2: relocation
  have hcap : ∀ i (t : Fin (Mc i)), dist (w i t.succ) (w i t.castSucc) + ρ ≤ wa i t := by
    intro i t
    have h1 := hcapcl i t
    have h2 := hρcl i
    linarith
  have hgate_src : ∀ i j : Fin L, i < j → ∀ t : Fin (Mc i),
      Disjoint (Metric.ball (w i t.succ) (wb i t)) (Metric.ball (w j 0) ρ) := by
    intro i j hij t
    rw [hw0 j]
    refine Set.disjoint_of_subset_right ?_ (hgates i t (c j) (hQc i j (Ne.symm (ne_of_lt hij))))
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    have := hρcl i
    linarith
  have hgate_land : ∀ i j : Fin L, j < i → ∀ t : Fin (Mc i),
      Disjoint (Metric.ball (w i t.succ) (wb i t)) (Metric.ball (w j (Fin.last (Mc j))) ρ) := by
    intro i j hji t
    rw [hwlast j]
    refine Set.disjoint_of_subset_right ?_ (hgates i t (z' j) (hQz' i j (ne_of_lt hji)))
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    have := hρcl i
    linarith
  have hland : ∀ j : Fin L,
      Metric.ball (w j (Fin.last (Mc j))) ρ ⊆ Metric.ball (zt (lab j)) (δl / 2) := by
    intro j
    rw [hwlast j]
    refine subset_trans ?_ (hz'sub j)
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    have := hρr' j
    linarith
  obtain ⟨θ₂, hθ₂dur, hθ₂move, _hθ₂fix, f₂, hf₂m, hf₂to, hf₂map⟩ :=
    exists_merge_tolerant_relocation Mc w hws hρpos wa wb hcap hab' hb2'
      hgate_src hgate_land (fun j => zt (lab j)) hland hτpos
  -- the pad block to exact duration `T`
  have hpad_nonneg : 0 ≤ T - (B : ℝ) * τ := by linarith
  obtain ⟨ppad, hpaddur, hpadfix⟩ := exists_parked_pad_block (d := d) hpad_nonneg
  set θtot : AttnSchedule d := (θ₁ ++ θ₂) ++ [ppad] with hθtotdef
  set F : Eucl d → Eucl d := f₂ ∘ f₁ with hFdef
  have hFm : Measurable F := hf₂m.comp hf₁m
  have hFto : Set.MapsTo F (sphere d) (sphere d) := hf₂to.comp hf₁to
  -- the universal transport map of the whole schedule
  have hU12 : ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
      attnMeasureFlow (θ₁ ++ θ₂) ν = ν.map F :=
    universal_map_append hf₁m hf₂m hf₁map hf₂map
  have hUtot : ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
      attnMeasureFlow θtot ν = ν.map F := by
    intro ν _ hνs
    haveI : IsProbabilityMeasure (attnMeasureFlow (θ₁ ++ θ₂) ν) :=
      isProbabilityMeasure_attnMeasureFlow _ ν hνs
    have h12s : supportedIn (attnMeasureFlow (θ₁ ++ θ₂) ν) (sphere d) :=
      attnMeasureFlow_supportedIn_sphere _ ν hνs
    rw [hθtotdef, attnMeasureFlow_append, hpadfix _ h12s, hU12 ν hνs]
  -- exact total duration
  have hdur : AttnSchedule.durationSum θtot = T := by
    rw [hθtotdef, AttnSchedule.durationSum_append, AttnSchedule.durationSum_append,
      hθ₁dur, hθ₂dur]
    have hsing : AttnSchedule.durationSum [ppad] = ppad.duration := by
      simp [AttnSchedule.durationSum]
    rw [hsing, hpaddur]
    linarith [hengines]
  -- the pointwise estimate on the good set
  have hgood_pt : ∀ x ∈ sphere d, ∀ k : Fin L, x ∈ E k → ‖ψ x - F x‖ < ε / 2 := by
    intro x hx k hxE
    have h1 : f₁ x ∈ ⋃ j ∈ {j : Fin L | lab j = lab k}, Metric.ball (c j) ρ :=
      flow_map_mem_of_universal hf₁map (hθ₁move k) hx hxE
    rw [Set.mem_iUnion₂] at h1
    obtain ⟨j, hjlab, hjball⟩ := h1
    have hf₁x_s : f₁ x ∈ sphere d := hf₁to hx
    have h2 : f₂ (f₁ x) ∈ Metric.ball (zt (lab j)) (δl / 2) := by
      refine flow_map_mem_of_universal hf₂map (hθ₂move j) hf₁x_s ?_
      rw [hw0 j]
      exact hjball
    have hψx : ψ x = zt (lab k) := by
      have hxA : x ∈ A (lab k) := hKc_sub (lab k) (hEK k hxE)
      rw [hAdef] at hxA
      exact hxA.1
    have hdistlt : dist (f₂ (f₁ x)) (zt (lab k)) < δl / 2 := by
      rw [← hjlab]
      exact Metric.mem_ball.mp h2
    calc ‖ψ x - F x‖ = dist (ψ x) (F x) := (dist_eq_norm _ _).symm
      _ = dist (f₂ (f₁ x)) (zt (lab k)) := by
          rw [hψx, dist_comm]
          rfl
      _ < δl / 2 := hdistlt
      _ ≤ ε / 2 := by linarith
  -- a.e. bookkeeping
  have hae_sphere : ∀ᵐ x ∂μ, x ∈ sphere d := by
    rw [ae_iff]
    exact hμs
  set G : Set (Eucl d) := ⋃ k, E k with hGdef
  have hGmeas : MeasurableSet G := MeasurableSet.iUnion fun k => hEmeas k
  have hm : AEStronglyMeasurable (fun x => ψ x - F x) μ :=
    (hψm.sub hFm).aestronglyMeasurable
  have hgood : ∀ᵐ x ∂μ, x ∉ Gᶜ → ‖ψ x - F x‖ ≤ ε / 2 := by
    filter_upwards [hae_sphere] with x hx hxG
    have hxG' : x ∈ G := not_not.mp hxG
    rw [hGdef, Set.mem_iUnion] at hxG'
    obtain ⟨k, hk⟩ := hxG'
    exact (hgood_pt x hx k hk).le
  have hbound : ∀ᵐ x ∂μ, ‖ψ x - F x‖ ≤ 2 := by
    filter_upwards [hae_sphere] with x hx
    have h1 : ‖ψ x‖ = 1 := norm_eq_one_of_mem_sphere (hs_sphere _ (hs_range x))
    have h2 : ‖F x‖ = 1 := norm_eq_one_of_mem_sphere (hFto hx)
    calc ‖ψ x - F x‖ ≤ ‖ψ x‖ + ‖F x‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  have hint : Integrable (fun x => ‖ψ x - F x‖ ^ 2) μ :=
    integrable_sq_norm_of_ae_bound hm hbound
  -- the bad-set mass
  have hbad : μ Gᶜ ≤ η := by
    have hsub : Gᶜ ⊆ (sphere d)ᶜ ∪ ((⋃ i, A i \ Kc i) ∪ ((⋃ i, Kc i) \ G)) := by
      intro x hxG
      by_cases hxs : x ∈ sphere d
      · right
        by_cases hxK : x ∈ ⋃ i, Kc i
        · exact Or.inr ⟨hxK, hxG⟩
        · left
          obtain ⟨i, hxA⟩ := Set.mem_iUnion.mp (hA_cover hxs)
          refine Set.mem_iUnion.mpr ⟨i, hxA, fun hxk => hxK (Set.mem_iUnion.mpr ⟨i, hxk⟩)⟩
      · exact Or.inl hxs
    have hcores : μ (⋃ i, A i \ Kc i) ≤ η / 2 := by
      calc μ (⋃ i, A i \ Kc i) ≤ ∑ i, μ (A i \ Kc i) := by
            refine le_trans (measure_iUnion_le _) ?_
            rw [tsum_fintype]
        _ ≤ ∑ _i : Fin n, η / 2 / (n + 1) := Finset.sum_le_sum fun i _ => (hKc_mass i).le
        _ = (n : ℝ≥0∞) * (η / 2 / (n + 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ((n : ℝ≥0∞) + 1) * (η / 2 / ((n : ℝ≥0∞) + 1)) := by
            gcongr
            exact le_self_add
        _ ≤ η / 2 := ENNReal.mul_div_le
    have h0 : μ ((sphere d)ᶜ) = 0 := hμs
    calc μ Gᶜ ≤ μ ((sphere d)ᶜ ∪ ((⋃ i, A i \ Kc i) ∪ ((⋃ i, Kc i) \ G))) :=
          measure_mono hsub
      _ ≤ μ ((sphere d)ᶜ) + μ ((⋃ i, A i \ Kc i) ∪ ((⋃ i, Kc i) \ G)) := measure_union_le _ _
      _ ≤ μ ((sphere d)ᶜ) + (μ (⋃ i, A i \ Kc i) + μ ((⋃ i, Kc i) \ G)) := by
          gcongr
          exact measure_union_le _ _
      _ = μ (⋃ i, A i \ Kc i) + μ ((⋃ i, Kc i) \ G) := by rw [h0, zero_add]
      _ ≤ η / 2 + η / 2 := add_le_add hcores hEmass
      _ = η := ENNReal.add_halves η
  -- the ledger
  have hηtop : η ≠ ⊤ := ENNReal.ofReal_ne_top
  have hledger := sqrtIntegral_le_of_good_bad (μ := μ) hm hGmeas.compl
    (δ := ε / 2) (C := 2) (η := η) (by positivity) (by norm_num) hηtop hgood hbound hbad
  have hηtoReal : η.toReal = ε ^ 2 / 8 := ENNReal.toReal_ofReal (by positivity)
  have hfinal : Real.sqrt ((ε / 2) ^ 2 + 2 ^ 2 * η.toReal) ≤ ε := by
    rw [hηtoReal]
    calc Real.sqrt ((ε / 2) ^ 2 + 2 ^ 2 * (ε ^ 2 / 8))
        ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = ε := Real.sqrt_sq hε.le
  exact ⟨θtot, F, hdur, hUtot μ hμs, hFm, hint, le_trans hledger hfinal⟩

end MeasureToMeasure.Statements
