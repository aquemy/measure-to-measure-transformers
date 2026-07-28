import MeasureToMeasure.Leaves.AnnulusMass
import MeasureToMeasure.Leaves.GatedTwoCap
import MeasureToMeasure.Leaves.GatedBlockMeanFieldBridge
import MeasureToMeasure.Leaves.WassersteinDiracBound
import MeasureToMeasure.Statements.SupportedIn
import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.Dynamics

/-!
# Hemisphere collapse to a Dirac (the `prop_2_1` engine)

`prop_2_1` asks for a schedule driving a sphere-supported probability measure carried by an OPEN
hemisphere `{0 < ⟪e,·⟫}` arbitrarily `W₂`-close to a Dirac at a sphere point, with duration
exactly `T` and one constant piece. This file builds that engine as a single attention block on
the mean-field layer, with the Dirac placed at the hemisphere's own pole `e`.

Two leaves, deliberately kept in one file:

* `hemisphere_subcap_mass_le` is the ONLY place the open hemisphere hypothesis is consumed: the
  hemisphere gives no uniform gap (`⟪e,x⟫` can be arbitrarily close to `0`), but the sub-level
  sets `{⟪e,·⟫ < m}` shrink to the mass-free closed half-space `{⟪e,·⟫ ≤ 0}` as `m ↓ 0`, so
  continuity of measure (`exists_annulus_measure_le` at `cosR := 0`) makes their mass an
  arbitrarily small budget. Keeping it as a named lemma documents that no statement narrowing
  (no uniform-gap strengthening) was needed.

* `exists_collapse_block_hemisphere_W2` assembles mass split + gated pull + mean-field bridge +
  pushforward bookkeeping + `W₂` closing. Witness: the amplitude-scaled parking block
  `pParkScaled A e e (-1) T` (gate open on the whole sphere minus the antipode, `cosR = -1`),
  whose amplitude `A` is chosen by `exists_scaledGatedBlock_mapsTo_cap` so that time `T` alone
  meets the rim budget -- the paper's parameter-norm freedom `‖θ‖ ~ C/(T·ε)`, so NO reach-budget
  replication or rescaling is needed and the duration is `T` by `rfl`. The bridge
  `attnMeasureFlow_pParkScaled_eq_measureFlow_scaledGatedBlock` rewrites the mean-field flow as
  a linear pushforward; off-cap mass after the flow is at most the off-sub-cap mass before it
  (`MapsTo` preimage bookkeeping), the surviving cap is a chordal ball
  (`‖y-e‖² = 2-2⟪y,e⟫ ≤ 2(1-b)`), and `W2_dirac_le_of_closedBall_mass` closes:
  `√(ε²/2 + 4·ε²/8) = ε`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Axioms MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **Mass split for an open hemisphere.** A probability measure carried by the OPEN hemisphere
`{0 < ⟪e,·⟫}` puts arbitrarily small mass below some positive inner-product level `m < 1`. This is
the only consumer of the open-hemisphere hypothesis in the `prop_2_1` engine: no uniform gap is
assumed, the sub-level mass is squeezed between the mass-free closed half-space `{⟪e,·⟫ ≤ 0}` and
the vanishing annulus `{0 < ⟪e,·⟫ < m}` of `exists_annulus_measure_le` at `cosR := 0`. -/
theorem hemisphere_subcap_mass_le {e : Eucl d} (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hhemi : supportedIn μ {x | 0 < (⟪e, x⟫ : ℝ)}) {budget : ℝ≥0∞} (hb : 0 < budget) :
    ∃ m : ℝ, 0 < m ∧ m < 1 ∧ μ {x | (⟪e, x⟫ : ℝ) < m} ≤ budget := by
  obtain ⟨m, hm0, hm1, hann⟩ :=
    exists_annulus_measure_le (ω := e) (μ := μ) (cosR := 0) one_pos hb
  refine ⟨m, hm0, hm1, ?_⟩
  have hsplit : {x : Eucl d | (⟪e, x⟫ : ℝ) < m}
      ⊆ {x : Eucl d | 0 < (⟪e, x⟫ : ℝ)}ᶜ
        ∪ {x : Eucl d | 0 < (⟪e, x⟫ : ℝ) ∧ (⟪e, x⟫ : ℝ) < m} := by
    intro x hx
    by_cases h : 0 < (⟪e, x⟫ : ℝ)
    · exact Set.mem_union_right _ ⟨h, hx⟩
    · exact Set.mem_union_left _ h
  calc μ {x : Eucl d | (⟪e, x⟫ : ℝ) < m}
      ≤ μ ({x : Eucl d | 0 < (⟪e, x⟫ : ℝ)}ᶜ
        ∪ {x : Eucl d | 0 < (⟪e, x⟫ : ℝ) ∧ (⟪e, x⟫ : ℝ) < m}) := measure_mono hsplit
    _ ≤ μ {x : Eucl d | 0 < (⟪e, x⟫ : ℝ)}ᶜ
        + μ {x : Eucl d | 0 < (⟪e, x⟫ : ℝ) ∧ (⟪e, x⟫ : ℝ) < m} := measure_union_le _ _
    _ = μ {x : Eucl d | 0 < (⟪e, x⟫ : ℝ) ∧ (⟪e, x⟫ : ℝ) < m} := by
        rw [hhemi, zero_add]
    _ ≤ budget := hann

variable [NeZero d]

/-- **Hemisphere collapse to a Dirac at the pole, on the mean-field layer.** A sphere-supported
probability measure carried by the open hemisphere `{0 < ⟪e,·⟫}` is driven `W₂`-within `ε` of the
Dirac at the pole `e` by a SINGLE attention block of duration EXACTLY `T`. This is the `prop_2_1`
engine: one constant piece, duration `T` on the nose (the amplitude, not the horizon, absorbs the
reach budget), target point on the sphere.

Witness: `pParkScaled A e e (-1) T` -- gate level `cosR = -1` opens the gate on the whole sphere
minus the antipode, the amplitude `A` from `exists_scaledGatedBlock_mapsTo_cap` pulls the closed
sub-cap `{m ≤ ⟪·,e⟫}` (all but `ε²/8` of the mass, by `hemisphere_subcap_mass_le`) above the cap
level `b := max (1-ε²/4) 0` in time `T`. On the sphere `b ≤ ⟪y,e⟫` reads as the chordal ball
`‖y-e‖ ≤ √(2(1-b))`, so `W2_dirac_le_of_closedBall_mass` gives
`W₂ ≤ √(2(1-b) + 4·ε²/8) ≤ √(ε²/2 + ε²/2) = ε`. -/
theorem exists_collapse_block_hemisphere_W2 {e : Eucl d} (he : ‖e‖ = 1)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hμs : supportedIn μ (sphere d)) (hhemi : supportedIn μ {x | 0 < (⟪e, x⟫ : ℝ)}) :
    ∃ p : AttnParams d, p.duration = T ∧
      Axioms.W2 (attnMeasureFlow [p] μ) (Measure.dirac e) ≤ ε := by
  have hes : e ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, he]
  have hcosR : (-1 : ℝ) ≤ -1 := le_rfl
  -- cap level `b`: within `Ioo (-1) 1` and with deficit `1 - b ≤ ε²/4`
  set b : ℝ := max (1 - ε ^ 2 / 4) 0 with hbdef
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    · apply max_lt _ one_pos
      nlinarith
  have hbge : 1 - ε ^ 2 / 4 ≤ b := le_max_left _ _
  have hb1 : 1 - b ≤ ε ^ 2 / 4 := by linarith
  -- mass split: all but `ε²/8` of the mass sits in the closed sub-cap `{m ≤ ⟪e,·⟫}`
  obtain ⟨m, hm0, hm1, hμm⟩ := hemisphere_subcap_mass_le μ hhemi
    (budget := ENNReal.ofReal (ε ^ 2 / 8)) (ENNReal.ofReal_pos.mpr (by positivity))
  -- amplitude meeting the rim budget at horizon exactly `T`
  obtain ⟨A, hA, hmaps⟩ := exists_scaledGatedBlock_mapsTo_cap (ω := e) he
    (cosR := -1) hcosR hT (by linarith : (-1 : ℝ) < m) hm1 hb
  set B : Block d := scaledGatedBlock hA he he hcosR hT.le with hBdef
  set p : AttnParams d := pParkScaled A e e (-1) T hT.le with hpdef
  have hdur : p.duration = T := rfl
  rw [supportedIn] at hμs
  -- mean-field bridge: the attention flow of `p` IS the linear pushforward by `B.blockFlow T`
  have hbr : attnMeasureFlow [p] μ = measureFlow [B] T μ :=
    attnMeasureFlow_pParkScaled_eq_measureFlow_scaledGatedBlock hA he he hcosR hT.le hμs
  set ν : Measure (Eucl d) := measureFlow [B] T μ with hνdef
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_measureFlow _ _ μ
  have hνS : ν (sphere d)ᶜ = 0 := measureFlow_supportedIn_sphere _ hT.le hμs
  have hνmap : ν = μ.map (B.blockFlow T) := by
    rw [hνdef, measureFlow_map, flowMap_cons, flowMap_nil, Function.id_comp]
  -- pushforward bookkeeping: mass below level `b` after the flow is below the split budget
  have hcontb : Continuous (fun y : Eucl d => (⟪y, e⟫ : ℝ)) :=
    continuous_id.inner continuous_const
  have hSMb : MeasurableSet {y : Eucl d | (⟪y, e⟫ : ℝ) < b} :=
    measurableSet_lt hcontb.measurable measurable_const
  have hνb : ν {y : Eucl d | (⟪y, e⟫ : ℝ) < b} ≤ ENNReal.ofReal (ε ^ 2 / 8) := by
    rw [hνmap, Measure.map_apply (B.measurable_blockFlow hT.le) hSMb]
    have hsub : (B.blockFlow T) ⁻¹' {y : Eucl d | (⟪y, e⟫ : ℝ) < b}
        ⊆ (sphere d)ᶜ ∪ {x : Eucl d | (⟪e, x⟫ : ℝ) < m} := by
      intro x hx
      by_cases hxs : x ∈ sphere d
      · refine Set.mem_union_right _ ?_
        by_contra hxm
        have hxm' : m ≤ (⟪x, e⟫ : ℝ) := by
          rw [real_inner_comm]
          exact not_lt.mp hxm
        have hcap := hmaps (show x ∈ {x : Eucl d | x ∈ sphere d ∧ m ≤ (⟪x, e⟫ : ℝ)}
          from ⟨hxs, hxm'⟩)
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx hcap
        linarith
      · exact Set.mem_union_left _ hxs
    calc μ ((B.blockFlow T) ⁻¹' {y : Eucl d | (⟪y, e⟫ : ℝ) < b})
        ≤ μ ((sphere d)ᶜ ∪ {x : Eucl d | (⟪e, x⟫ : ℝ) < m}) := measure_mono hsub
      _ ≤ μ (sphere d)ᶜ + μ {x : Eucl d | (⟪e, x⟫ : ℝ) < m} := measure_union_le _ _
      _ = μ {x : Eucl d | (⟪e, x⟫ : ℝ) < m} := by rw [hμs, zero_add]
      _ ≤ ENNReal.ofReal (ε ^ 2 / 8) := hμm
  -- chordal cap: on the sphere, `b ≤ ⟪y,e⟫` puts `y` in the closed ball of radius `√(2(1-b))`
  set R : ℝ := Real.sqrt (2 * (1 - b)) with hRdef
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hmass : ν (Metric.closedBall e R)ᶜ ≤ ENNReal.ofReal (ε ^ 2 / 8) := by
    have hsub : (Metric.closedBall e R)ᶜ
        ⊆ (sphere d)ᶜ ∪ {y : Eucl d | (⟪y, e⟫ : ℝ) < b} := by
      intro y hy
      by_cases hys : y ∈ sphere d
      · refine Set.mem_union_right _ ?_
        by_contra hyb
        have hyb' : b ≤ (⟪y, e⟫ : ℝ) := not_lt.mp fun h => hyb h
        refine hy ?_
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hyn : ‖y‖ = 1 := norm_eq_one_of_mem_sphere hys
        have hsq : ‖y - e‖ ^ 2 = 2 - 2 * (⟪y, e⟫ : ℝ) := by
          rw [norm_sub_sq_real, hyn, he]; ring
        have h2 : ‖y - e‖ ^ 2 ≤ 2 * (1 - b) := by rw [hsq]; linarith
        calc ‖y - e‖ = Real.sqrt (‖y - e‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (2 * (1 - b)) := Real.sqrt_le_sqrt h2
      · exact Set.mem_union_left _ hys
    calc ν (Metric.closedBall e R)ᶜ
        ≤ ν ((sphere d)ᶜ ∪ {y : Eucl d | (⟪y, e⟫ : ℝ) < b}) := measure_mono hsub
      _ ≤ ν (sphere d)ᶜ + ν {y : Eucl d | (⟪y, e⟫ : ℝ) < b} := measure_union_le _ _
      _ = ν {y : Eucl d | (⟪y, e⟫ : ℝ) < b} := by rw [hνS, zero_add]
      _ ≤ ENNReal.ofReal (ε ^ 2 / 8) := hνb
  -- close in `W₂`: `√(2(1-b) + 4·ε²/8) ≤ √(ε²/2 + ε²/2) = ε`
  have hW2 := MeasureToMeasure.W2_dirac_le_of_closedBall_mass ν hνS e hes R (ε ^ 2 / 8)
    hR0 (by positivity) hmass
  have hRsq : R ^ 2 = 2 * (1 - b) := Real.sq_sqrt (by nlinarith [hb.2])
  have harg : R ^ 2 + 4 * (ε ^ 2 / 8) ≤ ε ^ 2 := by rw [hRsq]; nlinarith
  have hsqrt : Real.sqrt (R ^ 2 + 4 * (ε ^ 2 / 8)) ≤ ε := by
    calc Real.sqrt (R ^ 2 + 4 * (ε ^ 2 / 8)) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt harg
      _ = ε := Real.sqrt_sq hε.le
  refine ⟨p, hdur, ?_⟩
  rw [hbr]
  show (MeasureToMeasure.W2 ν (Measure.dirac e)).toReal ≤ ε
  calc (MeasureToMeasure.W2 ν (Measure.dirac e)).toReal
      ≤ (ENNReal.ofReal (Real.sqrt (R ^ 2 + 4 * (ε ^ 2 / 8)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hW2
    _ = Real.sqrt (R ^ 2 + 4 * (ε ^ 2 / 8)) := ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
    _ ≤ ε := hsqrt

end MeasureToMeasure.Leaves
