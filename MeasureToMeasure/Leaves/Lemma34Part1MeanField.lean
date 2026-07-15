import MeasureToMeasure.Leaves.CapMassGap
import MeasureToMeasure.Leaves.DistinctDim
import MeasureToMeasure.Leaves.PoleGeometry
import MeasureToMeasure.Leaves.CapPole
import MeasureToMeasure.Leaves.OffCenterCollapse
import MeasureToMeasure.Leaves.OffCenterW2
import MeasureToMeasure.Leaves.AnnulusMass
import MeasureToMeasure.Leaves.BarycenterCollapseGap
import MeasureToMeasure.Leaves.GatedBlockMeanFieldBridge
import MeasureToMeasure.Statements.MidLevel

/-!
# Lemma 3.4, Part 1 — mean-field analogue (`γ₁ = 1` case, on `AttnSchedule d`)

`lemma_3_4_part1` (`Statements/Lemma34Part1.lean`) is machine-checked on the LINEAR layer
(`Params d`/`measureFlow`). Both `lemma_3_4_part2` and `exists_disentangling_balls`'s Phase 2 need
the SAME mass-gap-cap-collapse construction on the MEAN-FIELD layer (`AttnSchedule d`/
`attnMeasureFlow`). `Leaves/GatedBlockMeanFieldBridge.lean` shows `pPark` (mean-field) and
`gatedBlock` (linear) push a sphere-supported probability measure to the IDENTICAL measure, so this
file reproduces `Lemma34Part1.lean`'s geometric construction (steps 1-3: mass-gap cap, pigeonhole
pole, collapse-barycenter gap, reach/annulus/pole-floor bookkeeping -- all layer-agnostic, no flow
dependence) verbatim, and swaps ONLY the final flow-construction step (step 4) to use `pPark` instead
of `gatedBlock`, transferring the barycenter-separation conclusion via the bridge's measure equality
rather than re-deriving it.

M3b/mid-level staging: consumed when `lemma_3_4_part2`/`exists_disentangling_balls` are discharged.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Axioms MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ} [NeZero d]

set_option maxHeartbeats 1200000 in
/-- **Lemma 3.4, Part 1, mean-field form.** For two distinct probability measures on `𝕊^{d-1} ∩
Q₁^{d-1}` with equal barycenters and a common open carrier `U`, some mean-field schedule `θ` makes
the flowed barycenters differ while fixing the sphere off `U`. -/
theorem lemma_3_4_part1_meanField (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (_hbar : barycenter μ = barycenter ν)
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hμU : supportedIn μ U) (hνU : supportedIn ν U) :
    ∃ θ : AttnSchedule d,
      barycenter (attnMeasureFlow θ μ) ≠ barycenter (attnMeasureFlow θ ν) ∧
      ∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ μ = μ.map Φ ∧
        ∀ x ∈ sphere d, x ∉ U → Φ x = x := by
  rw [supportedIn] at hμs hνs hμ hν hμU hνU
  -- Step 1: a mass-gap cap `{cos R < ⟪z, ·⟫}` inside the carrier `U`
  obtain ⟨z, cosR, hzsphere, hcosRhalf, hcosR1, hcapsub, hmassne⟩ :=
    Leaves.exists_cap_measure_ne_subset hne hUopen hμU hνU hμs hνs
  have hz : ‖z‖ = 1 := norm_eq_one_of_mem_sphere hzsphere
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hcosRlb : (-1 : ℝ) ≤ cosR := by linarith
  have hcosR0 : (0 : ℝ) ≤ cosR := by linarith
  -- Step 2: the forced "bad" pole `v`, and a unit `w ⊥ z` (needs `2 ≤ d`)
  have hd2 : 2 ≤ d := Leaves.two_le_d_of_distinct hne hμs hνs hμ hν
  obtain ⟨w, hzw, hw⟩ := Leaves.exists_unit_orthogonal hd2 hz0
  set Sμ : ℝ := (μ {x | cosR < (⟪z, x⟫ : ℝ)}).toReal with hSμ
  set Sν : ℝ := (ν {x | cosR < (⟪z, x⟫ : ℝ)}).toReal with hSν
  set p : Eucl d := ∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ with hp
  set q : Eucl d := ∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν with hq
  set cc : ℝ := Sμ - Sν with hcc
  have hccne : cc ≠ 0 := by
    rw [hcc, sub_ne_zero]
    intro h
    exact hmassne (by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), ← ENNReal.ofReal_toReal (measure_ne_top ν _),
        ← hSμ, ← hSν, h])
  set v : Eucl d := cc⁻¹ • (q - p) with hv
  obtain ⟨ω, hωnorm, hzωcap, hωne⟩ := Leaves.exists_pole_in_cap_ne hz hw hzw hcosRlb hcosR1 v
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hωnorm]
  set cval : ℝ := (⟪z, ω⟫ : ℝ) with hcval
  have hcval1 : cval ≤ 1 := by
    rw [hcval]; calc (⟪z, ω⟫ : ℝ) ≤ ‖z‖ * ‖ω‖ := real_inner_le_norm z ω
      _ = 1 := by rw [hz, hωnorm, mul_one]
  have hcvalpos : (0 : ℝ) < cval := by rw [hcval] at hzωcap ⊢; linarith
  -- Step 3: the collapse barycenters and their gap
  have hbaryμ : barycenter (μ.map (capCollapseMap z ω cosR)) = Sμ • ω + p :=
    barycenter_map_capCollapse hμs
  have hbaryν : barycenter (ν.map (capCollapseMap z ω cosR)) = Sν • ω + q :=
    barycenter_map_capCollapse hνs
  set G : ℝ := ‖barycenter (μ.map (capCollapseMap z ω cosR))
    - barycenter (ν.map (capCollapseMap z ω cosR))‖ with hG
  have hdiff : barycenter (μ.map (capCollapseMap z ω cosR))
      - barycenter (ν.map (capCollapseMap z ω cosR)) = cc • ω + (p - q) := by
    rw [hbaryμ, hbaryν, hcc, sub_smul]; module
  have hGpos : 0 < G := by
    rw [hG, norm_pos_iff, hdiff]
    intro h0
    apply hωne
    have hccω : cc • ω = q - p := by
      have h1 : cc • ω = -(p - q) := eq_neg_of_add_eq_zero_left h0
      rw [h1]; abel
    rw [hv, ← hccω, smul_smul, inv_mul_cancel₀ hccne, one_smul]
  have hSMcap : MeasurableSet {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} :=
    (continuous_const.inner continuous_id).measurable measurableSet_Ioi
  have hgmeas : Measurable (capCollapseMap z ω cosR) :=
    Measurable.piecewise hSMcap measurable_const measurable_id
  have hgsphere : ∀ x ∈ sphere d, capCollapseMap z ω cosR x ∈ sphere d := by
    intro x hx
    by_cases hxc : x ∈ {y : Eucl d | cosR < (⟪z, y⟫ : ℝ)}
    · have hgx : capCollapseMap z ω cosR x = ω := Set.piecewise_eq_of_mem _ _ _ hxc
      rw [hgx]; exact hωs
    · have hgx : capCollapseMap z ω cosR x = x := Set.piecewise_eq_of_notMem _ _ _ hxc
      rw [hgx]; exact hx
  have hmscompl : MeasurableSet (sphere d)ᶜ := Metric.isClosed_sphere.measurableSet.compl
  have hαμs : (μ.map (capCollapseMap z ω cosR)) (sphere d)ᶜ = 0 := by
    rw [Measure.map_apply hgmeas hmscompl]
    refine measure_mono_null (fun x hx => ?_) hμs
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
    exact fun hxs => hx (hgsphere x hxs)
  have hανs : (ν.map (capCollapseMap z ω cosR)) (sphere d)ᶜ = 0 := by
    rw [Measure.map_apply hgmeas hmscompl]
    refine measure_mono_null (fun x hx => ?_) hνs
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
    exact fun hxs => hx (hgsphere x hxs)
  haveI hαμprob : IsProbabilityMeasure (μ.map (capCollapseMap z ω cosR)) :=
    ⟨by rw [Measure.map_apply hgmeas MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩
  haveI hανprob : IsProbabilityMeasure (ν.map (capCollapseMap z ω cosR)) :=
    ⟨by rw [Measure.map_apply hgmeas MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩
  have hGle2 : G ≤ 2 := by
    rw [hG]
    calc ‖barycenter (μ.map (capCollapseMap z ω cosR)) - barycenter (ν.map (capCollapseMap z ω cosR))‖
        ≤ ‖barycenter (μ.map (capCollapseMap z ω cosR))‖
          + ‖barycenter (ν.map (capCollapseMap z ω cosR))‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add
          (Leaves.norm_barycenter_le_one hαμs (Leaves.integrable_id_of_sphere_support hαμs))
          (Leaves.norm_barycenter_le_one hανs (Leaves.integrable_id_of_sphere_support hανs))
      _ = 2 := by norm_num
  clear_value G Sμ Sν cc
  -- Step 4: reach target `b`, annulus threshold `m`, pole floor `mp`
  set b : ℝ := 1 - G ^ 2 / 32 with hbdef
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by rw [hbdef]; nlinarith [hGpos, hGle2], by rw [hbdef]; nlinarith [hGpos]⟩
  clear_value b
  obtain ⟨m₀, hm₀lb, hm₀ub, hm₀ann⟩ :=
    Leaves.exists_annulus_measure_le (ω := z) (μ := μ + ν) hcosR1
      (ε := ENNReal.ofReal (G ^ 2 / 32)) (ENNReal.ofReal_pos.mpr (by nlinarith [hGpos]))
  set m : ℝ := min m₀ ((cosR + cval) / 2) with hmdef
  have hm0 : (0 : ℝ) < m := by
    rw [hmdef, lt_min_iff]; exact ⟨by linarith, by linarith⟩
  have hmlb : cosR < m := by
    rw [hmdef, lt_min_iff]; exact ⟨hm₀lb, by linarith⟩
  have hmcval : m < cval := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hm1 : m < 1 := lt_of_lt_of_le hmcval hcval1
  have hmle : m ≤ m₀ := min_le_left _ _
  have hannsub : {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}
      ⊆ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m₀} :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hmle⟩
  have hμann : (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal ≤ G ^ 2 / 32 := by
    refine ENNReal.toReal_le_of_le_ofReal (by nlinarith [hGpos]) ?_
    calc μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}
        ≤ (μ + ν) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m₀} := by
          rw [Measure.add_apply]; exact le_add_right (measure_mono hannsub)
      _ ≤ ENNReal.ofReal (G ^ 2 / 32) := hm₀ann
  have hνann : (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal ≤ G ^ 2 / 32 := by
    refine ENNReal.toReal_le_of_le_ofReal (by nlinarith [hGpos]) ?_
    calc ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}
        ≤ (μ + ν) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m₀} := by
          rw [Measure.add_apply]; exact le_add_left (measure_mono hannsub)
      _ ≤ ENNReal.ofReal (G ^ 2 / 32) := hm₀ann
  clear_value m
  set mp : ℝ := m * cval - Real.sqrt (1 - m ^ 2) * Real.sqrt (1 - cval ^ 2) with hmpdef
  have hsm : Real.sqrt (1 - m ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg m])
  have hsc : Real.sqrt (1 - cval ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg cval])
  have hprod : Real.sqrt (1 - m ^ 2) * Real.sqrt (1 - cval ^ 2) ≤ 1 :=
    mul_le_one₀ hsm (Real.sqrt_nonneg _) hsc
  have hmp : mp ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · rw [hmpdef]; nlinarith [mul_pos hm0 hcvalpos, hprod]
    · rw [hmpdef]
      have hmc : m * cval ≤ m := mul_le_of_le_one_right hm0.le hcval1
      linarith [Real.sqrt_nonneg (1 - m ^ 2), Real.sqrt_nonneg (1 - cval ^ 2),
        mul_nonneg (Real.sqrt_nonneg (1 - m ^ 2)) (Real.sqrt_nonneg (1 - cval ^ 2)), hmc, hm1]
  have hpole : ∀ x ∈ sphere d, m ≤ (⟪z, x⟫ : ℝ) → mp ≤ (⟪x, ω⟫ : ℝ) := by
    intro x hxs hxm
    have hxnorm : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hxs
    have hbound := Leaves.inner_pole_lower_bound hz hxnorm hωnorm
    have hpiece1 : m * cval ≤ (⟪z, x⟫ : ℝ) * cval := mul_le_mul_of_nonneg_right hxm hcvalpos.le
    have hpiece2 : Real.sqrt (1 - (⟪z, x⟫ : ℝ) ^ 2) ≤ Real.sqrt (1 - m ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hxm, hm0])
    have hpiece3 := mul_le_mul_of_nonneg_right hpiece2 (Real.sqrt_nonneg (1 - cval ^ 2))
    calc mp = m * cval - Real.sqrt (1 - m ^ 2) * Real.sqrt (1 - cval ^ 2) := hmpdef
      _ ≤ (⟪z, x⟫ : ℝ) * cval
          - Real.sqrt (1 - (⟪z, x⟫ : ℝ) ^ 2) * Real.sqrt (1 - cval ^ 2) := by linarith
      _ ≤ (⟪x, ω⟫ : ℝ) := by rw [hcval]; exact hbound
  clear_value mp
  -- reach budget: stack enough blocks (linear-side reasoning is layer-agnostic; the block runs for
  -- combined duration `n * T`)
  set slope : ℝ := 2 * (m - cosR) * T with hslope
  have hslopepos : 0 < slope := by
    rw [hslope]; exact mul_pos (mul_pos two_pos (by linarith)) hT
  obtain ⟨n, hn⟩ := exists_nat_ge ((logOdds b - logOdds mp) / slope)
  rw [div_le_iff₀ hslopepos] at hn
  have hnT0 : (0 : ℝ) ≤ (n : ℝ) * T := by positivity
  have hreach : logOdds b ≤ logOdds mp + 2 * (m - cosR) * ((n : ℝ) * T) := by
    have : 2 * (m - cosR) * ((n : ℝ) * T) = (n : ℝ) * slope := by rw [hslope]; ring
    rw [this]; linarith
  -- Mean-field flow: a SINGLE `pPark` block of combined duration `n * T`.
  set θ : AttnSchedule d := [pPark z ω cosR ((n : ℝ) * T) hnT0] with hθdef
  have hbrμ : attnMeasureFlow θ μ = measureFlow [gatedBlock hz hωnorm hcosRlb hnT0] ((n : ℝ) * T) μ :=
    attnMeasureFlow_pPark_eq_measureFlow_gatedBlock hz hωnorm hcosRlb hnT0 hμs
  have hbrν : attnMeasureFlow θ ν = measureFlow [gatedBlock hz hωnorm hcosRlb hnT0] ((n : ℝ) * T) ν :=
    attnMeasureFlow_pPark_eq_measureFlow_gatedBlock hz hωnorm hcosRlb hnT0 hνs
  have hW2μ := W2_measureFlow_offCenter_collapse_le hz hωnorm hcosRlb hcosR0 hnT0
    hmcval hmlb hb hmp hpole hreach hμs
  have hW2ν := W2_measureFlow_offCenter_collapse_le hz hωnorm hcosRlb hcosR0 hnT0
    hmcval hmlb hb hmp hpole hreach hνs
  rw [← hbrμ] at hW2μ
  rw [← hbrν] at hW2ν
  have h2b : 2 * (1 - b) = G ^ 2 / 16 := by rw [hbdef]; ring
  have hRμ : Real.sqrt (2 * (1 - b)
      + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) < G / 2 := by
    rw [h2b, show (G / 2 : ℝ) = Real.sqrt ((G / 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [hμann, hGpos]
  have hRν : Real.sqrt (2 * (1 - b)
      + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) < G / 2 := by
    rw [h2b, show (G / 2 : ℝ) = Real.sqrt ((G / 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [hνann, hGpos]
  haveI : IsProbabilityMeasure (attnMeasureFlow θ μ) := by
    rw [hbrμ]; exact isProbabilityMeasure_measureFlow _ _ μ
  haveI : IsProbabilityMeasure (attnMeasureFlow θ ν) := by
    rw [hbrν]; exact isProbabilityMeasure_measureFlow _ _ ν
  have hPμsphere : (attnMeasureFlow θ μ) (sphere d)ᶜ = 0 := by
    rw [hbrμ]; exact measureFlow_supportedIn_sphere _ hnT0 hμs
  have hPνsphere : (attnMeasureFlow θ ν) (sphere d)ᶜ = 0 := by
    rw [hbrν]; exact measureFlow_supportedIn_sphere _ hnT0 hνs
  refine ⟨θ, ?_, ?_⟩
  · refine Leaves.barycenter_ne_of_W2_gap hPμsphere hPνsphere hαμs hανs hW2μ hW2ν ?_
    rw [← hG]
    calc Real.sqrt (2 * (1 - b)
            + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
          + Real.sqrt (2 * (1 - b)
            + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
        < G / 2 + G / 2 := add_lt_add hRμ hRν
      _ = G := by ring
  · have hex := @exists_meanFieldFlow d (pPark z ω cosR ((n : ℝ) * T) hnT0) μ ‹_› hμs
    set Φ := hex.choose with hΦdef
    have hΦspec : IsMeanFieldFlow (pPark z ω cosR ((n : ℝ) * T) hnT0) μ Φ := hex.choose_spec
    set Φd := Φ (pPark z ω cosR ((n : ℝ) * T) hnT0).duration with hΦddef
    have hΦstep : attnMeasureFlow θ μ = μ.map Φd := by
      show attnStep (pPark z ω cosR ((n : ℝ) * T) hnT0) μ = _
      unfold attnStep
      rw [dif_pos ⟨‹_›, hμs⟩]
    refine ⟨Φd, hΦspec.measurable ((pPark z ω cosR ((n : ℝ) * T) hnT0).duration)
      ⟨hnT0, le_rfl⟩, hΦstep, ?_⟩
    intro x hxsphere hxU
    have hxcap : ¬ (cosR < (⟪z, x⟫ : ℝ)) := fun hlt => hxU (hcapsub x hxsphere hlt)
    have hxle : (⟪z, x⟫ : ℝ) ≤ cosR := not_lt.mp hxcap
    exact attnFlow_id_of_inner_le z ω cosR ((n : ℝ) * T) hnT0 hμs Φ hΦspec hxsphere hxle
      ⟨hnT0, le_rfl⟩

end MeasureToMeasure.Leaves
