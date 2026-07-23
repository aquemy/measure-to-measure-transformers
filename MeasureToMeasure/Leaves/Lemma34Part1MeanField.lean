import MeasureToMeasure.Leaves.CapMassGap
import MeasureToMeasure.Leaves.DistinctDim
import MeasureToMeasure.Leaves.PoleGeometry
import MeasureToMeasure.Leaves.CapPole
import MeasureToMeasure.Leaves.OffCenterCollapse
import MeasureToMeasure.Leaves.OffCenterW2
import MeasureToMeasure.Leaves.AnnulusMass
import MeasureToMeasure.Leaves.BarycenterCollapseGap
import MeasureToMeasure.Leaves.CollapseColinearityAvoidance
import MeasureToMeasure.Leaves.GatedBlockMeanFieldBridge
import MeasureToMeasure.Leaves.AttnRescale
import MeasureToMeasure.Statements.SupportedIn

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
/-- **The mass-gap-cap-collapse construction, mean-field form, γ-INDEPENDENT.** For two distinct
sphere-and-orthant-supported probability measures with a common open carrier `U`, some mean-field
schedule `θ` makes the flowed barycenters differ while fixing the sphere off `U` -- with NO relation
between `barycenter μ` and `barycenter ν` assumed. Matches the LINEAR layer's `lemma_3_4_part1`,
whose own `_hbar : barycenter μ = barycenter ν` hypothesis is provably unused (the mass-gap cap only
consumes `μ ≠ ν`): this mean-field form makes that generality explicit, since `lemma_3_4_part2`
needs it for COLINEAR-UNEQUAL (not equal) barycenters, unlike `lemma_3_4_part1`'s own `γ₁ = 1` case. -/
theorem barycenter_ne_of_massGapCollapse_meanField (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hμU : supportedIn μ U) (hνU : supportedIn ν U) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      barycenter (attnMeasureFlow θ μ) ≠ barycenter (attnMeasureFlow θ ν) ∧
      (∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ μ = μ.map Φ ∧
        ∀ x ∈ sphere d, x ∉ U → Φ x = x) ∧
      ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        supportedIn ρ Uᶜ → attnMeasureFlow θ ρ = ρ := by
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
  obtain ⟨ω, hωnorm, hzωcap, hωne, _⟩ := Leaves.exists_pole_in_cap_ne hz hw hzw hcosRlb hcosR1 v
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
  -- `n` is forced to `≥ 1` (via `n₀ + 1`, not just `exists_nat_ge`'s raw witness) so the final
  -- block can be time-rescaled to EXACTLY duration `T` (`AttnParams.rescale` divides by `n`,
  -- needing `n ≠ 0`); a larger `n` only helps the reach bound (`slope > 0`), so this costs nothing.
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((logOdds b - logOdds mp) / slope)
  rw [div_le_iff₀ hslopepos] at hn₀
  set n : ℕ := n₀ + 1 with hndef
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [hndef]; positivity
  have hnT0 : (0 : ℝ) ≤ (n : ℝ) * T := by positivity
  have hreach : logOdds b ≤ logOdds mp + 2 * (m - cosR) * ((n : ℝ) * T) := by
    have hmono : (n₀ : ℝ) * slope ≤ (n : ℝ) * slope := by
      rw [hndef]; push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hslopepos.le
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
  -- Rescale the single block to hit `T` EXACTLY (`n·T / n = T`), reusing every fact already
  -- established about `θ` via `attnMeasureFlow_singleton_rescale_eq` (same resulting measure).
  set θ' : AttnSchedule d := [(pPark z ω cosR ((n : ℝ) * T) hnT0).rescale hnpos] with hθ'def
  have hθ'dur : AttnSchedule.durationSum θ' = T := by
    rw [hθ'def]
    simp only [AttnSchedule.durationSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [AttnParams.rescale_duration]
    show (n : ℝ) * T / (n : ℝ) = T
    field_simp
  have hflowEqμ : attnMeasureFlow θ' μ = attnMeasureFlow θ μ := by
    rw [hθ'def, hθdef]
    exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T) hnT0) hnpos μ hμs
  have hflowEqν : attnMeasureFlow θ' ν = attnMeasureFlow θ ν := by
    rw [hθ'def, hθdef]
    exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T) hnT0) hnpos ν hνs
  refine ⟨θ', hθ'dur, ?_, ?_, ?_⟩
  · rw [hflowEqμ, hflowEqν]
    refine Leaves.barycenter_ne_of_W2_gap hPμsphere hPνsphere hαμs hανs hW2μ hW2ν ?_
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
      ⟨hnT0, le_rfl⟩, ?_, ?_⟩
    · rw [hflowEqμ]; exact hΦstep
    intro x hxsphere hxU
    have hxcap : ¬ (cosR < (⟪z, x⟫ : ℝ)) := fun hlt => hxU (hcapsub x hxsphere hlt)
    have hxle : (⟪z, x⟫ : ℝ) ≤ cosR := not_lt.mp hxcap
    exact attnFlow_id_of_inner_le z ω cosR ((n : ℝ) * T) hnT0 hμs Φ hΦspec hxsphere hxle
      ⟨hnT0, le_rfl⟩
  · -- **Bystander-fixing conjunct.** Any sphere-supported probability measure whose mass avoids
    -- the carrier `U` also avoids the mass-gap cap (`hcapsub` puts the cap inside `U`), so the
    -- single-block schedule `θ` (equivalently its exact-duration rescale `θ'`) fixes it exactly,
    -- via the just-banked `attnMeasureFlow_pPark_eq_of_off_cap` and the rescale bridge.
    intro ρ _ hρs hρU
    rw [supportedIn] at hρs
    rw [supportedIn, compl_compl] at hρU
    have hρcap : ρ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_union_null hρU hρs)
      by_cases hxs : x ∈ sphere d
      · exact Or.inl (hcapsub x hxs hx)
      · exact Or.inr hxs
    have hflowEqρ : attnMeasureFlow θ' ρ = attnMeasureFlow θ ρ := by
      rw [hθ'def, hθdef]
      exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T) hnT0) hnpos
        ρ hρs
    rw [hflowEqρ, hθdef]
    exact attnMeasureFlow_pPark_eq_of_off_cap z ω cosR ((n : ℝ) * T) hnT0 ρ hρs hρcap

set_option maxHeartbeats 1600000 in
/-- **Full non-colinearity of the mass-gap-cap-collapse construction, mean-field form**, closing
`lemma_3_4_part2`'s Gap 2 (`mean-field-axioms-retractability` project notes) UNDER AN EXPLICIT
non-degeneracy hypothesis (`hgenRest`) narrower than the full axiom.
`barycenter_ne_of_massGapCollapse_meanField` only proves the flowed barycenters are UNEQUAL; the
axiom needs them NON-COLINEAR for every `γ₂`. This theorem reuses that construction verbatim through
Steps 1–3 (mass-gap cap, pigeonhole pole, collapse-barycenter identification), then closes the
non-colinearity gap via `CollapseColinearityAvoidance.lean`'s Case A machinery
(`ne_smul_of_restComp_gramGap_perturbation`):

* the cap-pole `ω` lies in `span{z,w}` (`hωspan`, now exposed by `exists_pole_in_cap_ne`), so the
  ideal collapse targets' rest-component (orthogonal to `span{z,w}`) equals the leftover-mass
  integrals `p, q`'s own rest-component, `θ`-independently (`ω`'s own rest-component vanishes);
* `hgenRest` supplies the rest-component non-parallelism (Case A's applicability condition) for
  EVERY admissible mass-gap cap the Besicovitch-driven construction could produce, not just the
  specific `z, cosR, w` this particular run selects — the construction-internal `z, cosR` cannot be
  exposed to a caller-stated hypothesis before the fact (see `CollapseColinearityAvoidance.lean`'s
  docstring and the `mean-field-axioms-retractability` notes for why this is not implied by
  `lemma_3_4_part2`'s existing `hcol, hsupp, hu`, which constrain the GLOBAL barycenters, not the
  cap-construction-internal leftover integrals);
* given the qualitative non-parallelism, a quantitative `δ`-margin follows for free
  (`gramGap_pos_of_ne_smul`), itself fixed BEFORE `b, m, n` are chosen (it depends only on `p, q, z,
  w`, never on `θ` or the reach schedule) — exactly the "W₂-constant-matching" structure identified
  in `mean-field-axioms-retractability`;
* the `W₂`-error budget (`b`'s reach slack and the rim-annulus mass bound) is retuned to a single
  shared target `ε := δ²/20000` (comfortably small relative to `δ`, replacing the original
  `G²/32`-relative slack), giving `rP, rQ ≤ √(6ε) < δ/40`, which satisfies
  `ne_smul_of_restComp_gramGap_perturbation`'s smallness conditions (`rP, rQ ≤ δ/8`,
  `20(rP+rQ) < δ`) with comfortable room to spare; `n` is then chosen exactly as before (via
  `exists_nat_ge`, which succeeds for any finite reach target since `b < 1` strictly), except forced
  to `n₀ + 1 ≥ 1` (a strictly larger reach target only helps, since `slope > 0`) so the schedule can be
  time-rescaled to hit `T` EXACTLY.

**The conclusion now matches `lemma_3_4_part2`'s exact `durationSum θ = T ∧ switches θ ≤ 2 ∧ ...`
shape** (previously only proved for a schedule of duration `n·T`, `n` chosen by the reach budget, not
literally `T`): `Leaves/AttnRescale.lean`'s `attnStep_rescale_eq` shows the SAME single block,
rescaled by `n` (`AttnParams.rescale`, dividing `V, W` and duration by `n`), pushes a sphere-supported
probability measure to the IDENTICAL final measure — so the schedule literally returned is
`[block.rescale hnpos]` (duration EXACTLY `T`, `n ≠ 0` from the forcing above), with every fact already
established about the un-rescaled `θ` (the non-colinearity conclusion, the `Φ`/fixed-off-`U` clause)
transferred via this measure equality rather than re-derived. This closes BOTH outstanding wiring
obligations flagged in the previous version of this docstring; only the `hgenRest` residual-degeneracy
question (see `mean-field-axioms-retractability`) remains before `lemma_3_4_part2` itself could be
discharged. -/
theorem barycenter_nonColinear_of_massGapCollapse_meanField (μ ν : Measure (Eucl d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hμU : supportedIn μ U) (hνU : supportedIn ν U)
    (hgenRest : ∀ z : Eucl d, ‖z‖ = 1 → ∀ cosR : ℝ, cosR ∈ Set.Ioo (1 / 2 : ℝ) 1 →
      ∀ w : Eucl d, ‖w‖ = 1 → (⟪z, w⟫ : ℝ) = 0 →
      Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν) ≠ 0 ∧
      ∀ c : ℝ, Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ)
        ≠ c • Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν)) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧ AttnSchedule.switches θ ≤ 2 ∧
      (∀ γ₂ : ℝ, barycenter (attnMeasureFlow θ μ) ≠ γ₂ • barycenter (attnMeasureFlow θ ν)) ∧
      (∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ μ = μ.map Φ ∧
        ∀ x ∈ sphere d, x ∉ U → Φ x = x) ∧
      ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        supportedIn ρ Uᶜ → attnMeasureFlow θ ρ = ρ := by
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
  obtain ⟨ω, hωnorm, hzωcap, hωne, hωspan⟩ :=
    Leaves.exists_pole_in_cap_ne hz hw hzw hcosRlb hcosR1 v
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hωnorm]
  set cval : ℝ := (⟪z, ω⟫ : ℝ) with hcval
  have hcval1 : cval ≤ 1 := by
    rw [hcval]; calc (⟪z, ω⟫ : ℝ) ≤ ‖z‖ * ‖ω‖ := real_inner_le_norm z ω
      _ = 1 := by rw [hz, hωnorm, mul_one]
  have hcvalpos : (0 : ℝ) < cval := by rw [hcval] at hzωcap ⊢; linarith
  -- Step 2′: the rest-component gramGap, from `hgenRest` — fixed BEFORE Step 4's `b, m, n`
  obtain ⟨hq0, hnesmul⟩ := hgenRest z hz cosR ⟨hcosRhalf, hcosR1⟩ w hw hzw
  have hpqgap : (⟪Leaves.restComp z w p, Leaves.restComp z w q⟫ : ℝ) ^ 2
      < ‖Leaves.restComp z w p‖ ^ 2 * ‖Leaves.restComp z w q‖ ^ 2 :=
    Leaves.gramGap_pos_of_ne_smul hq0 hnesmul
  set δ : ℝ := ‖Leaves.restComp z w p‖ ^ 2 * ‖Leaves.restComp z w q‖ ^ 2
      - (⟪Leaves.restComp z w p, Leaves.restComp z w q⟫ : ℝ) ^ 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδeq : (⟪Leaves.restComp z w p, Leaves.restComp z w q⟫ : ℝ) ^ 2 + δ
      = ‖Leaves.restComp z w p‖ ^ 2 * ‖Leaves.restComp z w q‖ ^ 2 := by rw [hδdef]; ring
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
  have hA0norm : ‖Sμ • ω + p‖ ≤ 1 := by
    rw [← hbaryμ]
    exact Leaves.norm_barycenter_le_one hαμs (Leaves.integrable_id_of_sphere_support hαμs)
  have hB0norm : ‖Sν • ω + q‖ ≤ 1 := by
    rw [← hbaryν]
    exact Leaves.norm_barycenter_le_one hανs (Leaves.integrable_id_of_sphere_support hανs)
  -- the ideal collapse targets' rest-component (orthogonal to `span{z,w}`) equals `p`/`q`'s own,
  -- since `ω ∈ span{z,w}` (`hωspan`)
  have hzz1 : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hww1 : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwz0 : (⟪w, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzw
  have hωrest : Leaves.restComp z w ω = 0 := by
    unfold Leaves.restComp
    conv_lhs => rw [hωspan]
    simp only [inner_add_right, real_inner_smul_right, hzz1, hww1, hzw, hwz0]
    module
  have hrestA0 : Leaves.restComp z w (Sμ • ω + p) = Leaves.restComp z w p := by
    have hlin : Leaves.restComp z w (Sμ • ω + p)
        = Sμ • Leaves.restComp z w ω + Leaves.restComp z w p := by
      unfold Leaves.restComp
      simp only [inner_add_right, real_inner_smul_right, smul_sub]
      module
    rw [hlin, hωrest, smul_zero, zero_add]
  have hrestB0 : Leaves.restComp z w (Sν • ω + q) = Leaves.restComp z w q := by
    have hlin : Leaves.restComp z w (Sν • ω + q)
        = Sν • Leaves.restComp z w ω + Leaves.restComp z w q := by
      unfold Leaves.restComp
      simp only [inner_add_right, real_inner_smul_right, smul_sub]
      module
    rw [hlin, hωrest, smul_zero, zero_add]
  have hδfinal : (⟪Leaves.restComp z w (Sμ • ω + p), Leaves.restComp z w (Sν • ω + q)⟫ : ℝ) ^ 2 + δ
      ≤ ‖Leaves.restComp z w (Sμ • ω + p)‖ ^ 2 * ‖Leaves.restComp z w (Sν • ω + q)‖ ^ 2 := by
    rw [hrestA0, hrestB0]; exact hδeq.le
  have hrpnorm : ‖Leaves.restComp z w p‖ ≤ 1 := by
    rw [← hrestA0]; exact (Leaves.restComp_norm_le hz hw hzw _).trans hA0norm
  have hrqnorm : ‖Leaves.restComp z w q‖ ≤ 1 := by
    rw [← hrestB0]; exact (Leaves.restComp_norm_le hz hw hzw _).trans hB0norm
  have hδle1 : δ ≤ 1 := by
    rw [hδdef]
    have hrpsq : ‖Leaves.restComp z w p‖ ^ 2 ≤ 1 := by
      nlinarith [hrpnorm, norm_nonneg (Leaves.restComp z w p)]
    have hrqsq : ‖Leaves.restComp z w q‖ ^ 2 ≤ 1 := by
      nlinarith [hrqnorm, norm_nonneg (Leaves.restComp z w q)]
    have hprodle1 : ‖Leaves.restComp z w p‖ ^ 2 * ‖Leaves.restComp z w q‖ ^ 2 ≤ 1 :=
      mul_le_one₀ hrpsq (sq_nonneg _) hrqsq
    linarith [sq_nonneg (⟪Leaves.restComp z w p, Leaves.restComp z w q⟫ : ℝ), hprodle1]
  clear_value G Sμ Sν cc δ
  -- Step 4: reach target `b`, annulus threshold `m`, pole floor `mp` — slack RETUNED relative to
  -- `δ` (not `G`), following `mean-field-axioms-retractability`'s W₂-constant-matching finding
  set ε : ℝ := δ ^ 2 / 20000 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hδsq_le1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδpos.le hδle1
  have hεlt2 : ε < 2 := by rw [hεdef]; linarith [hδsq_le1]
  set b : ℝ := 1 - ε with hbdef
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by rw [hbdef]; linarith, by rw [hbdef]; linarith⟩
  clear_value b
  obtain ⟨m₀, hm₀lb, hm₀ub, hm₀ann⟩ :=
    Leaves.exists_annulus_measure_le (ω := z) (μ := μ + ν) hcosR1
      (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hεpos)
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
  have hμann : (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal ≤ ε := by
    refine ENNReal.toReal_le_of_le_ofReal hεpos.le ?_
    calc μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}
        ≤ (μ + ν) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m₀} := by
          rw [Measure.add_apply]; exact le_add_right (measure_mono hannsub)
      _ ≤ ENNReal.ofReal ε := hm₀ann
  have hνann : (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal ≤ ε := by
    refine ENNReal.toReal_le_of_le_ofReal hεpos.le ?_
    calc ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}
        ≤ (μ + ν) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m₀} := by
          rw [Measure.add_apply]; exact le_add_left (measure_mono hannsub)
      _ ≤ ENNReal.ofReal ε := hm₀ann
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
  -- `n` is forced to `≥ 1` (via `n₀ + 1`, not just `exists_nat_ge`'s raw witness) so the final
  -- block can be time-rescaled to EXACTLY duration `T` (`AttnParams.rescale` divides by `n`,
  -- needing `n ≠ 0`); a larger `n` only helps the reach bound (`slope > 0`), so this costs nothing.
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((logOdds b - logOdds mp) / slope)
  rw [div_le_iff₀ hslopepos] at hn₀
  set n : ℕ := n₀ + 1 with hndef
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [hndef]; positivity
  have hnT0 : (0 : ℝ) ≤ (n : ℝ) * T := by positivity
  have hreach : logOdds b ≤ logOdds mp + 2 * (m - cosR) * ((n : ℝ) * T) := by
    have hmono : (n₀ : ℝ) * slope ≤ (n : ℝ) * slope := by
      rw [hndef]; push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hslopepos.le
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
  haveI : IsProbabilityMeasure (attnMeasureFlow θ μ) := by
    rw [hbrμ]; exact isProbabilityMeasure_measureFlow _ _ μ
  haveI : IsProbabilityMeasure (attnMeasureFlow θ ν) := by
    rw [hbrν]; exact isProbabilityMeasure_measureFlow _ _ ν
  have hPμsphere : (attnMeasureFlow θ μ) (sphere d)ᶜ = 0 := by
    rw [hbrμ]; exact measureFlow_supportedIn_sphere _ hnT0 hμs
  have hPνsphere : (attnMeasureFlow θ ν) (sphere d)ᶜ = 0 := by
    rw [hbrν]; exact measureFlow_supportedIn_sphere _ hnT0 hνs
  -- the retuned `W₂` bounds beat `δ/40`, hence satisfy the perturbation lemma's smallness
  have h2b : 2 * (1 - b) = 2 * ε := by rw [hbdef]; ring
  have hrPbound : Real.sqrt (2 * (1 - b)
      + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
      ≤ Real.sqrt (6 * ε) := by
    rw [h2b]; exact Real.sqrt_le_sqrt (by linarith [hμann])
  have hrQbound : Real.sqrt (2 * (1 - b)
      + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
      ≤ Real.sqrt (6 * ε) := by
    rw [h2b]; exact Real.sqrt_le_sqrt (by linarith [hνann])
  have hδsqpos : 0 < δ ^ 2 := pow_pos hδpos 2
  have hεsqrt_lt : Real.sqrt (6 * ε) < δ / 40 := by
    have hlt : Real.sqrt (6 * ε) < Real.sqrt ((δ / 40) ^ 2) := by
      refine Real.sqrt_lt_sqrt (by positivity) ?_
      rw [hεdef]
      nlinarith [hδsqpos]
    rwa [Real.sqrt_sq (by positivity)] at hlt
  have hrPlt : Real.sqrt (2 * (1 - b)
      + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) < δ / 40 :=
    lt_of_le_of_lt hrPbound hεsqrt_lt
  have hrQlt : Real.sqrt (2 * (1 - b)
      + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) < δ / 40 :=
    lt_of_le_of_lt hrQbound hεsqrt_lt
  have hArP : ‖barycenter (attnMeasureFlow θ μ) - barycenter (μ.map (capCollapseMap z ω cosR))‖
      ≤ Real.sqrt (2 * (1 - b)
          + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) :=
    (Leaves.norm_barycenter_sub_le_W2 hPμsphere hαμs).trans hW2μ
  have hBrQ : ‖barycenter (attnMeasureFlow θ ν) - barycenter (ν.map (capCollapseMap z ω cosR))‖
      ≤ Real.sqrt (2 * (1 - b)
          + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) :=
    (Leaves.norm_barycenter_sub_le_W2 hPνsphere hανs).trans hW2ν
  have hrPsmall8 : Real.sqrt (2 * (1 - b)
      + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) ≤ δ / 8 := by
    linarith [hrPlt]
  have hrQsmall8 : Real.sqrt (2 * (1 - b)
      + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) ≤ δ / 8 := by
    linarith [hrQlt]
  have hsmall20 : 20 * (Real.sqrt (2 * (1 - b)
        + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
      + Real.sqrt (2 * (1 - b)
        + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)) < δ := by
    linarith [hrPlt, hrQlt]
  -- Rescale the single block to hit `T` EXACTLY (`n·T / n = T`), reusing every fact already
  -- established about `θ` via `attnMeasureFlow_singleton_rescale_eq` (same resulting measure).
  set θ' : AttnSchedule d := [(pPark z ω cosR ((n : ℝ) * T) hnT0).rescale hnpos] with hθ'def
  have hθ'dur : AttnSchedule.durationSum θ' = T := by
    rw [hθ'def]
    simp only [AttnSchedule.durationSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [AttnParams.rescale_duration]
    show (n : ℝ) * T / (n : ℝ) = T
    field_simp
  have hθ'switches : AttnSchedule.switches θ' ≤ 2 := by
    show [(pPark z ω cosR ((n : ℝ) * T) hnT0).rescale hnpos].length ≤ 2
    simp
  have hflowEqμ : attnMeasureFlow θ' μ = attnMeasureFlow θ μ := by
    rw [hθ'def, hθdef]
    exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T) hnT0) hnpos μ hμs
  have hflowEqν : attnMeasureFlow θ' ν = attnMeasureFlow θ ν := by
    rw [hθ'def, hθdef]
    exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T) hnT0) hnpos ν hνs
  refine ⟨θ', hθ'dur, hθ'switches, ?_, ?_, ?_⟩
  · intro γ₂
    rw [hflowEqμ, hflowEqν]
    rw [hbaryμ] at hArP
    rw [hbaryν] at hBrQ
    exact Leaves.ne_smul_of_restComp_gramGap_perturbation hz hw hzw hA0norm hB0norm hArP hBrQ hδfinal
      hδpos hrPsmall8 hrQsmall8 hsmall20 γ₂
  · have hex := @exists_meanFieldFlow d (pPark z ω cosR ((n : ℝ) * T) hnT0) μ ‹_› hμs
    set Φ := hex.choose with hΦdef
    have hΦspec : IsMeanFieldFlow (pPark z ω cosR ((n : ℝ) * T) hnT0) μ Φ := hex.choose_spec
    set Φd := Φ (pPark z ω cosR ((n : ℝ) * T) hnT0).duration with hΦddef
    have hΦstep : attnMeasureFlow θ μ = μ.map Φd := by
      show attnStep (pPark z ω cosR ((n : ℝ) * T) hnT0) μ = _
      unfold attnStep
      rw [dif_pos ⟨‹_›, hμs⟩]
    refine ⟨Φd, hΦspec.measurable ((pPark z ω cosR ((n : ℝ) * T) hnT0).duration)
      ⟨hnT0, le_rfl⟩, ?_, ?_⟩
    · rw [hflowEqμ]; exact hΦstep
    intro x hxsphere hxU
    have hxcap : ¬ (cosR < (⟪z, x⟫ : ℝ)) := fun hlt => hxU (hcapsub x hxsphere hlt)
    have hxle : (⟪z, x⟫ : ℝ) ≤ cosR := not_lt.mp hxcap
    exact attnFlow_id_of_inner_le z ω cosR ((n : ℝ) * T) hnT0 hμs Φ hΦspec hxsphere hxle
      ⟨hnT0, le_rfl⟩
  · -- **Bystander-fixing conjunct.** Any sphere-supported probability measure whose mass avoids
    -- the carrier `U` also avoids the mass-gap cap (`hcapsub` puts the cap inside `U`), so the
    -- single-block schedule `θ` (equivalently its exact-duration rescale `θ'`) fixes it exactly,
    -- via the just-banked `attnMeasureFlow_pPark_eq_of_off_cap` and the rescale bridge.
    intro ρ _ hρs hρU
    rw [supportedIn] at hρs
    rw [supportedIn, compl_compl] at hρU
    have hρcap : ρ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_union_null hρU hρs)
      by_cases hxs : x ∈ sphere d
      · exact Or.inl (hcapsub x hxs hx)
      · exact Or.inr hxs
    have hflowEqρ : attnMeasureFlow θ' ρ = attnMeasureFlow θ ρ := by
      rw [hθ'def, hθdef]
      exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T) hnT0) hnpos
        ρ hρs
    rw [hflowEqρ, hθdef]
    exact attnMeasureFlow_pPark_eq_of_off_cap z ω cosR ((n : ℝ) * T) hnT0 ρ hρs hρcap

set_option maxHeartbeats 1600000 in
/-- **Caller-supplied-cap sibling of `barycenter_nonColinear_of_massGapCollapse_meanField`.** Same
conclusion, but the mass-gap cap `z, cosR` (together with its carrier-containment `hcapsub` and its
mass-gap witness `hmassne`) is a CALLER-SUPPLIED explicit argument instead of being produced
internally via `Leaves.exists_cap_measure_ne_subset` from an open carrier `U` and `hμU`/`hνU`. This
is the form actually consumed downstream (`GenRestNearBall.lean`, `MidLevel.lean`), where the caller
already has a cap in hand and only needs `hcapsub` (not `hUopen`/`hμU`/`hνU` themselves) to fix
`Φ`'s off-`U` behaviour. The proof is a verbatim replay of
`barycenter_nonColinear_of_massGapCollapse_meanField`'s body from right after its internal
`exists_cap_measure_ne_subset` call: Steps 2 through 4 (pigeonhole pole, rest-component gramGap from
`hgenRest`, collapse-barycenter gap, reach/annulus/pole-floor bookkeeping, single-block mean-field
flow, rescale to duration `T`) are unchanged. -/
theorem barycenter_nonColinear_of_massGapCollapse_meanField_callerCap (μ ν : Measure (Eucl d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (U : Set (Eucl d)) (z : Eucl d) (cosR : ℝ) (hzsphere : z ∈ sphere d)
    (hcosRhalf : 1 / 2 < cosR) (hcosR1 : cosR < 1)
    (hcapsub : ∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∈ U)
    (hmassne : μ {x | cosR < (⟪z, x⟫ : ℝ)} ≠ ν {x | cosR < (⟪z, x⟫ : ℝ)})
    (hgenRest : ∀ w : Eucl d, ‖w‖ = 1 → (⟪z, w⟫ : ℝ) = 0 →
      Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν) ≠ 0 ∧
      ∀ c : ℝ, Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ)
        ≠ c • Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν)) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧ AttnSchedule.switches θ ≤ 2 ∧
      (∀ γ₂ : ℝ, barycenter (attnMeasureFlow θ μ) ≠ γ₂ • barycenter (attnMeasureFlow θ ν)) ∧
      ∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ μ = μ.map Φ ∧
        ∀ x ∈ sphere d, x ∉ U → Φ x = x := by
  rw [supportedIn] at hμs hνs hμ hν
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
  obtain ⟨ω, hωnorm, hzωcap, hωne, hωspan⟩ :=
    Leaves.exists_pole_in_cap_ne hz hw hzw hcosRlb hcosR1 v
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hωnorm]
  set cval : ℝ := (⟪z, ω⟫ : ℝ) with hcval
  have hcval1 : cval ≤ 1 := by
    rw [hcval]; calc (⟪z, ω⟫ : ℝ) ≤ ‖z‖ * ‖ω‖ := real_inner_le_norm z ω
      _ = 1 := by rw [hz, hωnorm, mul_one]
  have hcvalpos : (0 : ℝ) < cval := by rw [hcval] at hzωcap ⊢; linarith
  -- Step 2′: the rest-component gramGap, from `hgenRest` — fixed BEFORE Step 4's `b, m, n`
  obtain ⟨hq0, hnesmul⟩ := hgenRest w hw hzw
  have hpqgap : (⟪Leaves.restComp z w p, Leaves.restComp z w q⟫ : ℝ) ^ 2
      < ‖Leaves.restComp z w p‖ ^ 2 * ‖Leaves.restComp z w q‖ ^ 2 :=
    Leaves.gramGap_pos_of_ne_smul hq0 hnesmul
  set δ : ℝ := ‖Leaves.restComp z w p‖ ^ 2 * ‖Leaves.restComp z w q‖ ^ 2
      - (⟪Leaves.restComp z w p, Leaves.restComp z w q⟫ : ℝ) ^ 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδeq : (⟪Leaves.restComp z w p, Leaves.restComp z w q⟫ : ℝ) ^ 2 + δ
      = ‖Leaves.restComp z w p‖ ^ 2 * ‖Leaves.restComp z w q‖ ^ 2 := by rw [hδdef]; ring
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
  have hA0norm : ‖Sμ • ω + p‖ ≤ 1 := by
    rw [← hbaryμ]
    exact Leaves.norm_barycenter_le_one hαμs (Leaves.integrable_id_of_sphere_support hαμs)
  have hB0norm : ‖Sν • ω + q‖ ≤ 1 := by
    rw [← hbaryν]
    exact Leaves.norm_barycenter_le_one hανs (Leaves.integrable_id_of_sphere_support hανs)
  -- the ideal collapse targets' rest-component (orthogonal to `span{z,w}`) equals `p`/`q`'s own,
  -- since `ω ∈ span{z,w}` (`hωspan`)
  have hzz1 : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hww1 : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwz0 : (⟪w, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzw
  have hωrest : Leaves.restComp z w ω = 0 := by
    unfold Leaves.restComp
    conv_lhs => rw [hωspan]
    simp only [inner_add_right, real_inner_smul_right, hzz1, hww1, hzw, hwz0]
    module
  have hrestA0 : Leaves.restComp z w (Sμ • ω + p) = Leaves.restComp z w p := by
    have hlin : Leaves.restComp z w (Sμ • ω + p)
        = Sμ • Leaves.restComp z w ω + Leaves.restComp z w p := by
      unfold Leaves.restComp
      simp only [inner_add_right, real_inner_smul_right, smul_sub]
      module
    rw [hlin, hωrest, smul_zero, zero_add]
  have hrestB0 : Leaves.restComp z w (Sν • ω + q) = Leaves.restComp z w q := by
    have hlin : Leaves.restComp z w (Sν • ω + q)
        = Sν • Leaves.restComp z w ω + Leaves.restComp z w q := by
      unfold Leaves.restComp
      simp only [inner_add_right, real_inner_smul_right, smul_sub]
      module
    rw [hlin, hωrest, smul_zero, zero_add]
  have hδfinal : (⟪Leaves.restComp z w (Sμ • ω + p), Leaves.restComp z w (Sν • ω + q)⟫ : ℝ) ^ 2 + δ
      ≤ ‖Leaves.restComp z w (Sμ • ω + p)‖ ^ 2 * ‖Leaves.restComp z w (Sν • ω + q)‖ ^ 2 := by
    rw [hrestA0, hrestB0]; exact hδeq.le
  have hrpnorm : ‖Leaves.restComp z w p‖ ≤ 1 := by
    rw [← hrestA0]; exact (Leaves.restComp_norm_le hz hw hzw _).trans hA0norm
  have hrqnorm : ‖Leaves.restComp z w q‖ ≤ 1 := by
    rw [← hrestB0]; exact (Leaves.restComp_norm_le hz hw hzw _).trans hB0norm
  have hδle1 : δ ≤ 1 := by
    rw [hδdef]
    have hrpsq : ‖Leaves.restComp z w p‖ ^ 2 ≤ 1 := by
      nlinarith [hrpnorm, norm_nonneg (Leaves.restComp z w p)]
    have hrqsq : ‖Leaves.restComp z w q‖ ^ 2 ≤ 1 := by
      nlinarith [hrqnorm, norm_nonneg (Leaves.restComp z w q)]
    have hprodle1 : ‖Leaves.restComp z w p‖ ^ 2 * ‖Leaves.restComp z w q‖ ^ 2 ≤ 1 :=
      mul_le_one₀ hrpsq (sq_nonneg _) hrqsq
    linarith [sq_nonneg (⟪Leaves.restComp z w p, Leaves.restComp z w q⟫ : ℝ), hprodle1]
  clear_value G Sμ Sν cc δ
  -- Step 4: reach target `b`, annulus threshold `m`, pole floor `mp` — slack RETUNED relative to
  -- `δ` (not `G`), following `mean-field-axioms-retractability`'s W₂-constant-matching finding
  set ε : ℝ := δ ^ 2 / 20000 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hδsq_le1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδpos.le hδle1
  have hεlt2 : ε < 2 := by rw [hεdef]; linarith [hδsq_le1]
  set b : ℝ := 1 - ε with hbdef
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by rw [hbdef]; linarith, by rw [hbdef]; linarith⟩
  clear_value b
  obtain ⟨m₀, hm₀lb, hm₀ub, hm₀ann⟩ :=
    Leaves.exists_annulus_measure_le (ω := z) (μ := μ + ν) hcosR1
      (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hεpos)
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
  have hμann : (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal ≤ ε := by
    refine ENNReal.toReal_le_of_le_ofReal hεpos.le ?_
    calc μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}
        ≤ (μ + ν) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m₀} := by
          rw [Measure.add_apply]; exact le_add_right (measure_mono hannsub)
      _ ≤ ENNReal.ofReal ε := hm₀ann
  have hνann : (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal ≤ ε := by
    refine ENNReal.toReal_le_of_le_ofReal hεpos.le ?_
    calc ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}
        ≤ (μ + ν) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m₀} := by
          rw [Measure.add_apply]; exact le_add_left (measure_mono hannsub)
      _ ≤ ENNReal.ofReal ε := hm₀ann
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
  -- `n` is forced to `≥ 1` (via `n₀ + 1`, not just `exists_nat_ge`'s raw witness) so the final
  -- block can be time-rescaled to EXACTLY duration `T` (`AttnParams.rescale` divides by `n`,
  -- needing `n ≠ 0`); a larger `n` only helps the reach bound (`slope > 0`), so this costs nothing.
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((logOdds b - logOdds mp) / slope)
  rw [div_le_iff₀ hslopepos] at hn₀
  set n : ℕ := n₀ + 1 with hndef
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [hndef]; positivity
  have hnT0 : (0 : ℝ) ≤ (n : ℝ) * T := by positivity
  have hreach : logOdds b ≤ logOdds mp + 2 * (m - cosR) * ((n : ℝ) * T) := by
    have hmono : (n₀ : ℝ) * slope ≤ (n : ℝ) * slope := by
      rw [hndef]; push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hslopepos.le
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
  haveI : IsProbabilityMeasure (attnMeasureFlow θ μ) := by
    rw [hbrμ]; exact isProbabilityMeasure_measureFlow _ _ μ
  haveI : IsProbabilityMeasure (attnMeasureFlow θ ν) := by
    rw [hbrν]; exact isProbabilityMeasure_measureFlow _ _ ν
  have hPμsphere : (attnMeasureFlow θ μ) (sphere d)ᶜ = 0 := by
    rw [hbrμ]; exact measureFlow_supportedIn_sphere _ hnT0 hμs
  have hPνsphere : (attnMeasureFlow θ ν) (sphere d)ᶜ = 0 := by
    rw [hbrν]; exact measureFlow_supportedIn_sphere _ hnT0 hνs
  -- the retuned `W₂` bounds beat `δ/40`, hence satisfy the perturbation lemma's smallness
  have h2b : 2 * (1 - b) = 2 * ε := by rw [hbdef]; ring
  have hrPbound : Real.sqrt (2 * (1 - b)
      + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
      ≤ Real.sqrt (6 * ε) := by
    rw [h2b]; exact Real.sqrt_le_sqrt (by linarith [hμann])
  have hrQbound : Real.sqrt (2 * (1 - b)
      + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
      ≤ Real.sqrt (6 * ε) := by
    rw [h2b]; exact Real.sqrt_le_sqrt (by linarith [hνann])
  have hδsqpos : 0 < δ ^ 2 := pow_pos hδpos 2
  have hεsqrt_lt : Real.sqrt (6 * ε) < δ / 40 := by
    have hlt : Real.sqrt (6 * ε) < Real.sqrt ((δ / 40) ^ 2) := by
      refine Real.sqrt_lt_sqrt (by positivity) ?_
      rw [hεdef]
      nlinarith [hδsqpos]
    rwa [Real.sqrt_sq (by positivity)] at hlt
  have hrPlt : Real.sqrt (2 * (1 - b)
      + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) < δ / 40 :=
    lt_of_le_of_lt hrPbound hεsqrt_lt
  have hrQlt : Real.sqrt (2 * (1 - b)
      + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) < δ / 40 :=
    lt_of_le_of_lt hrQbound hεsqrt_lt
  have hArP : ‖barycenter (attnMeasureFlow θ μ) - barycenter (μ.map (capCollapseMap z ω cosR))‖
      ≤ Real.sqrt (2 * (1 - b)
          + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) :=
    (Leaves.norm_barycenter_sub_le_W2 hPμsphere hαμs).trans hW2μ
  have hBrQ : ‖barycenter (attnMeasureFlow θ ν) - barycenter (ν.map (capCollapseMap z ω cosR))‖
      ≤ Real.sqrt (2 * (1 - b)
          + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) :=
    (Leaves.norm_barycenter_sub_le_W2 hPνsphere hανs).trans hW2ν
  have hrPsmall8 : Real.sqrt (2 * (1 - b)
      + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) ≤ δ / 8 := by
    linarith [hrPlt]
  have hrQsmall8 : Real.sqrt (2 * (1 - b)
      + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) ≤ δ / 8 := by
    linarith [hrQlt]
  have hsmall20 : 20 * (Real.sqrt (2 * (1 - b)
        + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
      + Real.sqrt (2 * (1 - b)
        + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)) < δ := by
    linarith [hrPlt, hrQlt]
  -- Rescale the single block to hit `T` EXACTLY (`n·T / n = T`), reusing every fact already
  -- established about `θ` via `attnMeasureFlow_singleton_rescale_eq` (same resulting measure).
  set θ' : AttnSchedule d := [(pPark z ω cosR ((n : ℝ) * T) hnT0).rescale hnpos] with hθ'def
  have hθ'dur : AttnSchedule.durationSum θ' = T := by
    rw [hθ'def]
    simp only [AttnSchedule.durationSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [AttnParams.rescale_duration]
    show (n : ℝ) * T / (n : ℝ) = T
    field_simp
  have hθ'switches : AttnSchedule.switches θ' ≤ 2 := by
    show [(pPark z ω cosR ((n : ℝ) * T) hnT0).rescale hnpos].length ≤ 2
    simp
  have hflowEqμ : attnMeasureFlow θ' μ = attnMeasureFlow θ μ := by
    rw [hθ'def, hθdef]
    exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T) hnT0) hnpos μ hμs
  have hflowEqν : attnMeasureFlow θ' ν = attnMeasureFlow θ ν := by
    rw [hθ'def, hθdef]
    exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T) hnT0) hnpos ν hνs
  refine ⟨θ', hθ'dur, hθ'switches, ?_, ?_⟩
  · intro γ₂
    rw [hflowEqμ, hflowEqν]
    rw [hbaryμ] at hArP
    rw [hbaryν] at hBrQ
    exact Leaves.ne_smul_of_restComp_gramGap_perturbation hz hw hzw hA0norm hB0norm hArP hBrQ hδfinal
      hδpos hrPsmall8 hrQsmall8 hsmall20 γ₂
  · have hex := @exists_meanFieldFlow d (pPark z ω cosR ((n : ℝ) * T) hnT0) μ ‹_› hμs
    set Φ := hex.choose with hΦdef
    have hΦspec : IsMeanFieldFlow (pPark z ω cosR ((n : ℝ) * T) hnT0) μ Φ := hex.choose_spec
    set Φd := Φ (pPark z ω cosR ((n : ℝ) * T) hnT0).duration with hΦddef
    have hΦstep : attnMeasureFlow θ μ = μ.map Φd := by
      show attnStep (pPark z ω cosR ((n : ℝ) * T) hnT0) μ = _
      unfold attnStep
      rw [dif_pos ⟨‹_›, hμs⟩]
    refine ⟨Φd, hΦspec.measurable ((pPark z ω cosR ((n : ℝ) * T) hnT0).duration)
      ⟨hnT0, le_rfl⟩, ?_, ?_⟩
    · rw [hflowEqμ]; exact hΦstep
    intro x hxsphere hxU
    have hxcap : ¬ (cosR < (⟪z, x⟫ : ℝ)) := fun hlt => hxU (hcapsub x hxsphere hlt)
    have hxle : (⟪z, x⟫ : ℝ) ≤ cosR := not_lt.mp hxcap
    exact attnFlow_id_of_inner_le z ω cosR ((n : ℝ) * T) hnT0 hμs Φ hΦspec hxsphere hxle
      ⟨hnT0, le_rfl⟩

/-- **Lemma 3.4, Part 1, mean-field form** (paper-faithful statement, `γ₁ = 1` case). Thin wrapper
around `barycenter_ne_of_massGapCollapse_meanField`, which does not need the equal-barycenter
hypothesis at all. -/
theorem lemma_3_4_part1_meanField (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (_hbar : barycenter μ = barycenter ν)
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hμU : supportedIn μ U) (hνU : supportedIn ν U) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      barycenter (attnMeasureFlow θ μ) ≠ barycenter (attnMeasureFlow θ ν) ∧
      (∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ μ = μ.map Φ ∧
        ∀ x ∈ sphere d, x ∉ U → Φ x = x) ∧
      ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        supportedIn ρ Uᶜ → attnMeasureFlow θ ρ = ρ :=
  barycenter_ne_of_massGapCollapse_meanField μ ν T hT hne hμs hνs hμ hν U hUopen hμU hνU

end MeasureToMeasure.Leaves
