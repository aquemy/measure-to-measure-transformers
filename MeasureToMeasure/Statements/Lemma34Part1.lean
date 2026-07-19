import MeasureToMeasure.Statements.MidLevel
import MeasureToMeasure.Leaves.CapMassGap
import MeasureToMeasure.Leaves.DistinctDim
import MeasureToMeasure.Leaves.PoleGeometry
import MeasureToMeasure.Leaves.CapPole
import MeasureToMeasure.Leaves.OffCenterCollapse
import MeasureToMeasure.Leaves.OffCenterW2
import MeasureToMeasure.Leaves.AnnulusMass
import MeasureToMeasure.Leaves.GeodesicHullConvex
import MeasureToMeasure.Leaves.BarycenterCollapseGap
import MeasureToMeasure.Leaves.FlowStack
import MeasureToMeasure.Leaves.GatedPark

/-!
# Lemma 3.4, Part 1 — discharged (App. B.3, `γ₁ = 1` case)

The `γ₁ = 1` half of Lemma 3.4: for two **distinct** probability measures on the orthant `Q₁^{d-1}`
with equal barycenters, a single (linear, `V ≡ 0`) parameter choice makes the flowed barycenters
differ while fixing the sphere off any open carrier.

This module discharges what used to be `axiom lemma_3_4_part1` (in `Statements/MidLevel.lean`) into a
kernel-clean `theorem`. It lives here, not in `MidLevel`, only to avoid an import cycle: the proof
cites `Leaves.two_le_d_of_distinct`, which imports `MidLevel` for `orthant`.

The construction is the paper's App. B.3 Part 1 (`paper.pdf`, p.35), assembled from the banked leaves:

* `exists_cap_measure_ne_subset` — a mass-gap spherical cap `{cos R < ⟪z,·⟫} ⊆ U` with
  `μ(cap) ≠ ν(cap)` (Besicovitch differentiation), `cos R > 1/2` so the cap has radius `< 1`.
* The **pigeonhole pole** `ω`: any unit vector strictly inside the cap off the single forced vector
  `v = c⁻¹(∫_{capᶜ}(ν−μ))` separates the two collapse barycenters
  `ℰ_{α_μ} = μ(cap)·ω + ∫_{capᶜ}x dμ` (`barycenter_map_capCollapse`). Such an `ω` exists by the
  cap-rotation `exists_pole_in_cap_ne`, fed a unit `w ⊥ z` from `exists_unit_orthogonal` — whence the
  only use of `2 ≤ d`, itself recovered from `μ ≠ ν` by `two_le_d_of_distinct`.
* The **flow**: `θ` stacks `n` copies of one gated block (`flowMap_replicate` realises effective time
  `n·T` at the fixed axiom time `T` — the honest form of the paper's "take `T` large"). Reaching to
  `b → 1` on the sub-cap `{⟪z,·⟫ ≥ m}` (`W2_measureFlow_offCenter_collapse_le`, with the tangential
  pole floor `mp` from `inner_pole_lower_bound`) and a thin annulus (`exists_annulus_measure_le`) makes
  `W₂(measureFlow θ T μ, α_μ)` as small as the barycenter gap needs.
* **Separation**: the barycenter is `W₂`-Lipschitz (`barycenter_ne_of_W2_gap`), so the flowed
  barycenters inherit the collapse gap. **Fixing**: off `U` the gate is inactive
  (`flowMap_gatedBlock_id_of_inner_le`), so `flowMap θ T` is the identity there.

**Fidelity / soundness** (carried over from the axiom's notes):
* The hypotheses `μ ≠ ν`, `IsProbabilityMeasure`, sphere+orthant support are the paper's; the original
  hypothesis-free stub was kernel-refuted (`Regression.Refuted`, finding F11): with `μ = ν` no `θ`
  separates the identical flowed barycenters, and heavy-tailed orthant measures have junk-zero
  barycenters (F12). Sphere support makes the identity integrable and the barycenter genuine.
* The fixing clause is stated relative to an **open carrier `U`** (`φ = id` on the sphere off `U`),
  the sound form of the paper's "identity off `conv_g supp μ₀ ∪ conv_g supp ν₀`" — as printed that is
  refutable for atomic inputs (finding F17 / erratum E4).
* Layer (F14): the LINEAR layer, faithfully — the part-1 construction sets `V ≡ 0`, so the field never
  reads the measure. The discharge in fact needs neither `V` nor the equal-barycenter hypothesis
  `hbar`: the mass-gap collapse separates the barycenters unconditionally, so `hbar` is retained only
  to match the paper's (and the former axiom's) statement verbatim.
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Leaves (barycenter)
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

set_option maxHeartbeats 1200000 in
/-- **Lemma 3.4, Part 1** (`γ₁ = 1` case), machine-checked. For two distinct probability measures on
`𝕊^{d-1} ∩ Q₁^{d-1}` with equal barycenters and a common open carrier `U`, some linear schedule `θ`
makes the flowed barycenters differ while fixing the sphere off `U`. -/
theorem lemma_3_4_part1 (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (_hbar : barycenter μ = barycenter ν)
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hμU : supportedIn μ U) (hνU : supportedIn ν U) :
    ∃ θ : Params d,
      barycenter (measureFlow θ T μ) ≠ barycenter (measureFlow θ T ν) ∧
      ∀ x ∈ sphere d, x ∉ U → flowMap θ T x = x := by
  -- unfold `supportedIn`
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
  -- the collapse pole: unit, strictly inside the cap, off `v`
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
  -- collapse map: measurable, maps the sphere into itself; `αμ, αν` are sphere-supported probabilities
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
  -- `G ≤ 2` (each collapse barycenter has norm ≤ 1)
  have hGle2 : G ≤ 2 := by
    rw [hG]
    calc ‖barycenter (μ.map (capCollapseMap z ω cosR)) - barycenter (ν.map (capCollapseMap z ω cosR))‖
        ≤ ‖barycenter (μ.map (capCollapseMap z ω cosR))‖
          + ‖barycenter (ν.map (capCollapseMap z ω cosR))‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add
          (Leaves.norm_barycenter_le_one hαμs (Leaves.integrable_id_of_sphere_support hαμs))
          (Leaves.norm_barycenter_le_one hανs (Leaves.integrable_id_of_sphere_support hανs))
      _ = 2 := by norm_num
  -- make the (huge) norm `G` opaque so the numeric `nlinarith`s do not unfold it
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
  -- pole floor `mp` (tangential Cauchy–Schwarz)
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
  -- reach budget: stack enough blocks
  set slope : ℝ := 2 * (m - cosR) * T with hslope
  have hslopepos : 0 < slope := by
    rw [hslope]; exact mul_pos (mul_pos two_pos (by linarith)) hT
  obtain ⟨n, hn⟩ := exists_nat_ge ((logOdds b - logOdds mp) / slope)
  rw [div_le_iff₀ hslopepos] at hn
  have hnT0 : (0 : ℝ) ≤ (n : ℝ) * T := by positivity
  have hreach : logOdds b ≤ logOdds mp + 2 * (m - cosR) * ((n : ℝ) * T) := by
    have : 2 * (m - cosR) * ((n : ℝ) * T) = (n : ℝ) * slope := by rw [hslope]; ring
    rw [this]; linarith
  set block : Block d := gatedBlock hz hωnorm hcosRlb hnT0 with hblock
  set θ : Params d := List.replicate n block with hθ
  have hflowθ : flowMap θ T = flowMap [block] ((n : ℝ) * T) := by
    rw [hθ]; exact flowMap_replicate_eq_singleton block n T
  have hPμeq : measureFlow θ T μ = measureFlow [block] ((n : ℝ) * T) μ := by
    rw [measureFlow_map, measureFlow_map, hflowθ]
  have hPνeq : measureFlow θ T ν = measureFlow [block] ((n : ℝ) * T) ν := by
    rw [measureFlow_map, measureFlow_map, hflowθ]
  have hW2μ := W2_measureFlow_offCenter_collapse_le hz hωnorm hcosRlb hcosR0 hnT0
    hmcval hmlb hb hmp hpole hreach hμs
  have hW2ν := W2_measureFlow_offCenter_collapse_le hz hωnorm hcosRlb hcosR0 hnT0
    hmcval hmlb hb hmp hpole hreach hνs
  rw [← hblock, ← hPμeq] at hW2μ
  rw [← hblock, ← hPνeq] at hW2ν
  -- the two `W₂` bounds are each `< G/2`
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
  -- assemble
  haveI : IsProbabilityMeasure (measureFlow θ T μ) := isProbabilityMeasure_measureFlow θ T μ
  haveI : IsProbabilityMeasure (measureFlow θ T ν) := isProbabilityMeasure_measureFlow θ T ν
  have hPμsphere : (measureFlow θ T μ) (sphere d)ᶜ = 0 := measureFlow_supportedIn_sphere θ hT.le hμs
  have hPνsphere : (measureFlow θ T ν) (sphere d)ᶜ = 0 := measureFlow_supportedIn_sphere θ hT.le hνs
  refine ⟨θ, ?_, ?_⟩
  · refine Leaves.barycenter_ne_of_W2_gap hPμsphere hPνsphere hαμs hανs hW2μ hW2ν ?_
    rw [← hG]
    calc Real.sqrt (2 * (1 - b)
            + 4 * (μ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
          + Real.sqrt (2 * (1 - b)
            + 4 * (ν {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
        < G / 2 + G / 2 := add_lt_add hRμ hRν
      _ = G := by ring
  · intro x hxsphere hxU
    have hxcap : ¬ (cosR < (⟪z, x⟫ : ℝ)) := fun hlt => hxU (hcapsub x hxsphere hlt)
    have hxle : (⟪z, x⟫ : ℝ) ≤ cosR := not_lt.mp hxcap
    rw [hflowθ]
    exact flowMap_gatedBlock_id_of_inner_le hz hωnorm hcosRlb hnT0 ((n : ℝ) * T) hxle

end MeasureToMeasure.Statements
