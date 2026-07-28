import MeasureToMeasure.Leaves.PoleGeometry
import MeasureToMeasure.Leaves.CapPoleAvoiding
import MeasureToMeasure.Leaves.OffSpanMargin
import MeasureToMeasure.Leaves.OffCenterCollapse
import MeasureToMeasure.Leaves.OffCenterW2
import MeasureToMeasure.Leaves.AnnulusMass
import MeasureToMeasure.Leaves.BarycenterCollapseGap
import MeasureToMeasure.Leaves.GatedBlockMeanFieldBridge
import MeasureToMeasure.Leaves.MeanFieldPark
import MeasureToMeasure.Leaves.AttnRescale
import MeasureToMeasure.Statements.SupportedIn

/-!
# Asymmetric cap collapse: the μ-side quantitative engine, packaged once

The mass-gap-cap-collapse construction of `Leaves/Lemma34Part1MeanField.lean` runs its Step 4
(reach target, annulus threshold, pole floor, reach budget, `pPark` block, `W₂` transfer, exact
rescale) INLINE, twice, with a two-sided `G`-budget tied to the pair `(μ, ν)` and an orthant-derived
cap from `exists_cap_measure_ne_subset`. The asymmetric-cap route to a non-vacuous `lemma_3_4_part2`
re-discharge (see the `mean-field-axioms-retractability` notes) needs the SAME engine on ONE measure
at a time, for a cap that is GIVEN (not constructed), with a one-sided `ε`-budget: a single `pPark`
block of exact duration `T2` whose output barycenter is `ε`-close to the ideal collapse target
`Sμ'·ω + p'` (identified by `barycenter_map_capCollapse`), and which EXACTLY fixes every off-cap
sphere probability measure (`attnMeasureFlow_pPark_eq_of_off_cap` + the rescale bridge).

No orthant hypotheses appear anywhere: the cap `{cosR < ⟪z, ·⟫}` and its pole `ω` are inputs, so
`exists_cap_measure_ne_subset` is never called and the assembly (or any future consumer) chooses
them freely. The budget arithmetic replaces the source's `b := 1 - G²/32` by `b := 1 - e²/16` with
`e := min ε 1` (annulus mass `≤ e²/16` via `exists_annulus_measure_le` on `μ'` alone), giving
`√(2(1-b) + 4·annulus) ≤ √(3e²/8) < e ≤ ε` through `norm_barycenter_sub_le_W2`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Axioms MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ} [NeZero d]

set_option maxHeartbeats 1200000 in
/-- **Single-measure ε-approximate cap collapse with exact off-cap fixing.** For a sphere-supported
probability measure `μ'` and a GIVEN cap `{cosR < ⟪z, ·⟫}` (with `cosR ∈ (1/2, 1)`) containing the
given pole `ω`, some single attention block `p` of duration EXACTLY `T2` pushes `μ'`'s barycenter to
within `ε` of the ideal collapse target `μ'(cap)·ω + ∫_{capᶜ} x dμ'`, while fixing EXACTLY every
sphere-supported probability measure that puts no mass on the cap, and while keeping every
sphere-supported probability measure carried by a measurable region `S` containing the cap's
sphere-trace carried by `S` (region-generic forward invariance,
`attnMeasureFlow_pPark_supportedIn_of_cap_subset` through the rescale bridge). Witness:
`pPark z ω cosR (n·T2)` rescaled by the reach-budget `n ≥ 1`; the barycenter estimate transfers
from the linear layer's `W2_measureFlow_offCenter_collapse_le` through
`norm_barycenter_sub_le_W2` and the `pPark`/`gatedBlock` bridge. -/
theorem exists_collapse_block_barycenter_close (μ' : Measure (Eucl d)) [IsProbabilityMeasure μ']
    (hμ's : supportedIn μ' (sphere d)) {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1)
    {cosR : ℝ} (hcosR : cosR ∈ Set.Ioo (1 / 2 : ℝ) 1) (hωcap : cosR < (⟪z, ω⟫ : ℝ))
    {T2 : ℝ} (hT2 : 0 < T2) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : AttnParams d, p.duration = T2 ∧
      ‖barycenter (attnMeasureFlow [p] μ')
        - ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
          + ∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ')‖ < ε ∧
      (∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        ρ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} = 0 → attnMeasureFlow [p] ρ = ρ) ∧
      ∀ S : Set (Eucl d), MeasurableSet S →
        (∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∈ S) →
        ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
          supportedIn ρ S → supportedIn (attnMeasureFlow [p] ρ) S := by
  rw [supportedIn] at hμ's
  obtain ⟨hcosRhalf, hcosR1⟩ := hcosR
  have hcosRlb : (-1 : ℝ) ≤ cosR := by linarith
  have hcosR0 : (0 : ℝ) ≤ cosR := by linarith
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  set cval : ℝ := (⟪z, ω⟫ : ℝ) with hcval
  have hcval1 : cval ≤ 1 := by
    rw [hcval]
    calc (⟪z, ω⟫ : ℝ) ≤ ‖z‖ * ‖ω‖ := real_inner_le_norm z ω
      _ = 1 := by rw [hz, hω, mul_one]
  have hcvalpos : (0 : ℝ) < cval := by linarith
  -- the ideal collapse target
  have hbary : barycenter (μ'.map (capCollapseMap z ω cosR))
      = (μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
        + ∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ' :=
    barycenter_map_capCollapse hμ's
  -- the collapsed measure is a sphere-supported probability measure
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
  have hαμs : (μ'.map (capCollapseMap z ω cosR)) (sphere d)ᶜ = 0 := by
    rw [Measure.map_apply hgmeas hmscompl]
    refine measure_mono_null (fun x hx => ?_) hμ's
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
    exact fun hxs => hx (hgsphere x hxs)
  haveI hαμprob : IsProbabilityMeasure (μ'.map (capCollapseMap z ω cosR)) :=
    ⟨by rw [Measure.map_apply hgmeas MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩
  -- one-sided ε-budget: reach target `b`, annulus threshold `m`, pole floor `mp`
  set e : ℝ := min ε 1 with hedef
  have he0 : (0 : ℝ) < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have he2le1 : e ^ 2 ≤ 1 := pow_le_one₀ he0.le he1
  have he2pos : (0 : ℝ) < e ^ 2 := pow_pos he0 2
  set b : ℝ := 1 - e ^ 2 / 16 with hbdef
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by rw [hbdef]; linarith, by rw [hbdef]; linarith⟩
  clear_value b
  obtain ⟨m₀, hm₀lb, hm₀ub, hm₀ann⟩ :=
    Leaves.exists_annulus_measure_le (ω := z) (μ := μ') hcosR1
      (ε := ENNReal.ofReal (e ^ 2 / 16)) (ENNReal.ofReal_pos.mpr (by positivity))
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
  have hμann : (μ' {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal
      ≤ e ^ 2 / 16 := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc μ' {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}
        ≤ μ' {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m₀} := measure_mono hannsub
      _ ≤ ENNReal.ofReal (e ^ 2 / 16) := hm₀ann
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
    have hbound := Leaves.inner_pole_lower_bound hz hxnorm hω
    have hpiece1 : m * cval ≤ (⟪z, x⟫ : ℝ) * cval := mul_le_mul_of_nonneg_right hxm hcvalpos.le
    have hpiece2 : Real.sqrt (1 - (⟪z, x⟫ : ℝ) ^ 2) ≤ Real.sqrt (1 - m ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hxm, hm0])
    have hpiece3 := mul_le_mul_of_nonneg_right hpiece2 (Real.sqrt_nonneg (1 - cval ^ 2))
    calc mp = m * cval - Real.sqrt (1 - m ^ 2) * Real.sqrt (1 - cval ^ 2) := hmpdef
      _ ≤ (⟪z, x⟫ : ℝ) * cval
          - Real.sqrt (1 - (⟪z, x⟫ : ℝ) ^ 2) * Real.sqrt (1 - cval ^ 2) := by linarith
      _ ≤ (⟪x, ω⟫ : ℝ) := by rw [hcval]; exact hbound
  clear_value mp
  -- reach budget, with `n ≥ 1` forced so the block can be rescaled to duration EXACTLY `T2`
  set slope : ℝ := 2 * (m - cosR) * T2 with hslope
  have hslopepos : 0 < slope := by
    rw [hslope]; exact mul_pos (mul_pos two_pos (by linarith)) hT2
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((logOdds b - logOdds mp) / slope)
  rw [div_le_iff₀ hslopepos] at hn₀
  set n : ℕ := n₀ + 1 with hndef
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [hndef]; positivity
  have hnT0 : (0 : ℝ) ≤ (n : ℝ) * T2 := by positivity
  have hreach : logOdds b ≤ logOdds mp + 2 * (m - cosR) * ((n : ℝ) * T2) := by
    have hmono : (n₀ : ℝ) * slope ≤ (n : ℝ) * slope := by
      rw [hndef]; push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hslopepos.le
    have : 2 * (m - cosR) * ((n : ℝ) * T2) = (n : ℝ) * slope := by rw [hslope]; ring
    rw [this]; linarith
  -- a SINGLE `pPark` block of combined duration `n * T2`
  set θ : AttnSchedule d := [pPark z ω cosR ((n : ℝ) * T2) hnT0] with hθdef
  have hbr : attnMeasureFlow θ μ'
      = measureFlow [gatedBlock hz hω hcosRlb hnT0] ((n : ℝ) * T2) μ' :=
    attnMeasureFlow_pPark_eq_measureFlow_gatedBlock hz hω hcosRlb hnT0 hμ's
  have hW2 := W2_measureFlow_offCenter_collapse_le hz hω hcosRlb hcosR0 hnT0
    hmcval hmlb hb hmp hpole hreach hμ's
  rw [← hbr] at hW2
  haveI : IsProbabilityMeasure (attnMeasureFlow θ μ') := by
    rw [hbr]; exact isProbabilityMeasure_measureFlow _ _ μ'
  have hPsphere : (attnMeasureFlow θ μ') (sphere d)ᶜ = 0 := by
    rw [hbr]; exact measureFlow_supportedIn_sphere _ hnT0 hμ's
  -- the one-sided budget beats `ε`: `√(e²/8 + 4·(e²/16)) = √(3e²/8) < √(e²) = e ≤ ε`
  have h2b : 2 * (1 - b) = e ^ 2 / 8 := by rw [hbdef]; ring
  have hclose : ‖barycenter (attnMeasureFlow θ μ')
      - barycenter (μ'.map (capCollapseMap z ω cosR))‖ < ε := by
    have hle := (Leaves.norm_barycenter_sub_le_W2 hPsphere hαμs).trans hW2
    have hlt : Real.sqrt (2 * (1 - b)
        + 4 * (μ' {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal)
        < Real.sqrt (e ^ 2) := by
      refine Real.sqrt_lt_sqrt (by rw [h2b]; positivity) ?_
      rw [h2b]
      linarith [hμann, he2pos]
    rw [Real.sqrt_sq he0.le] at hlt
    calc ‖barycenter (attnMeasureFlow θ μ')
          - barycenter (μ'.map (capCollapseMap z ω cosR))‖
        ≤ Real.sqrt (2 * (1 - b)
            + 4 * (μ' {x : Eucl d | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) := hle
      _ < e := hlt
      _ ≤ ε := heε
  -- rescale the block to duration EXACTLY `T2`
  set pfin : AttnParams d := (pPark z ω cosR ((n : ℝ) * T2) hnT0).rescale hnpos with hpfindef
  have hdur : pfin.duration = T2 := by
    rw [hpfindef, AttnParams.rescale_duration]
    show (n : ℝ) * T2 / (n : ℝ) = T2
    field_simp
  have hflowEq : attnMeasureFlow [pfin] μ' = attnMeasureFlow θ μ' := by
    rw [hpfindef, hθdef]
    exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T2) hnT0)
      hnpos μ' hμ's
  refine ⟨pfin, hdur, ?_, ?_, ?_⟩
  · rw [hflowEq, ← hbary]
    exact hclose
  · -- exact fixing of every off-cap sphere probability measure, through the same rescale bridge
    intro ρ _ hρs hρcap
    rw [supportedIn] at hρs
    have hflowEqρ : attnMeasureFlow [pfin] ρ = attnMeasureFlow θ ρ := by
      rw [hpfindef, hθdef]
      exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T2) hnT0)
        hnpos ρ hρs
    rw [hflowEqρ, hθdef]
    exact attnMeasureFlow_pPark_eq_of_off_cap z ω cosR ((n : ℝ) * T2) hnT0 ρ hρs hρcap
  · -- region-generic sphere-trace invariance, through the same rescale bridge
    intro S hS hcapS ρ _ hρs hρS
    rw [supportedIn] at hρs hρS
    have hflowEqρ : attnMeasureFlow [pfin] ρ = attnMeasureFlow θ ρ := by
      rw [hpfindef, hθdef]
      exact Leaves.attnMeasureFlow_singleton_rescale_eq (pPark z ω cosR ((n : ℝ) * T2) hnT0)
        hnpos ρ hρs
    rw [supportedIn, hflowEqρ, hθdef]
    exact attnMeasureFlow_pPark_supportedIn_of_cap_subset z ω cosR ((n : ℝ) * T2) hnT0 hS hcapS
      ρ hρs hρS

/-- **The asymmetric-cap collapse schedule: one block defeats every `γ₂`.** Given the axiom's
asymmetric cap (`μ'`-positive, `ν'`-null mass) on the sphere, some single attention block `p` of
duration EXACTLY `T2` fixes `ν'` and makes the flowed barycenters non-colinear for EVERY scalar
`γ₂`. The `ν'`-side is exact: zero cap mass means the block fixes `ν'` outright
(`exists_collapse_block_barycenter_close`'s bystander clause), so its barycenter `β` is untouched.
The `μ'`-side is quantitative: the pole `ω` is chosen by the total arc pigeonhole
(`exists_pole_in_cap_avoiding_total`) so that the ideal collapse target `Sμ'·ω + p'` avoids the
whole line `span{β}` (when `β = 0`, an `Empty` family plus the forbidden vector
`v := -(Sμ')⁻¹ • p'` makes the target nonzero, which is off `span{0}` already); the off-span
margin (`forall_ne_smul_of_dist_lt_infDist_span`) turns that qualitative avoidance into a
positive `infDist` margin `M`, and running the collapse block at `ε := M/2` keeps the flowed
`μ'`-barycenter strictly inside the margin, where no scalar multiple of `β` lives.

This is the Phase-B glue of the non-vacuous `lemma_3_4_part2` re-discharge (claim
`cap-nu-null-b16`), replacing the refuted `hgenRest`/gramGap route entirely: only un-gated
components are consumed.

Two bystander conjuncts ride along for the static-cap induction over `N`
(`exists_disentangling_balls` re-base): the block fixes EVERY sphere-supported probability
measure with zero cap mass (the `ν'`-fixing clause is its instance at `ρ := ν'`), and it keeps
every sphere-supported probability measure carried by a measurable region `S` containing the
cap's sphere-trace carried by `S`. Both are inherited verbatim from
`exists_collapse_block_barycenter_close`'s own bystander clauses. -/
theorem exists_asymmetric_collapse_schedule (hd2 : 2 ≤ d)
    (μ' ν' : Measure (Eucl d)) [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hμ's : supportedIn μ' (sphere d)) (hν's : supportedIn ν' (sphere d))
    {z : Eucl d} (hzs : z ∈ sphere d)
    {cosR : ℝ} (hcosR : cosR ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hμcap : 0 < μ' {x | cosR < (⟪z, x⟫ : ℝ)})
    (hνcap : ν' {x | cosR < (⟪z, x⟫ : ℝ)} = 0)
    {T2 : ℝ} (hT2 : 0 < T2) :
    ∃ p : AttnParams d, p.duration = T2 ∧ attnMeasureFlow [p] ν' = ν' ∧
      (∀ γ₂ : ℝ, barycenter (attnMeasureFlow [p] μ')
        ≠ γ₂ • barycenter (attnMeasureFlow [p] ν')) ∧
      (∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        ρ {x | cosR < (⟪z, x⟫ : ℝ)} = 0 → attnMeasureFlow [p] ρ = ρ) ∧
      ∀ S : Set (Eucl d), MeasurableSet S →
        (∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∈ S) →
        ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
          supportedIn ρ S → supportedIn (attnMeasureFlow [p] ρ) S := by
  have hz : ‖z‖ = 1 := norm_eq_one_of_mem_sphere hzs
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  obtain ⟨hcosRhalf, hcosR1⟩ := hcosR
  have hcosR0 : (0 : ℝ) ≤ cosR := by linarith
  have hSpos : 0 < (μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal :=
    ENNReal.toReal_pos hμcap.ne' (measure_ne_top μ' _)
  have hSne : (μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal ≠ 0 := ne_of_gt hSpos
  obtain ⟨w, hzw, hw⟩ := Leaves.exists_unit_orthogonal hd2 hz0
  -- pole choice: in both branches, the ideal collapse target avoids the `β`-line entirely
  have hpole : ∃ ω : Eucl d, ‖ω‖ = 1 ∧ cosR < (⟪z, ω⟫ : ℝ) ∧
      ∀ c : ℝ, (μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
        + (∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ') ≠ c • barycenter ν' := by
    by_cases hβ0 : barycenter ν' = 0
    · -- `β = 0`: an `Empty` family; the pole only needs to dodge the single vector `-Sμ'⁻¹ • p'`
      obtain ⟨ω, hωnorm, hωcap, hωne, -, -⟩ :=
        exists_pole_in_cap_avoiding_total z w hz hw hzw cosR ⟨hcosR0, hcosR1⟩
          (-(((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal)⁻¹
            • (∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ')))
          ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal) hSne
          (∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ')
          (ι := Empty) Empty.elim (fun i => i.elim)
      refine ⟨ω, hωnorm, hωcap, ?_⟩
      intro c hc
      rw [hβ0, smul_zero] at hc
      apply hωne
      have h1 : (μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
          = -(∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ') := eq_neg_of_add_eq_zero_left hc
      have h2 : ω = ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal)⁻¹
          • ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω) := by
        rw [smul_smul, inv_mul_cancel₀ hSne, one_smul]
      rw [h1, smul_neg] at h2
      exact h2
    · -- `β ≠ 0`: the singleton family `{β}` feeds the arc pigeonhole directly
      obtain ⟨ω, hωnorm, hωcap, -, -, havoid⟩ :=
        exists_pole_in_cap_avoiding_total z w hz hw hzw cosR ⟨hcosR0, hcosR1⟩ 0
          ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal) hSne
          (∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ')
          (ι := Unit) (fun _ => barycenter ν') (fun _ => hβ0)
      exact ⟨ω, hωnorm, hωcap, fun c => havoid () c⟩
  obtain ⟨ω, hωnorm, hωcap, htarget⟩ := hpole
  -- positive margin off the `β`-line, with perturbation stability
  obtain ⟨hMpos, hstab⟩ := forall_ne_smul_of_dist_lt_infDist_span (E := Eucl d) htarget
  -- ε-approximate collapse block, `ε :=` half the margin
  obtain ⟨p, hpdur, hpclose, hpfix, hpS⟩ :=
    exists_collapse_block_barycenter_close μ' hμ's hz hωnorm ⟨hcosRhalf, hcosR1⟩ hωcap hT2
      (ε := Metric.infDist
        ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
          + (∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ'))
        (Submodule.span ℝ {barycenter ν'} : Set (Eucl d)) / 2)
      (by linarith)
  have hνfix : attnMeasureFlow [p] ν' = ν' := hpfix ν' hν's hνcap
  refine ⟨p, hpdur, hνfix, ?_, hpfix, hpS⟩
  intro γ₂
  rw [hνfix]
  refine hstab _ ?_ γ₂
  rw [dist_eq_norm]
  calc ‖barycenter (attnMeasureFlow [p] μ')
      - ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
        + (∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ'))‖
      < Metric.infDist
        ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
          + (∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ'))
        (Submodule.span ℝ {barycenter ν'} : Set (Eucl d)) / 2 := hpclose
    _ ≤ Metric.infDist
        ((μ' {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
          + (∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ'))
        (Submodule.span ℝ {barycenter ν'} : Set (Eucl d)) := by linarith

end MeasureToMeasure.Leaves
