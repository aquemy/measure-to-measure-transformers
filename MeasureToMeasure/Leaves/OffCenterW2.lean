import MeasureToMeasure.Leaves.OffCenterDisplacement
import MeasureToMeasure.Leaves.OffCenterCollapse
import MeasureToMeasure.Leaves.GatedPark
import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.Dynamics

/-!
# Leaf (Lemma 3.4 Part 1, Path I): the non-self-centered `W₂` collapse bound

The Path I analog of L3-collapse-3 (`W2_measureFlow_collapse_le`). A single **non-self-centered** gated
block `gatedBlock hz hω` gates on a fixed cap `{cos R < ⟪z,·⟫}` (direction `z`) and collapses that
cap's mass onto a separate pole `ω`, up to a small `W₂` error. The exact target is the pushforward
`μ.map (capCollapseMap z ω cos R)`.

Writing `Φ = flowMap [gatedBlock hz hω …] T` and `g = capCollapseMap z ω cos R`, the map-coupling
theorem `Axioms.W2_map_le_L2` (with `measureFlow θ T μ = μ.map Φ`) gives
`W₂(measureFlow θ T μ, μ.map g) ≤ √(∫ ‖Φ x − g x‖² dμ)`, and the displacement is controlled a.e.:

* **off the cap** (`⟪z,x⟫ ≤ cos R`): `Φ x = x = g x` (L2 `flowMap_gatedBlock_id_of_inner_le`, general
  in `z`), so `0`;
* **on the sub-cap** (`m ≤ ⟪z,x⟫`): `g x = ω`, and `‖Φ x − ω‖² ≤ 2(1 − b)` — either `x = ω` (the pole
  is a fixed point of the block, so displacement `0`) or `x ≠ ω` (off-center displacement bound
  `normSq_flowMap_gatedBlock_offCenter_sub_pole_le`, fed the uniform rim budget through the pole-cap
  lower bound `mp ≤ ⟪x,ω⟫`);
* **on the rim annulus** (`cos R < ⟪z,x⟫ < m`): `g x = ω` and `‖Φ x − ω‖² ≤ 4` (sphere diameter).

So `‖Φ x − g x‖² ≤ 2(1 − b) + 4·𝟙_{annulus}(x)` a.e., whence
`W₂(measureFlow θ T μ, μ.map g) ≤ √(2(1 − b) + 4·μ(annulus))`. Both error terms vanish in the assembly
(`T → ∞` and `m ↓ cos R`).

The one structural difference from the self-centered case: because the gate direction `z` no longer
controls the pole coordinate `⟪·,ω⟫`, the uniform rim budget needs an explicit pole-cap lower bound
`hpole : ∀ x ∈ 𝕊, m ≤ ⟪z,x⟫ → mp ≤ ⟪x,ω⟫` (in the assembly `mp` is close to `1`, since a tight cap
around `z` with `ω` nearby keeps every cap point close to the pole).
-/

namespace MeasureToMeasure

open MeasureTheory
open scoped RealInnerProductSpace ENNReal
open Axioms (measureFlow measureFlow_map)

variable {d : ℕ}

/-- **Non-self-centered `W₂` collapse.** A single gated block `gatedBlock hz hω` concentrates the
probability measure `μ` onto the pole `ω` (collapsing its gate cap `{cos R < ⟪z,·⟫}`) up to a `W₂`
error `√(2(1 − b) + 4·μ(annulus))`, where the annulus is the rim `{cos R < ⟪z,·⟫ < m}`. Non-self-centered
analog of `W2_measureFlow_collapse_le`: the on-sub-cap displacement comes from
`normSq_flowMap_gatedBlock_offCenter_sub_pole_le`, fed the uniform rim budget through the pole-cap lower
bound `hpole`; the pole `x = ω` is a fixed point (displacement `0`); off-cap is fixed by L2. -/
theorem W2_measureFlow_offCenter_collapse_le {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1)
    {cosR : ℝ} (hcosR : -1 ≤ cosR) (hcosR0 : 0 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {m b mp : ℝ}
    (hzω : m < (⟪z, ω⟫ : ℝ)) (hmR : cosR < m) (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hmp : mp ∈ Set.Ioo (-1 : ℝ) 1)
    (hpole : ∀ x ∈ sphere d, m ≤ (⟪z, x⟫ : ℝ) → mp ≤ (⟪x, ω⟫ : ℝ))
    (hreach : logOdds b ≤ logOdds mp + 2 * (m - cosR) * T)
    {μ : Measure (Eucl d)} [IsProbabilityMeasure μ] (hμs : μ (sphere d)ᶜ = 0) :
    Axioms.W2 (measureFlow [gatedBlock hz hω hcosR hT] T μ) (μ.map (capCollapseMap z ω cosR))
      ≤ Real.sqrt (2 * (1 - b) + 4 * (μ {x | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m}).toReal) := by
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  set Φ : Eucl d → Eucl d := flowMap [gatedBlock hz hω hcosR hT] T with hΦ
  set A : Set (Eucl d) := {x | cosR < (⟪z, x⟫ : ℝ) ∧ (⟪z, x⟫ : ℝ) < m} with hA
  have hb1 : (0 : ℝ) ≤ 1 - b := by have := hb.2; linarith
  -- measurability of the cap, the annulus, the flow, and the collapse map
  have hcont : Continuous (fun x : Eucl d => (⟪z, x⟫ : ℝ)) := continuous_const.inner continuous_id
  have hcapM : MeasurableSet {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} :=
    hcont.measurable measurableSet_Ioi
  have hAM : MeasurableSet A := by
    have hpre : A = (fun x : Eucl d => (⟪z, x⟫ : ℝ)) ⁻¹' Set.Ioo cosR m := by
      ext x; simp only [hA, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
    rw [hpre]; exact hcont.measurable measurableSet_Ioo
  have hΦmeas : Measurable Φ := measurable_flowMap _ hT
  have hgmeas : Measurable (capCollapseMap z ω cosR) :=
    Measurable.piecewise hcapM measurable_const measurable_id
  -- the integrable majorant `bnd = 2(1−b) + 4·𝟙_A`
  set bnd : Eucl d → ℝ := fun x => 2 * (1 - b) + 4 * A.indicator (fun _ => (1 : ℝ)) x with hbnd
  have hbndInt : Integrable bnd μ := by
    simp only [hbnd]
    exact (integrable_const (2 * (1 - b))).add
      (((integrable_const (1 : ℝ)).indicator hAM).const_mul 4)
  -- μ-a.e. every point is on the sphere
  have hae : ∀ᵐ x ∂μ, x ∈ sphere d := ae_iff.mpr hμs
  -- the pointwise displacement bound, a.e.
  have hpt : ∀ᵐ x ∂μ, ‖Φ x - capCollapseMap z ω cosR x‖ ^ 2 ≤ bnd x := by
    filter_upwards [hae] with x hx
    have hb0 : (0 : ℝ) ≤ 4 * A.indicator (fun _ => (1 : ℝ)) x :=
      mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    by_cases hxcap : cosR < (⟪z, x⟫ : ℝ)
    · -- on the cap: `g x = ω`
      have hgx : capCollapseMap z ω cosR x = ω := Set.piecewise_eq_of_mem _ _ _ hxcap
      by_cases hxm : m ≤ (⟪z, x⟫ : ℝ)
      · -- sub-cap
        by_cases hxω : x = ω
        · -- pole: fixed point of the block, displacement 0
          have hfix : Φ x = ω := by
            have h1 : flowMap [gatedBlock hz hω hcosR hT] T ω
                = (gatedBlock hz hω hcosR hT).blockFlow T ω := by
              rw [flowMap_cons, flowMap_nil]; rfl
            rw [hΦ, hxω, h1]
            exact (gatedBlock hz hω hcosR hT).blockFlow_fixed
              (gatedField_pole_eq_zero hωs cosR) T
          rw [hgx, hfix, sub_self, norm_zero]; simp only [hbnd]; nlinarith [hb1, hb0]
        · -- off the pole: off-center displacement bound
          have hxnp : x ≠ -ω := by
            intro h; rw [h, inner_neg_right] at hxm; nlinarith [hzω, hmR, hcosR0]
          have hmp_le : mp ≤ (⟪x, ω⟫ : ℝ) := hpole x hx hxm
          have hbudget : logOdds b ≤ logOdds (⟪x, ω⟫ : ℝ) + 2 * (m - cosR) * T := by
            have hmono := logOdds_le_logOdds hmp (inner_mem_Ioo_of_ne hx hωs hxω hxnp) hmp_le
            linarith
          have hle : ‖Φ x - ω‖ ^ 2 ≤ 2 * (1 - b) :=
            normSq_flowMap_gatedBlock_offCenter_sub_pole_le hz hω hcosR hcosR0 hT hzω hb
              hx hxω hxnp hxm hbudget
          rw [hgx]; simp only [hbnd]; linarith [hle, hb0]
      · -- rim annulus: crude diameter bound `≤ 4`
        rw [not_le] at hxm
        have hxA : x ∈ A := ⟨hxcap, hxm⟩
        have hΦs : Φ x ∈ sphere d := flowMap_mem_sphere _ hT hx
        have hle2 : ‖Φ x - ω‖ ≤ 2 := by
          calc ‖Φ x - ω‖ ≤ ‖Φ x‖ + ‖ω‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_eq_one_of_mem_sphere hΦs, hω]; norm_num
        have hdiam : ‖Φ x - ω‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (Φ x - ω)]
        have hindA : A.indicator (fun _ => (1 : ℝ)) x = 1 := Set.indicator_of_mem hxA _
        rw [hgx]; simp only [hbnd, hindA]; linarith [hdiam, hb1]
    · -- off the cap: `Φ x = x = g x`
      rw [not_lt] at hxcap
      have hgx : capCollapseMap z ω cosR x = x :=
        Set.piecewise_eq_of_notMem _ _ _ (not_lt.mpr hxcap)
      have hΦx : Φ x = x := flowMap_gatedBlock_id_of_inner_le hz hω hcosR hT T hxcap
      rw [hΦx, hgx, sub_self, norm_zero]; simp only [hbnd]; nlinarith [hb1, hb0]
  -- integrability of the displacement square (dominated by `bnd`)
  have hdispInt : Integrable (fun x => ‖Φ x - capCollapseMap z ω cosR x‖ ^ 2) μ := by
    apply hbndInt.mono' ((hΦmeas.sub hgmeas).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hpt] with x hx
    rw [Real.norm_of_nonneg (by positivity)]; exact hx
  -- the map-coupling bound, then integrate the majorant
  have hstep : Axioms.W2 (measureFlow [gatedBlock hz hω hcosR hT] T μ) (μ.map (capCollapseMap z ω cosR))
      ≤ Real.sqrt (∫ x, ‖Φ x - capCollapseMap z ω cosR x‖ ^ 2 ∂μ) := by
    rw [measureFlow_map]
    exact Axioms.W2_map_le_L2 μ Φ (capCollapseMap z ω cosR) hΦmeas hgmeas hdispInt
  refine hstep.trans (Real.sqrt_le_sqrt ?_)
  have hbndval : ∫ x, bnd x ∂μ = 2 * (1 - b) + 4 * (μ A).toReal := by
    simp only [hbnd]
    rw [integral_add (integrable_const _)
        (((integrable_const (1 : ℝ)).indicator hAM).const_mul 4),
      integral_const, integral_const_mul, integral_indicator_const _ hAM]
    simp [measureReal_def, measure_univ]
  calc ∫ x, ‖Φ x - capCollapseMap z ω cosR x‖ ^ 2 ∂μ
      ≤ ∫ x, bnd x ∂μ := integral_mono_ae hdispInt hbndInt hpt
    _ = 2 * (1 - b) + 4 * (μ A).toReal := hbndval

end MeasureToMeasure
