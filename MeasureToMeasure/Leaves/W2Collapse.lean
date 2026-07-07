import MeasureToMeasure.Leaves.GatedCollapse
import MeasureToMeasure.Leaves.GatedPark
import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.Dynamics

/-!
# Leaf L3-collapse-3 (Lemma 3.4 Part 1): the `W₂` collapse bound (capstone)

The App. B.3 Part 1 collapse concentrates a probability measure `μ` onto the pole `ω = x*` with one
self-centered gated block, up to a small `W₂` error. This leaf assembles that error bound from the
two halves already banked plus the map-coupling theorem `Axioms.W2_map_le_L2`.

Write `Φ = flowMap [gatedBlock …] T` for the single-block flow and
`g = collapseMap ω cosR = {cosR < ⟪ω,·⟫}.piecewise (fun _ => ω) id` for the **exact** collapse (send
the open gate cap to `ω`, fix the rest). Then `measureFlow θ T μ = μ.map Φ` and the target
`α_μ = μ.map g`, so `Axioms.W2_map_le_L2` gives
`W₂(measureFlow θ T μ, α_μ) ≤ √(∫ ‖Φ x − g x‖² dμ)`.

The displacement integrand is controlled pointwise (μ-a.e., i.e. on the sphere):
* **off the cap** (`⟪ω,x⟫ ≤ cos R`): `Φ x = x = g x` (L2 `flowMap_gatedBlock_id_of_inner_le`), so `0`;
* **on the sub-cap** (`m ≤ ⟪ω,x⟫`): `g x = ω` and `‖Φ x − ω‖² ≤ 2(1−b)` (L3-collapse-1);
* **on the rim annulus** (`cos R < ⟪ω,x⟫ < m`): `g x = ω` and `‖Φ x − ω‖² ≤ 4` (the sphere diameter).

So `‖Φ x − g x‖² ≤ 2(1−b) + 4·𝟙_{annulus}(x)` a.e., whence
`∫ ‖Φ − g‖² dμ ≤ 2(1−b) + 4·μ(annulus)` and
`W₂(measureFlow θ T μ, α_μ) ≤ √(2(1−b) + 4·μ(annulus))`. The two error terms vanish under the rim
budget (`T → ∞`, L3-collapse-1) and `m ↓ cos R` (L3-collapse-2, `exists_annulus_measure_le`).
-/

namespace MeasureToMeasure

open MeasureTheory
open scoped RealInnerProductSpace ENNReal
open Axioms (measureFlow measureFlow_map)

variable {d : ℕ}

/-- The **exact collapse map**: send the open gate cap `{cos R < ⟪ω,·⟫}` to the pole `ω`, fix
everything else. Its pushforward `μ.map (collapseMap ω cos R)` is the target `α_μ` of the App. B.3
Part 1 collapse; its barycenter is `μ(cap)·ω + ∫_{capᶜ} x dμ`. -/
noncomputable def collapseMap (ω : Eucl d) (cosR : ℝ) : Eucl d → Eucl d :=
  {x | cosR < (⟪ω, x⟫ : ℝ)}.piecewise (fun _ => ω) id

/-- **L3-collapse-3 (capstone).** A single self-centered gated block concentrates the probability
measure `μ` onto the pole `ω` up to a `W₂` error `√(2(1−b) + 4·μ(annulus))`, where the annulus is the
rim `{cos R < ⟪ω,·⟫ < m}`. Combines the on-cap displacement bound (L3-collapse-1) and the off-cap
fixing (L2) through the map-coupling bound `Axioms.W2_map_le_L2`. Feeding `T → ∞` (rim budget) and
`m ↓ cos R` (L3-collapse-2) drives both error terms to `0`. -/
theorem W2_measureFlow_collapse_le {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ} (hcosR : -1 ≤ cosR)
    {T : ℝ} (hT : 0 ≤ T) {m b : ℝ} (hmR : cosR < m) (hm1 : m < 1) (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hreach : logOdds b ≤ logOdds m + 2 * (m - cosR) * T)
    {μ : Measure (Eucl d)} [IsProbabilityMeasure μ] (hμs : μ (sphere d)ᶜ = 0) :
    Axioms.W2 (measureFlow [gatedBlock hω hω hcosR hT] T μ) (μ.map (collapseMap ω cosR))
      ≤ Real.sqrt (2 * (1 - b) + 4 * (μ {x | cosR < (⟪ω, x⟫ : ℝ) ∧ (⟪ω, x⟫ : ℝ) < m}).toReal) := by
  set Φ : Eucl d → Eucl d := flowMap [gatedBlock hω hω hcosR hT] T with hΦ
  set A : Set (Eucl d) := {x | cosR < (⟪ω, x⟫ : ℝ) ∧ (⟪ω, x⟫ : ℝ) < m} with hA
  have hb1 : (0 : ℝ) ≤ 1 - b := by have := hb.2; linarith
  -- measurability of the cap, the annulus, the flow, and the collapse map
  have hcont : Continuous (fun x : Eucl d => (⟪ω, x⟫ : ℝ)) := continuous_const.inner continuous_id
  have hcapM : MeasurableSet {x : Eucl d | cosR < (⟪ω, x⟫ : ℝ)} :=
    hcont.measurable measurableSet_Ioi
  have hAM : MeasurableSet A := by
    have hpre : A = (fun x : Eucl d => (⟪ω, x⟫ : ℝ)) ⁻¹' Set.Ioo cosR m := by
      ext x; simp only [hA, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
    rw [hpre]; exact hcont.measurable measurableSet_Ioo
  have hΦmeas : Measurable Φ := measurable_flowMap _ hT
  have hgmeas : Measurable (collapseMap ω cosR) :=
    Measurable.piecewise hcapM measurable_const measurable_id
  -- the integrable majorant `bnd = 2(1−b) + 4·𝟙_A`
  set bnd : Eucl d → ℝ := fun x => 2 * (1 - b) + 4 * A.indicator (fun _ => (1 : ℝ)) x with hbnd
  have hbndInt : Integrable bnd μ := by
    simp only [hbnd]
    exact (integrable_const (2 * (1 - b))).add
      (((integrable_const (1 : ℝ)).indicator hAM).const_mul 4)
  -- μ-a.e. every point is on the sphere
  have hae : ∀ᵐ x ∂μ, x ∈ sphere d := by
    have hz : μ {x | x ∉ sphere d} = 0 := hμs
    exact ae_iff.mpr hz
  -- the pointwise displacement bound, a.e.
  have hpt : ∀ᵐ x ∂μ, ‖Φ x - collapseMap ω cosR x‖ ^ 2 ≤ bnd x := by
    filter_upwards [hae] with x hx
    have hb0 : (0 : ℝ) ≤ 4 * A.indicator (fun _ => (1 : ℝ)) x :=
      mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    by_cases hxcap : cosR < (⟪ω, x⟫ : ℝ)
    · -- on the cap: `g x = ω`
      have hgx : collapseMap ω cosR x = ω := Set.piecewise_eq_of_mem _ _ _ hxcap
      by_cases hxm : m ≤ (⟪ω, x⟫ : ℝ)
      · -- sub-cap: L3-collapse-1
        have hxm' : m ≤ (⟪x, ω⟫ : ℝ) := by rwa [real_inner_comm]
        have hle : ‖Φ x - ω‖ ^ 2 ≤ 2 * (1 - b) :=
          normSq_flowMap_gatedBlock_sub_pole_le hω hcosR hT hmR hm1 hb hreach hx hxm'
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
      have hgx : collapseMap ω cosR x = x :=
        Set.piecewise_eq_of_notMem _ _ _ (not_lt.mpr hxcap)
      have hΦx : Φ x = x := flowMap_gatedBlock_id_of_inner_le hω hω hcosR hT T hxcap
      rw [hΦx, hgx, sub_self, norm_zero]; simp only [hbnd]; nlinarith [hb1, hb0]
  -- integrability of the displacement square (dominated by `bnd`)
  have hdispInt : Integrable (fun x => ‖Φ x - collapseMap ω cosR x‖ ^ 2) μ := by
    apply hbndInt.mono' ((hΦmeas.sub hgmeas).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hpt] with x hx
    rw [Real.norm_of_nonneg (by positivity)]; exact hx
  -- the map-coupling bound, then integrate the majorant
  have hstep : Axioms.W2 (measureFlow [gatedBlock hω hω hcosR hT] T μ) (μ.map (collapseMap ω cosR))
      ≤ Real.sqrt (∫ x, ‖Φ x - collapseMap ω cosR x‖ ^ 2 ∂μ) := by
    rw [measureFlow_map]
    exact Axioms.W2_map_le_L2 μ Φ (collapseMap ω cosR) hΦmeas hgmeas hdispInt
  refine hstep.trans (Real.sqrt_le_sqrt ?_)
  have hbndval : ∫ x, bnd x ∂μ = 2 * (1 - b) + 4 * (μ A).toReal := by
    simp only [hbnd]
    rw [integral_add (integrable_const _)
        (((integrable_const (1 : ℝ)).indicator hAM).const_mul 4),
      integral_const, integral_const_mul, integral_indicator_const _ hAM]
    simp [measureReal_def, measure_univ]
  calc ∫ x, ‖Φ x - collapseMap ω cosR x‖ ^ 2 ∂μ
      ≤ ∫ x, bnd x ∂μ := integral_mono_ae hdispInt hbndInt hpt
    _ = 2 * (1 - b) + 4 * (μ A).toReal := hbndval

end MeasureToMeasure
