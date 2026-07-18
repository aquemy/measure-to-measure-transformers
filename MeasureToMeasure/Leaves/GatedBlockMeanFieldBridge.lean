import MeasureToMeasure.Leaves.MeanFieldPark
import MeasureToMeasure.Foundations.GatedBlock
import MeasureToMeasure.Foundations.FlowMap
import MeasureToMeasure.Axioms.ContinuityEquation

/-!
# The linear-layer gated block IS the mean-field `pPark` block, on the sphere

`lemma_3_4_part1`'s machine-checked mass-gap-cap-collapse construction lives on the LINEAR layer
(`Params d`/`measureFlow`, via `gatedBlock`), but several open axioms (`lemma_3_4_part2`,
`exists_disentangling_balls`'s Phase 2) need the SAME construction on the MEAN-FIELD layer
(`AttnSchedule d`/`attnMeasureFlow`). This file supplies the bridge: `pPark` (already built for
`exists_parked_schedule`, `Leaves/MeanFieldPark.lean`) and `gatedBlock` (built for `lemma_3_4_part1`,
`Foundations/GatedBlock.lean`) turn out to have EXACTLY the same field on the sphere --
`pPark`'s field is `max 0 (⟪z,x⟫-cosR) • tangentialProjector x ω` with no cutoff (legal since
`AttnParams.field` is already globally Lipschitz-on-the-sphere for any parameter choice); `gatedField`
is the same formula composed with a `normCutoff` that equals `1` throughout the unit ball (needed on
the LINEAR layer only for the AMBIENT `ℝ^d`-wide Picard-Lindelöf `Block` structure, irrelevant to
`IsMeanFieldFlow`, which is characterized purely on-sphere).

Rather than re-deriving ODE uniqueness from scratch, both bridges reuse the GENERAL machinery already
built for the M3b well-posedness campaign (`Foundations/Attention.lean`'s `isMeanFieldFlow_blockFlow`,
`Foundations/AttnStepExistence.lean`'s `attnStep_eq_map_blockFlow`): for ANY `V = 0` `AttnParams` `p`
and ANY `Block b` whose field agrees with `p`'s perceptron-gate formula on the sphere, `b.blockFlow`
IS a valid mean-field flow of `p`, and uniqueness (`meanFieldFlow_unique`) does the rest. `pPark`/
`gatedBlock` (and their amplitude-scaled analogues `pParkScaled`/`scaledGatedBlock`) are exactly one
instance of this generic fact, once the field-agreement is checked.

The `n`-replicated-schedule extension turned out unnecessary: `lemma_3_4_part1`'s own proof already
collapses `List.replicate n block` into a single block evaluated at the combined duration `n·T` (an
autonomous field composes by adding time), so the single-block bridge applies directly -- see
`Leaves/Lemma34Part1MeanField.lean` for the full mean-field analogue of `lemma_3_4_part1` built this
way.

This file also supplies the AMPLITUDE-SCALED analogue (`pParkScaled`/`scaledGatedBlock`), needed for
`lemma_3_2`'s own construction (`Foundations/OrthantRotation.lean`'s
`exists_twoPhase_mapsTo_orthant`), which uses `scaledGatedBlock` rather than the plain `gatedBlock` --
the SAME sphere-field-equality argument applies verbatim, since scaling the field by an amplitude `A`
commutes with everything the bridge argument uses.

Staged for the `lemma_3_4_part2`/`exists_disentangling_balls` campaigns; see the
`mean-field-axioms-retractability` project notes for the full plan.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure.Foundations MeasureToMeasure.Axioms

variable {d : ℕ} [NeZero d]

/-- On the sphere, `pPark`'s field agrees exactly with `gatedField` -- both reduce to the same
ReLU-gated tangential projection, since `normCutoff = 1` throughout the closed unit ball. -/
theorem pPark_field_eq_gatedField_of_mem_sphere {z ω : Eucl d} (hz : ‖z‖ = 1) {cosR T : ℝ}
    (hT : 0 ≤ T) {x : Eucl d} (hx : x ∈ sphere d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν] :
    (pPark z ω cosR T hT).field ν x = gatedField z ω cosR x := by
  rw [pPark_field, gatedField, gateFactor,
    normCutoff_eq_one (le_of_eq (norm_eq_one_of_mem_sphere hx)), one_mul, reluGate]

/-- `gatedBlock`'s field matches `pPark`'s raw perceptron-gate formula on the sphere -- the
hypothesis `attnStep_eq_map_blockFlow`/`isMeanFieldFlow_blockFlow` need. -/
theorem gatedBlock_field_agree {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR T : ℝ}
    (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T) (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0] :
    ∀ y ∈ sphere d, (gatedBlock hz hω hcosR hT).field y
      = tangentialProjector y ((pPark z ω cosR T hT).W
          (reluVec ((pPark z ω cosR T hT).U y + (pPark z ω cosR T hT).b))) := by
  intro y hy
  show gatedField z ω cosR y = _
  rw [← pPark_field_eq_gatedField_of_mem_sphere hz hT hy μ0]
  unfold AttnParams.field
  rw [show (pPark z ω cosR T hT).V = (0 : Eucl d →L[ℝ] Eucl d) from rfl]
  simp

/-- **The point-level bridge.** Any mean-field flow of `pPark z ω cosR T hT` agrees, on the sphere,
with the linear layer's `gatedBlock` point flow for the SAME `z, ω, cosR, T`: both solve the
identical autonomous sphere-restricted ODE, so uniqueness (`meanFieldFlow_unique`, applied to
`gatedBlock`'s point flow via `isMeanFieldFlow_blockFlow`) identifies the two trajectories. -/
theorem attnFlow_eq_blockFlow_gatedBlock {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR T : ℝ}
    (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pPark z ω cosR T hT) μ0 Φ)
    {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Φ t x = (gatedBlock hz hω hcosR hT).blockFlow t x := by
  have hΨ : IsMeanFieldFlow (pPark z ω cosR T hT) μ0
      (fun s => (gatedBlock hz hω hcosR hT).blockFlow s) :=
    isMeanFieldFlow_blockFlow (gatedBlock hz hω hcosR hT) (pPark z ω cosR T hT) rfl
      (gatedBlock_field_agree hz hω hcosR hT μ0) μ0
  exact meanFieldFlow_unique hμ0S hΦ hΨ t ht x hx

/-- **The measure-level bridge.** The mean-field flow of `[pPark z ω cosR T hT]` and the linear flow
of `[gatedBlock hz hω hcosR hT]` push forward a sphere-supported probability measure to the SAME
measure -- the mean-field layer's `V = 0` block is not merely analogous to the linear layer's gated
block, it realizes the identical dynamics. -/
theorem attnMeasureFlow_pPark_eq_measureFlow_gatedBlock {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1)
    {cosR T : ℝ} (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0) :
    attnMeasureFlow [pPark z ω cosR T hT] μ0 = measureFlow [gatedBlock hz hω hcosR hT] T μ0 := by
  show attnStep (pPark z ω cosR T hT) μ0 = _
  rw [attnStep_eq_map_blockFlow (pPark z ω cosR T hT) rfl (gatedBlock hz hω hcosR hT)
    (gatedBlock_field_agree hz hω hcosR hT μ0) μ0 hμ0S]
  show μ0.map ((gatedBlock hz hω hcosR hT).blockFlow (pPark z ω cosR T hT).duration) = _
  rw [show (pPark z ω cosR T hT).duration = T from rfl, measureFlow, flowMap_cons, flowMap_nil]
  rfl

end MeasureToMeasure.Leaves

namespace MeasureToMeasure.Foundations

variable {d : ℕ} [NeZero d]

/-- The mean-field amplitude-scaled parking block: `pPark`'s `W` scaled by `A`. -/
noncomputable def pParkScaled (A : ℝ) (z ω : Eucl d) (cosR T : ℝ) (hT : 0 ≤ T) : AttnParams d where
  V := 0
  B := 0
  W := A • (ContinuousLinearMap.smulRight (EuclideanSpace.proj (0 : Fin d)) ω)
  U := (innerSL ℝ z).smulRight (MeasureToMeasure.Leaves.e1 d)
  b := (-cosR) • MeasureToMeasure.Leaves.e1 d
  duration := T
  duration_nonneg := hT

end MeasureToMeasure.Foundations

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure.Foundations MeasureToMeasure.Axioms

variable {d : ℕ} [NeZero d]

/-- The scaled parking block's field is `A` times `pPark`'s field, everywhere. -/
theorem pParkScaled_field (A : ℝ) (z ω : Eucl d) (cosR T : ℝ) (hT : 0 ≤ T) (x : Eucl d)
    (ν : Measure (Eucl d)) [IsProbabilityMeasure ν] :
    (pParkScaled A z ω cosR T hT).field ν x
      = A • (max 0 (⟪z, x⟫ - cosR) • tangentialProjector x ω) := by
  have h0 : (pParkScaled A z ω cosR T hT).V = (0 : Eucl d →L[ℝ] Eucl d) := rfl
  have hUb : (pParkScaled A z ω cosR T hT).U x + (pParkScaled A z ω cosR T hT).b
      = (⟪z, x⟫ - cosR) • e1 d := by
    show ((innerSL ℝ z).smulRight (e1 d) : Eucl d →L[ℝ] Eucl d) x + (-cosR) • e1 d
      = (⟪z, x⟫ - cosR) • e1 d
    rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, sub_smul, neg_smul,
      sub_eq_add_neg]
  unfold AttnParams.field
  rw [h0]
  simp only [zero_apply, zero_add]
  show tangentialProjector x
    ((pParkScaled A z ω cosR T hT).W (reluVec ((pParkScaled A z ω cosR T hT).U x
      + (pParkScaled A z ω cosR T hT).b))) = _
  rw [hUb]
  have hrelu : reluVec ((⟪z, x⟫ - cosR) • e1 d) = max 0 (⟪z, x⟫ - cosR) • e1 d := by
    ext i
    by_cases hi : i = 0
    · subst hi; simp [reluVec, e1_apply_zero]
    · simp [reluVec, e1_apply_ne hi]
  rw [hrelu]
  show tangentialProjector x
    ((A • (ContinuousLinearMap.smulRight (EuclideanSpace.proj (0 : Fin d)) ω) :
      Eucl d →L[ℝ] Eucl d) (max 0 (⟪z, x⟫ - cosR) • e1 d)) = _
  rw [smul_apply, ContinuousLinearMap.smulRight_apply]
  have hcoord : (EuclideanSpace.proj (0 : Fin d) : Eucl d →L[ℝ] ℝ)
      (max 0 (⟪z, x⟫ - cosR) • e1 d) = max 0 (⟪z, x⟫ - cosR) := by
    show (max 0 (⟪z, x⟫ - cosR) • e1 d) 0 = max 0 (⟪z, x⟫ - cosR)
    simp [e1_apply_zero]
  rw [hcoord, tangentialProjector_smul_right, tangentialProjector_smul_right]

/-- On the sphere, the scaled fields agree too: `pParkScaled`'s field equals `scaledGatedField`'s. -/
theorem pParkScaled_field_eq_scaledGatedField_of_mem_sphere (A : ℝ) {z ω : Eucl d} (hz : ‖z‖ = 1)
    {cosR T : ℝ} (hT : 0 ≤ T) {x : Eucl d} (hx : x ∈ sphere d) (ν : Measure (Eucl d))
    [IsProbabilityMeasure ν] :
    (pParkScaled A z ω cosR T hT).field ν x = scaledGatedField A z ω cosR x := by
  rw [pParkScaled_field, scaledGatedField, gatedField, gateFactor,
    normCutoff_eq_one (le_of_eq (norm_eq_one_of_mem_sphere hx)), one_mul, reluGate]

/-- `scaledGatedBlock`'s field matches `pParkScaled`'s raw perceptron-gate formula on the sphere. -/
theorem scaledGatedBlock_field_agree {A : ℝ} (hA : 0 ≤ A) {z ω : Eucl d} (hz : ‖z‖ = 1)
    (hω : ‖ω‖ = 1) {cosR T : ℝ} (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0] :
    ∀ y ∈ sphere d, (scaledGatedBlock hA hz hω hcosR hT).field y
      = tangentialProjector y ((pParkScaled A z ω cosR T hT).W
          (reluVec ((pParkScaled A z ω cosR T hT).U y + (pParkScaled A z ω cosR T hT).b))) := by
  intro y hy
  show scaledGatedField A z ω cosR y = _
  rw [← pParkScaled_field_eq_scaledGatedField_of_mem_sphere A hz hT hy μ0]
  unfold AttnParams.field
  rw [show (pParkScaled A z ω cosR T hT).V = (0 : Eucl d →L[ℝ] Eucl d) from rfl]
  simp

/-- **The point-level bridge, scaled form.** Any mean-field flow of `pParkScaled A z ω cosR T hT`
agrees, on the sphere, with the linear layer's `scaledGatedBlock` point flow. -/
theorem attnFlow_eq_blockFlow_scaledGatedBlock {A : ℝ} (hA : 0 ≤ A) {z ω : Eucl d} (hz : ‖z‖ = 1)
    (hω : ‖ω‖ = 1) {cosR T : ℝ} (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pParkScaled A z ω cosR T hT) μ0 Φ)
    {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Φ t x = (scaledGatedBlock hA hz hω hcosR hT).blockFlow t x := by
  have hΨ : IsMeanFieldFlow (pParkScaled A z ω cosR T hT) μ0
      (fun s => (scaledGatedBlock hA hz hω hcosR hT).blockFlow s) :=
    isMeanFieldFlow_blockFlow (scaledGatedBlock hA hz hω hcosR hT) (pParkScaled A z ω cosR T hT) rfl
      (scaledGatedBlock_field_agree hA hz hω hcosR hT μ0) μ0
  exact meanFieldFlow_unique hμ0S hΦ hΨ t ht x hx

/-- **The measure-level bridge, scaled form.** The mean-field flow of `[pParkScaled A z ω cosR T hT]`
and the linear flow of `[scaledGatedBlock hA hz hω hcosR hT]` push forward a sphere-supported
probability measure to the SAME measure. -/
theorem attnMeasureFlow_pParkScaled_eq_measureFlow_scaledGatedBlock {A : ℝ} (hA : 0 ≤ A)
    {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR T : ℝ} (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0) :
    attnMeasureFlow [pParkScaled A z ω cosR T hT] μ0
      = measureFlow [scaledGatedBlock hA hz hω hcosR hT] T μ0 := by
  show attnStep (pParkScaled A z ω cosR T hT) μ0 = _
  rw [attnStep_eq_map_blockFlow (pParkScaled A z ω cosR T hT) rfl
    (scaledGatedBlock hA hz hω hcosR hT) (scaledGatedBlock_field_agree hA hz hω hcosR hT μ0) μ0 hμ0S]
  show μ0.map ((scaledGatedBlock hA hz hω hcosR hT).blockFlow (pParkScaled A z ω cosR T hT).duration)
    = _
  rw [show (pParkScaled A z ω cosR T hT).duration = T from rfl, measureFlow, flowMap_cons,
    flowMap_nil]
  rfl

end MeasureToMeasure.Leaves
