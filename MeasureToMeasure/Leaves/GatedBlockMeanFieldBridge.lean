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
`IsMeanFieldFlow`, which is characterized purely on-sphere). Since both flows solve the identical
autonomous sphere-restricted ODE, ODE uniqueness (the SAME technique `MeanFieldPark.lean`'s own
`attnFlow_id_of_inner_le` uses, comparing against a constant trajectory instead of `gatedBlock`'s)
identifies the two flow MAPS on the sphere, hence the two PUSHFORWARD MEASURES, for a single block.

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

/-- **The point-level bridge.** Any mean-field flow of `pPark z ω cosR T hT` agrees, on the sphere,
with the linear layer's `gatedBlock` point flow for the SAME `z, ω, cosR, T`: both solve the
identical autonomous sphere-restricted ODE, so `ODE_solution_unique_of_mem_Icc_right` (the same tool
`attnFlow_id_of_inner_le` uses) identifies the two trajectories. -/
theorem attnFlow_eq_blockFlow_gatedBlock {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR T : ℝ}
    (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pPark z ω cosR T hT) μ0 Φ)
    {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Φ t x = (gatedBlock hz hω hcosR hT).blockFlow t x := by
  set p := pPark z ω cosR T hT with hpdef
  set b := gatedBlock hz hω hcosR hT with hbdef
  set C : ℝ := (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖)
    + 2 * (‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖)) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hEq : Set.EqOn (fun s => Φ s x) (fun s => b.blockFlow s x) (Set.Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun s y => p.field (μ0.map (Φ s)) y) (s := fun _ => sphere d)
      (K := C.toNNReal) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s hs
      have hsIcc := Set.Ico_subset_Icc_self hs
      haveI := isProbabilityMeasure_map_flow hΦ hsIcc
      have hmapS := map_flow_sphere_support hμ0S hΦ hsIcc
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro a ha bb hbb
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖p.field (μ0.map (Φ s)) a - p.field (μ0.map (Φ s)) bb‖
          ≤ C * ‖a - bb‖ := norm_field_sub_point_le p (μ0.map (Φ s)) hmapS ha hbb
        _ = (C.toNNReal : ℝ) * ‖a - bb‖ := by rw [Real.coe_toNNReal C hC0]
    · exact fun s hs => (hΦ.deriv x hx s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hΦ.deriv x hx s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    · exact fun s hs => (hΦ.sphere_bijOn s (Set.Ico_subset_Icc_self hs)).mapsTo hx
    · exact fun s hs => (b.blockCurve_isIntegralCurve x s).continuousAt.continuousWithinAt
    · intro s hs
      have hsIcc := Set.Ico_subset_Icc_self hs
      haveI := isProbabilityMeasure_map_flow hΦ hsIcc
      have hbsph : b.blockFlow s x ∈ sphere d := b.blockFlow_mem_sphere hx hs.1
      have hfeq : p.field (μ0.map (Φ s)) (b.blockFlow s x) = b.field (b.blockFlow s x) := by
        show (pPark z ω cosR T hT).field (μ0.map (Φ s)) (b.blockFlow s x)
          = gatedField z ω cosR (b.blockFlow s x)
        exact pPark_field_eq_gatedField_of_mem_sphere hz hT hbsph (μ0.map (Φ s))
      rw [hfeq]
      exact (b.blockCurve_isIntegralCurve x s).hasDerivWithinAt
    · exact fun s hs => b.blockFlow_mem_sphere hx (Set.Ico_subset_Icc_self hs).1
    · show Φ 0 x = b.blockFlow 0 x
      rw [hΦ.init, b.blockFlow_zero]; rfl
  exact hEq ht

/-- **The measure-level bridge.** The mean-field flow of `[pPark z ω cosR T hT]` and the linear flow
of `[gatedBlock hz hω hcosR hT]` push forward a sphere-supported probability measure to the SAME
measure -- the mean-field layer's `V = 0` block is not merely analogous to the linear layer's gated
block, it realizes the identical dynamics. -/
theorem attnMeasureFlow_pPark_eq_measureFlow_gatedBlock {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1)
    {cosR T : ℝ} (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0) :
    attnMeasureFlow [pPark z ω cosR T hT] μ0 = measureFlow [gatedBlock hz hω hcosR hT] T μ0 := by
  have hex := @exists_meanFieldFlow d (pPark z ω cosR T hT) μ0 ‹_› hμ0S
  set Φ := hex.choose with hΦdef
  have hΦspec : IsMeanFieldFlow (pPark z ω cosR T hT) μ0 Φ := hex.choose_spec
  have hstep : attnStep (pPark z ω cosR T hT) μ0 = μ0.map (Φ (pPark z ω cosR T hT).duration) := by
    unfold attnStep
    rw [dif_pos ⟨‹_›, hμ0S⟩]
  show attnStep (pPark z ω cosR T hT) μ0 = _
  rw [hstep, measureFlow]
  have hdur : (pPark z ω cosR T hT).duration = T := rfl
  have hflowsingle : flowMap [gatedBlock hz hω hcosR hT] T
      = (gatedBlock hz hω hcosR hT).blockFlow T := by
    rw [flowMap_cons, flowMap_nil]; rfl
  rw [hflowsingle, hdur]
  apply Measure.map_congr
  filter_upwards [hμ0S] with x hx
  exact attnFlow_eq_blockFlow_gatedBlock hz hω hcosR hT hμ0S Φ hΦspec hx ⟨hT, le_refl T⟩

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

/-- **The point-level bridge, scaled form.** Any mean-field flow of `pParkScaled A z ω cosR T hT`
agrees, on the sphere, with the linear layer's `scaledGatedBlock` point flow. -/
theorem attnFlow_eq_blockFlow_scaledGatedBlock {A : ℝ} (hA : 0 ≤ A) {z ω : Eucl d} (hz : ‖z‖ = 1)
    (hω : ‖ω‖ = 1) {cosR T : ℝ} (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pParkScaled A z ω cosR T hT) μ0 Φ)
    {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Φ t x = (scaledGatedBlock hA hz hω hcosR hT).blockFlow t x := by
  set p := pParkScaled A z ω cosR T hT with hpdef
  set b := scaledGatedBlock hA hz hω hcosR hT with hbdef
  set C : ℝ := (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖)
    + 2 * (‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖)) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hEq : Set.EqOn (fun s => Φ s x) (fun s => b.blockFlow s x) (Set.Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun s y => p.field (μ0.map (Φ s)) y) (s := fun _ => sphere d)
      (K := C.toNNReal) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s hs
      have hsIcc := Set.Ico_subset_Icc_self hs
      haveI := isProbabilityMeasure_map_flow hΦ hsIcc
      have hmapS := map_flow_sphere_support hμ0S hΦ hsIcc
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro a ha bb hbb
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖p.field (μ0.map (Φ s)) a - p.field (μ0.map (Φ s)) bb‖
          ≤ C * ‖a - bb‖ := norm_field_sub_point_le p (μ0.map (Φ s)) hmapS ha hbb
        _ = (C.toNNReal : ℝ) * ‖a - bb‖ := by rw [Real.coe_toNNReal C hC0]
    · exact fun s hs => (hΦ.deriv x hx s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hΦ.deriv x hx s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    · exact fun s hs => (hΦ.sphere_bijOn s (Set.Ico_subset_Icc_self hs)).mapsTo hx
    · exact fun s hs => (b.blockCurve_isIntegralCurve x s).continuousAt.continuousWithinAt
    · intro s hs
      have hsIcc := Set.Ico_subset_Icc_self hs
      haveI := isProbabilityMeasure_map_flow hΦ hsIcc
      have hbsph : b.blockFlow s x ∈ sphere d := b.blockFlow_mem_sphere hx hs.1
      have hfeq : p.field (μ0.map (Φ s)) (b.blockFlow s x) = b.field (b.blockFlow s x) := by
        show (pParkScaled A z ω cosR T hT).field (μ0.map (Φ s)) (b.blockFlow s x)
          = scaledGatedField A z ω cosR (b.blockFlow s x)
        exact pParkScaled_field_eq_scaledGatedField_of_mem_sphere A hz hT hbsph (μ0.map (Φ s))
      rw [hfeq]
      exact (b.blockCurve_isIntegralCurve x s).hasDerivWithinAt
    · exact fun s hs => b.blockFlow_mem_sphere hx (Set.Ico_subset_Icc_self hs).1
    · show Φ 0 x = b.blockFlow 0 x
      rw [hΦ.init, b.blockFlow_zero]; rfl
  exact hEq ht

/-- **The measure-level bridge, scaled form.** The mean-field flow of `[pParkScaled A z ω cosR T hT]`
and the linear flow of `[scaledGatedBlock hA hz hω hcosR hT]` push forward a sphere-supported
probability measure to the SAME measure. -/
theorem attnMeasureFlow_pParkScaled_eq_measureFlow_scaledGatedBlock {A : ℝ} (hA : 0 ≤ A)
    {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR T : ℝ} (hcosR : (-1 : ℝ) ≤ cosR) (hT : 0 ≤ T)
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0) :
    attnMeasureFlow [pParkScaled A z ω cosR T hT] μ0
      = measureFlow [scaledGatedBlock hA hz hω hcosR hT] T μ0 := by
  have hex := @exists_meanFieldFlow d (pParkScaled A z ω cosR T hT) μ0 ‹_› hμ0S
  set Φ := hex.choose with hΦdef
  have hΦspec : IsMeanFieldFlow (pParkScaled A z ω cosR T hT) μ0 Φ := hex.choose_spec
  have hstep : attnStep (pParkScaled A z ω cosR T hT) μ0
      = μ0.map (Φ (pParkScaled A z ω cosR T hT).duration) := by
    unfold attnStep
    rw [dif_pos ⟨‹_›, hμ0S⟩]
  show attnStep (pParkScaled A z ω cosR T hT) μ0 = _
  rw [hstep, measureFlow]
  have hdur : (pParkScaled A z ω cosR T hT).duration = T := rfl
  have hflowsingle : flowMap [scaledGatedBlock hA hz hω hcosR hT] T
      = (scaledGatedBlock hA hz hω hcosR hT).blockFlow T := by
    rw [flowMap_cons, flowMap_nil]; rfl
  rw [hflowsingle, hdur]
  apply Measure.map_congr
  filter_upwards [hμ0S] with x hx
  exact attnFlow_eq_blockFlow_scaledGatedBlock hA hz hω hcosR hT hμ0S Φ hΦspec hx ⟨hT, le_refl T⟩

end MeasureToMeasure.Leaves
