import MeasureToMeasure.Leaves.DivergenceFormula

/-!
# The mean-field parking primitive (`exists_parked_schedule` leaf 1)

`exists_parked_schedule` (Appendix B) needs a mean-field analog of `GatedPark.lean`'s linear-layer
fact `flowMap_gatedBlock_id_of_inner_le`: an `AttnParams` block whose field vanishes off a cap, for
**every** measure (not just one), so that a `IsMeanFieldFlow` of that block fixes every off-cap
point regardless of how the *rest* of the family's mass moves.

**The construction.** `pPark z ω cosR T hT` is the `AttnParams` block with `V = 0` (killing the
softmax/attention term's measure-dependence entirely -- the field no longer sees `ν` at all), and a
rank-1 perceptron term `U, b, W` chosen so that `W (reluVec (U x + b)) = (⟪z,x⟫ - cosR)₊ • ω` --
exactly the linear layer's `gatedField z ω cosR x` restricted to the ReLU-gate factor (the
`normCutoff` radial cutoff `GatedBlock.lean` needs to tame the field's Lipschitz constant *away
from the sphere* is not needed here: `AttnParams.field` is already known globally Lipschitz-in-point
on the sphere for *any* choice of `V,B,W,U,b`, via `norm_field_sub_point_le`, already banked by the
M3b well-posedness campaign). Since `V = 0`, the field is measure-independent, so it vanishes off
the cap `{x | ⟪z,x⟫ ≤ cosR}` for every measure at once (`pPark_field_eq_zero_of_inner_le`).

**The parking fact.** `attnFlow_id_of_inner_le`: for `x` off the cap, `Φ t x = x` for the whole
duration -- via the SAME `ODE_solution_unique_of_mem_Icc_right` route `meanFieldFlow_unique` uses
(field Lipschitz-on-the-sphere via `norm_field_sub_point_le`), but comparing `Φ` against the
CONSTANT trajectory `s ↦ x` rather than another mean-field flow: since the field vanishes AT `x`
for every measure, the constant trajectory trivially solves the same non-autonomous ODE, and
uniqueness pins `Φ · x` to it.

M3b/mid-level staging: consumed when `exists_parked_schedule` is discharged; see
`Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace NNReal
open MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The first standard basis vector, used as the single hidden coordinate a rank-1 perceptron
routes its ReLU gate through. -/
noncomputable def e1 (d : ℕ) [NeZero d] : Eucl d := EuclideanSpace.single 0 1

theorem e1_apply_zero (d : ℕ) [NeZero d] : (e1 d) 0 = 1 := by simp [e1]

theorem e1_apply_ne {d : ℕ} [NeZero d] {i : Fin d} (h : i ≠ 0) : (e1 d) i = 0 := by simp [e1, h]

/-- **The mean-field parking block.** `V = 0` kills the measure-dependent softmax term entirely;
the rank-1 perceptron `U, b, W` computes the ReLU gate `(⟪z,x⟫-cosR)₊` in the `e1`-coordinate and
routes it into the `ω` direction. -/
noncomputable def pPark (z ω : Eucl d) (cosR : ℝ) (T : ℝ) (hT : 0 ≤ T) [NeZero d] :
    AttnParams d where
  V := 0
  B := 0
  W := ContinuousLinearMap.smulRight (EuclideanSpace.proj (0 : Fin d)) ω
  U := (innerSL ℝ z).smulRight (e1 d)
  b := (-cosR) • e1 d
  duration := T
  duration_nonneg := hT

@[simp] theorem pPark_duration (z ω : Eucl d) (cosR T : ℝ) (hT : 0 ≤ T) [NeZero d] :
    (pPark (d := d) z ω cosR T hT).duration = T := rfl

/-- **The field reduces to the linear layer's ReLU-gated perceptron term**, for ANY measure `ν`
(since `V = 0` kills the measure dependence). -/
theorem pPark_field (z ω : Eucl d) (cosR T : ℝ) (hT : 0 ≤ T) [NeZero d] (x : Eucl d)
    (ν : Measure (Eucl d)) [IsProbabilityMeasure ν] :
    (pPark z ω cosR T hT).field ν x = max 0 (⟪z, x⟫ - cosR) • tangentialProjector x ω := by
  unfold AttnParams.field pPark
  simp only [zero_apply, zero_add]
  have hUb : ((innerSL ℝ z).smulRight (e1 d) : Eucl d →L[ℝ] Eucl d) x + (-cosR) • e1 d
      = (⟪z, x⟫ - cosR) • e1 d := by
    rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, sub_smul, neg_smul,
      sub_eq_add_neg]
  rw [hUb]
  have hrelu : reluVec ((⟪z, x⟫ - cosR) • e1 d) = max 0 (⟪z, x⟫ - cosR) • e1 d := by
    ext i
    by_cases hi : i = 0
    · subst hi; simp [reluVec, e1_apply_zero]
    · simp [reluVec, e1_apply_ne hi]
  rw [hrelu, ContinuousLinearMap.smulRight_apply]
  have hcoord : (EuclideanSpace.proj (0 : Fin d) : Eucl d →L[ℝ] ℝ)
      (max 0 (⟪z, x⟫ - cosR) • e1 d) = max 0 (⟪z, x⟫ - cosR) := by
    show (max 0 (⟪z, x⟫ - cosR) • e1 d) 0 = max 0 (⟪z, x⟫ - cosR)
    simp [e1_apply_zero]
  rw [hcoord, tangentialProjector_smul_right]

/-- **Off the cap the field vanishes, for every measure at once.** -/
theorem pPark_field_eq_zero_of_inner_le (z ω : Eucl d) (cosR T : ℝ) (hT : 0 ≤ T) [NeZero d]
    {x : Eucl d} (h : (⟪z, x⟫ : ℝ) ≤ cosR) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν] :
    (pPark z ω cosR T hT).field ν x = 0 := by
  rw [pPark_field]
  simp [max_eq_left (by linarith : (⟪z, x⟫ - cosR) ≤ 0)]

/-- **The mean-field parking fact.** A point off the cap is fixed by the WHOLE mean-field flow of
`pPark`, for the whole duration -- regardless of how the rest of the family's mass moves. -/
theorem attnFlow_id_of_inner_le (z ω : Eucl d) (cosR T : ℝ) (hT : 0 ≤ T) [NeZero d]
    {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pPark z ω cosR T hT) μ0 Φ)
    {x : Eucl d} (hx : x ∈ sphere d) (h : (⟪z, x⟫ : ℝ) ≤ cosR)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Φ t x = x := by
  set p := pPark z ω cosR T hT with hpdef
  set C : ℝ := (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖)
    + 2 * (‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖)) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hEq : Set.EqOn (fun s => Φ s x) (fun _ => x) (Set.Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun s y => p.field (μ0.map (Φ s)) y) (s := fun _ => sphere d)
      (K := C.toNNReal) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s hs
      have hsIcc := Set.Ico_subset_Icc_self hs
      haveI := isProbabilityMeasure_map_flow hΦ hsIcc
      have hmapS := map_flow_sphere_support hμ0S hΦ hsIcc
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro a ha b hb
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖p.field (μ0.map (Φ s)) a - p.field (μ0.map (Φ s)) b‖
          ≤ C * ‖a - b‖ := norm_field_sub_point_le p (μ0.map (Φ s)) hmapS ha hb
        _ = (C.toNNReal : ℝ) * ‖a - b‖ := by rw [Real.coe_toNNReal C hC0]
    · exact fun s hs => (hΦ.deriv x hx s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hΦ.deriv x hx s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    · exact fun s hs => (hΦ.sphere_bijOn s (Set.Ico_subset_Icc_self hs)).mapsTo hx
    · exact fun s _ => continuousWithinAt_const
    · intro s hs
      haveI := isProbabilityMeasure_map_flow hΦ (Set.Ico_subset_Icc_self hs)
      have hz : p.field (μ0.map (Φ s)) x = 0 :=
        pPark_field_eq_zero_of_inner_le z ω cosR T hT h (μ0.map (Φ s))
      rw [hz]
      exact (hasDerivAt_const s x).hasDerivWithinAt
    · exact fun s _ => hx
    · show Φ 0 x = x
      rw [hΦ.init]; rfl
  exact hEq ht

/-- **Packaging: the whole mean-field flow of `pPark` fixes an off-cap sphere-supported measure.**
The measure-generic form `attnFlow_id_of_inner_le` needs pointwise: any sphere-supported
probability measure whose mass avoids the open cap `{x | cosR < ⟪z, x⟫}` is left EXACTLY fixed by
the single-block schedule `[pPark z ω cosR T hT]`'s solution operator. This is the packaging both
Phase 2 and Phase 3's `pPark`-tailed constructions need: it lets the tail block be inserted without
disturbing any bystander mass that already avoids the cap. -/
theorem attnMeasureFlow_pPark_eq_of_off_cap (z ω : Eucl d) (cosR T : ℝ) (hT : 0 ≤ T) [NeZero d]
    (ρ : Measure (Eucl d)) [IsProbabilityMeasure ρ] (hρs : ρ (sphere d)ᶜ = 0)
    (hρcap : ρ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} = 0) :
    attnMeasureFlow [pPark z ω cosR T hT] ρ = ρ := by
  set p := pPark z ω cosR T hT with hpdef
  have hΦ := (@exists_meanFieldFlow d p ρ ‹_› hρs).choose_spec
  set Φ := (@exists_meanFieldFlow d p ρ ‹_› hρs).choose with hΦdef
  show attnStep p ρ = ρ
  unfold attnStep
  rw [dif_pos ⟨‹IsProbabilityMeasure ρ›, hρs⟩]
  have hid : ρ.map (Φ p.duration) = ρ.map (fun x => x) := by
    refine Measure.map_congr ?_
    rw [Filter.EventuallyEq, ae_iff]
    have hnull : ρ ((sphere d)ᶜ ∪ {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}) = 0 :=
      measure_union_null hρs hρcap
    refine measure_mono_null (fun x hx => ?_) hnull
    simp only [Set.mem_setOf_eq] at hx
    by_contra hxor
    apply hx
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_lt, not_not]
      at hxor
    obtain ⟨hxs, hxcap⟩ := hxor
    exact attnFlow_id_of_inner_le z ω cosR T hT hρs Φ hΦ hxs hxcap ⟨p.duration_nonneg, le_rfl⟩
  rw [hid, Measure.map_id']

end MeasureToMeasure.Leaves
