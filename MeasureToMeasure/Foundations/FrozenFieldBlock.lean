import MeasureToMeasure.Foundations.MeanFieldExistence
import MeasureToMeasure.Foundations.ProjectorVarying
import MeasureToMeasure.Foundations.GatedBlock

/-!
# The frozen attention field as a `Block` (M3b existence, leaf E2a-4)

The culmination of leaf E2a of the `exists_meanFieldFlow` campaign. For a *frozen* sphere-supported
probability measure `ν`, the paper's per-block velocity field `p.field ν x = P_x^⊥(V·A_B[ν](x) +
W·(Ux+b)₊)` is only defined/well-behaved on the sphere: the softmax `A_B[ν]` is bounded and Lipschitz
only on the unit ball, and the tangential projector `P_x^⊥` is quadratic (locally Lipschitz). A
Picard–Lindelöf existence proof needs a **globally** Lipschitz, bounded field. This file builds that
global extension and packages it as a genuine `Block`:

`attnFieldExt p ν x = normCutoff x • P_x^⊥ (rawFieldBall p ν x)`,

where (E2a-1/E2a-2) `rawFieldBall = rawField ∘ ballProj` retracts the softmax argument into the unit
ball — making the raw field globally bounded (`fieldBallBound`) and Lipschitz (`fieldBallLip`) — and
(E2a-3) the projector-of-varying-argument is bounded/Lipschitz on the ball of radius `2`, off which the
cutoff `normCutoff` kills the field. The gluing is `GatedBlock.lipschitzWith_smul_of_vanishing`
(compactly-supported cutoff × on-ball-nice vector field ⇒ globally Lipschitz), exactly as for the
linear `gatedBlock` — the difference being that here the projector's argument varies with the base
point (E2a-3's generalization of the constant-`ω` `GatedBlock` estimates).

`frozenBlock` discharges every `Block` obligation (global Lipschitz, global bound `5·fieldBallBound`,
radial-tangency with gate `attnGate`), and `attnFieldExt_eq_field_of_mem_sphere` records that on the
sphere the extended field is exactly `p.field ν`. This is the well-posedness datum the frozen-field
flow (E2b: `Block.isPicardLindelof` + `SphereFlow.sphere_invariant`) will consume; the Picard fixed
point over the measure trajectory (E3+) then closes `exists_meanFieldFlow`.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The uniform bound constant of the raw attention field: `‖V‖·e^{2‖B‖} + ‖W‖·(‖U‖+‖b‖)`. -/
noncomputable def fieldBallBound (p : AttnParams d) : ℝ :=
  ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖)

/-- The Lipschitz constant of the raw attention field: `‖V‖·2‖B‖e^{4‖B‖} + ‖W‖·‖U‖`. -/
noncomputable def fieldBallLip (p : AttnParams d) : ℝ :=
  ‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖

theorem fieldBallBound_nonneg (p : AttnParams d) : 0 ≤ fieldBallBound p := by
  unfold fieldBallBound; positivity

theorem fieldBallLip_nonneg (p : AttnParams d) : 0 ≤ fieldBallLip p := by
  unfold fieldBallLip; positivity

theorem five_bound_nonneg (p : AttnParams d) : 0 ≤ 5 * fieldBallBound p :=
  mul_nonneg (by norm_num) (fieldBallBound_nonneg p)

theorem fiveLip_four_bound_nonneg (p : AttnParams d) :
    0 ≤ 5 * fieldBallLip p + 4 * fieldBallBound p :=
  add_nonneg (mul_nonneg (by norm_num) (fieldBallLip_nonneg p))
    (mul_nonneg (by norm_num) (fieldBallBound_nonneg p))

theorem norm_rawFieldBall_le' (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) (x : Eucl d) : ‖rawFieldBall p ν x‖ ≤ fieldBallBound p := by
  unfold fieldBallBound; exact norm_rawFieldBall_le p ν hν x

theorem norm_rawFieldBall_sub_le' (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) (x y : Eucl d) :
    ‖rawFieldBall p ν x - rawFieldBall p ν y‖ ≤ fieldBallLip p * ‖x - y‖ := by
  unfold fieldBallLip; exact norm_rawFieldBall_sub_le p ν hν x y

/-- The **frozen attention field**, extended globally: `normCutoff x • P_x^⊥ (rawFieldBall p ν x)`.
The softmax argument is retracted into the unit ball by `ballProj` (inside `rawFieldBall`), and the
quadratic projector is localized near the sphere by `normCutoff`, so the whole field is globally
Lipschitz and bounded — a genuine `Block` field. On the sphere it equals `p.field ν`. -/
noncomputable def attnFieldExt (p : AttnParams d) (ν : Measure (Eucl d)) (x : Eucl d) : Eucl d :=
  normCutoff x • tangentialProjector x (rawFieldBall p ν x)

/-- The radial **gate** of the extended field: `c(x) = -normCutoff x · ⟪x, rawFieldBall p ν x⟫`. -/
noncomputable def attnGate (p : AttnParams d) (ν : Measure (Eucl d)) (x : Eucl d) : ℝ :=
  -(normCutoff x * ⟪x, rawFieldBall p ν x⟫)

/-- On the sphere the cutoff is `1` and `ballProj` is the identity, so the extended field is the
paper's velocity field `p.field ν`. -/
theorem attnFieldExt_eq_field_of_mem_sphere (p : AttnParams d) (ν : Measure (Eucl d)) {x : Eucl d}
    (hx : x ∈ sphere d) : attnFieldExt p ν x = p.field ν x := by
  have h1 : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  rw [attnFieldExt, normCutoff_eq_one h1.le, one_smul,
    rawFieldBall_eq_rawField_of_norm_le_one p ν h1.le]
  exact (field_eq_tangentialProjector_rawField p ν x).symm

/-- **Global bound on the extended field:** `‖attnFieldExt p ν x‖ ≤ 5·fieldBallBound p`. On the ball
the projector-of-varying-argument is bounded by `5C` and the cutoff by `1`; off the ball the cutoff
kills the field. -/
theorem norm_attnFieldExt_le (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) (x : Eucl d) : ‖attnFieldExt p ν x‖ ≤ 5 * fieldBallBound p := by
  rw [attnFieldExt, norm_smul, Real.norm_eq_abs]
  rcases le_or_gt 2 ‖x‖ with hx | hx
  · rw [normCutoff_eq_zero hx, abs_zero, zero_mul]; exact five_bound_nonneg p
  · calc |normCutoff x| * ‖tangentialProjector x (rawFieldBall p ν x)‖
        ≤ 1 * (5 * fieldBallBound p) :=
          mul_le_mul (abs_normCutoff_le_one x)
            (norm_tangentialProjector_comp_le_onBall (norm_rawFieldBall_le' p ν hν x) hx.le)
            (norm_nonneg _) (by norm_num)
      _ = 5 * fieldBallBound p := one_mul _

/-- **Radial-tangency identity:** `⟪x, attnFieldExt p ν x⟫ = attnGate p ν x · (‖x‖² - 1)`, so the field
is tangent on the sphere (where its flow stays). Holds for all `x` by a global computation. -/
theorem attnFieldExt_radial (p : AttnParams d) (ν : Measure (Eucl d)) (x : Eucl d) :
    ⟪x, attnFieldExt p ν x⟫ = attnGate p ν x * (‖x‖ ^ 2 - 1) := by
  simp only [attnFieldExt, attnGate, real_inner_smul_right, inner_tangentialProjector_left]
  ring

/-- Uniform bound on twice the gate: `|2·attnGate p ν x| ≤ 4·fieldBallBound p` (`normCutoff ≤ 1`,
`|⟪x, rawFieldBall⟫| ≤ ‖x‖·‖rawFieldBall‖ ≤ 2·C` on the support, zero off it). -/
theorem abs_two_attnGate_le (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) (x : Eucl d) : |2 * attnGate p ν x| ≤ 4 * fieldBallBound p := by
  rcases le_or_gt 2 ‖x‖ with hx | hx
  · rw [attnGate, normCutoff_eq_zero hx]
    simp only [zero_mul, neg_zero, mul_zero, abs_zero]
    exact mul_nonneg (by norm_num) (fieldBallBound_nonneg p)
  · have hnc : |normCutoff x| ≤ 1 := abs_normCutoff_le_one x
    have hi : |⟪x, rawFieldBall p ν x⟫| ≤ 2 * fieldBallBound p := by
      calc |⟪x, rawFieldBall p ν x⟫| ≤ ‖x‖ * ‖rawFieldBall p ν x‖ := abs_real_inner_le_norm _ _
        _ ≤ 2 * fieldBallBound p :=
            mul_le_mul hx.le (norm_rawFieldBall_le' p ν hν x) (norm_nonneg _) (by norm_num)
    have hprod : |normCutoff x| * |⟪x, rawFieldBall p ν x⟫| ≤ 1 * (2 * fieldBallBound p) :=
      mul_le_mul hnc hi (abs_nonneg _) zero_le_one
    have hrw : |2 * attnGate p ν x| = 2 * (|normCutoff x| * |⟪x, rawFieldBall p ν x⟫|) := by
      rw [attnGate, mul_neg, abs_neg, abs_mul, abs_mul]; norm_num
    rw [hrw]; linarith [hprod]

/-- **The extended field is globally Lipschitz.** `GatedBlock.lipschitzWith_smul_of_vanishing` with the
compactly-supported `1`-Lipschitz cutoff `normCutoff` (`Ks = Bs = 1`, vanishing outside the ball of
radius `2`) and the projector-of-varying-argument, bounded (`5·fieldBallBound`) and Lipschitz
(`5·fieldBallLip + 4·fieldBallBound`) on that ball (leaf E2a-3). Stated about the `def` (not a lambda)
so the constant and the `Eucl d` pseudo-emetric instance match `Block.field`, as for `gatedField`. -/
theorem attnFieldExt_lipschitz (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) :
    LipschitzWith (Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
      + Real.toNNReal (5 * fieldBallBound p)) (attnFieldExt p ν) := by
  have h := lipschitzWith_smul_of_vanishing (F := Eucl d) (Ks := 1) (Bs := 1)
    (Kv := Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p))
    (Bv := Real.toNNReal (5 * fieldBallBound p)) (R := 2)
    (s := normCutoff) (V := fun x => tangentialProjector x (rawFieldBall p ν x))
    normCutoff_lipschitz (fun x => abs_normCutoff_le_one x)
    (fun x hx => normCutoff_eq_zero hx)
    (fun x y hx hy => by
      rw [Real.coe_toNNReal _ (fiveLip_four_bound_nonneg p)]
      exact norm_tangentialProjector_comp_sub_le_onBall
        (fun z => norm_rawFieldBall_le' p ν hν z) (norm_rawFieldBall_sub_le' p ν hν x y) hx hy)
    (fun x hx => by
      rw [Real.coe_toNNReal _ (five_bound_nonneg p)]
      exact norm_tangentialProjector_comp_le_onBall (norm_rawFieldBall_le' p ν hν x) hx)
  rw [one_mul, one_mul] at h
  exact h

/-- **The frozen attention `Block`.** For a sphere-supported probability measure `ν` and duration
`T ≥ 0`, the globally-extended attention field is a genuine well-posed `Block`: globally Lipschitz
(via `GatedBlock.lipschitzWith_smul_of_vanishing`, cutoff × on-ball-bounded-Lipschitz projector),
bounded by `5·fieldBallBound p`, radially tangent with gate `attnGate`. On the sphere its field is
`p.field ν`, so its flow (via `Block.isPicardLindelof` + `SphereFlow.sphere_invariant`) is the frozen
mean-field characteristic. -/
noncomputable def frozenBlock (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {T : ℝ} (hT : 0 ≤ T) : Block d where
  field := attnFieldExt p ν
  lipConst := Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
    + Real.toNNReal (5 * fieldBallBound p)
  lipschitz := attnFieldExt_lipschitz p ν hν
  bound := Real.toNNReal (5 * fieldBallBound p)
  field_le := fun x => by
    rw [Real.coe_toNNReal _ (five_bound_nonneg p)]
    exact norm_attnFieldExt_le p ν hν x
  gate := attnGate p ν
  gateBound := 4 * fieldBallBound p
  gate_le := abs_two_attnGate_le p ν hν
  radial := attnFieldExt_radial p ν
  dur := T
  dur_nonneg := hT

/-- The frozen block's field is the extended field (definitional, recorded for downstream use). -/
theorem frozenBlock_field (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {T : ℝ} (hT : 0 ≤ T) :
    (frozenBlock p ν hν hT).field = attnFieldExt p ν := rfl

end MeasureToMeasure.Foundations
