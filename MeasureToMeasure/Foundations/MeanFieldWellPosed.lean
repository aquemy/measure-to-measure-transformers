import MeasureToMeasure.Foundations.AttentionEstimates

/-!
# Lipschitz-in-measure modulus of the self-attention field (milestone M3b)

The McKean-Vlasov well-posedness axioms `exists_meanFieldFlow` / `meanFieldFlow_unique` of
`Foundations/Attention.lean` are the Picard-Lindelöf / Grönwall consequences of the velocity field
(1.2) being Lipschitz jointly in the *point* `x` and the *measure* `μ` (for the `W₁` metric). The
point modulus is `AttentionEstimates.attnAvg_sub_le_of_norm_le`; the vector Kantorovich-Rubinstein
machinery (`ofReal_norm_integral_sub_le_W1`) is the tool for the measure modulus.

This file assembles the **structural half** of the measure modulus, which is unconditional and
kernel-clean:

* `field_sub_measure_eq` — the field difference at a fixed point sees the measure only through the
  self-attention average: `field μ x - field ν x = P_x^⊥ (V (A_B[μ]x - A_B[ν]x))`. The perceptron
  term `W (U x + b)₊` is measure-independent, so it cancels exactly.
* `norm_field_sub_measure_le` — hence `‖field μ x - field ν x‖ ≤ ‖V‖ · ‖A_B[μ]x - A_B[ν]x‖` on the
  sphere, because the tangential projector is nonexpansive (`norm_tangentialProjector_le`).

This reduces the field's Lipschitz-in-measure modulus to the *self-attention average's* modulus
`‖A_B[μ]x - A_B[ν]x‖ ≲ W₁(μ, ν)` — the single remaining analytic estimate before a McKean-Vlasov
Grönwall/Picard argument can discharge the two axioms. It is the exact interface a mean-field ODE
theory (absent from Mathlib `v4.31.0`) would consume.
-/

namespace MeasureToMeasure.Foundations

open MeasureTheory MeasureToMeasure
open scoped RealInnerProductSpace ENNReal NNReal

variable {d : ℕ}

/-- The tangential projector is linear in the vector argument (subtraction form). -/
theorem tangentialProjector_sub (x u w : Eucl d) :
    tangentialProjector x (u - w) = tangentialProjector x u - tangentialProjector x w := by
  simp only [tangentialProjector_apply, inner_sub_right, sub_smul]
  abel

/-- **The tangential projector is nonexpansive at a unit vector:** `‖P_x^⊥ v‖ ≤ ‖v‖` for
`x ∈ 𝕊^{d-1}`. `P_x^⊥` is the orthogonal projection onto `{x}^⊥`, so it never increases norm;
concretely `‖P_x^⊥ v‖² = ‖v‖² - ⟪x, v⟫² ≤ ‖v‖²`. -/
theorem norm_tangentialProjector_le {x : Eucl d} (hx : x ∈ sphere d) (v : Eucl d) :
    ‖tangentialProjector x v‖ ≤ ‖v‖ := by
  -- `P_x^⊥ v ⟂ x`, so `⟪P_x^⊥ v, P_x^⊥ v⟫ = ⟪P_x^⊥ v, v⟫ = ‖v‖² - ⟪x,v⟫²`.
  have hperp : ⟪tangentialProjector x v, x⟫ = 0 := by
    rw [tangentialProjector_symm, tangentialProjector_self hx, inner_zero_right]
  have hself : ⟪tangentialProjector x v, tangentialProjector x v⟫
      = ⟪tangentialProjector x v, v⟫ := by
    nth_rewrite 2 [tangentialProjector_apply x v]
    rw [inner_sub_right, real_inner_smul_right, hperp, mul_zero, sub_zero]
  have hsq : ‖tangentialProjector x v‖ ^ 2 = ‖v‖ ^ 2 - ⟪x, v⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (tangentialProjector x v), hself,
      projector_inner_sub_sq hx]
  have hle : ‖tangentialProjector x v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg (⟪x, v⟫ : ℝ)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg v) hle

/-- **The field difference at a fixed point is carried by the self-attention average.** The
perceptron term `W (U x + b)₊` does not depend on the measure, so it cancels:
`field μ x - field ν x = P_x^⊥ (V (A_B[μ] x - A_B[ν] x))`. -/
theorem field_sub_measure_eq (p : AttnParams d) (μ ν : Measure (Eucl d)) (x : Eucl d) :
    p.field μ x - p.field ν x
      = tangentialProjector x (p.V (attnAvg p.B μ x - attnAvg p.B ν x)) := by
  simp only [AttnParams.field]
  rw [← tangentialProjector_sub]
  congr 1
  rw [map_sub p.V]
  abel

/-- **Structural measure modulus of the field.** On the sphere the field is Lipschitz in the
measure with the self-attention average's own modulus, scaled by the value matrix:
`‖field μ x - field ν x‖ ≤ ‖V‖ · ‖A_B[μ] x - A_B[ν] x‖`. Combined with a bound
`‖A_B[μ] x - A_B[ν] x‖ ≲ W₁(μ, ν)` (the remaining analytic estimate) this is the Lipschitz-in-`W₁`
modulus a McKean-Vlasov argument needs. -/
theorem norm_field_sub_measure_le (p : AttnParams d) (μ ν : Measure (Eucl d)) {x : Eucl d}
    (hx : x ∈ sphere d) :
    ‖p.field μ x - p.field ν x‖ ≤ ‖p.V‖ * ‖attnAvg p.B μ x - attnAvg p.B ν x‖ := by
  rw [field_sub_measure_eq]
  calc ‖tangentialProjector x (p.V (attnAvg p.B μ x - attnAvg p.B ν x))‖
      ≤ ‖p.V (attnAvg p.B μ x - attnAvg p.B ν x)‖ := norm_tangentialProjector_le hx _
    _ ≤ ‖p.V‖ * ‖attnAvg p.B μ x - attnAvg p.B ν x‖ := p.V.le_opNorm _

end MeasureToMeasure.Foundations
