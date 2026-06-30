import MeasureToMeasure.Foundations.Sphere

/-!
# The tangential projector `P_x^⊥ = I - x xᵀ`

Layer normalization in the Transformer continuity equation (1.2)-(1.3) projects the velocity
field onto the tangent space `T_x 𝕊^{d-1}`. For a unit vector `x`, the orthogonal projector onto
`{x}^⊥` is `P_x^⊥ = I_d - x xᵀ`, i.e. `P_x^⊥ v = v - ⟪x, v⟫ x`.

This file defines `tangentialProjector` and proves the algebraic identities used throughout
(`L1` in the project ledger): symmetry, idempotence, that it annihilates `x`, and the key
quadratic identity `⟪P_x^⊥ v, v⟫ = ‖v‖² - ⟪x, v⟫²` for `‖x‖ = 1`, which drives the gate ODE
(B.5) and the barycenter ODE (B.9).
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The tangential projector `P_x^⊥ v = v - ⟪x, v⟫ x`. For `‖x‖ = 1` this is the orthogonal
projection onto the tangent space `{x}^⊥`. -/
noncomputable def tangentialProjector (x v : Eucl d) : Eucl d := v - (⟪x, v⟫) • x

@[simp] theorem tangentialProjector_apply (x v : Eucl d) :
    tangentialProjector x v = v - (⟪x, v⟫) • x := rfl

/-- `P_x^⊥` is linear in the vector argument (additivity). -/
theorem tangentialProjector_add (x v w : Eucl d) :
    tangentialProjector x (v + w) = tangentialProjector x v + tangentialProjector x w := by
  simp only [tangentialProjector, inner_add_right, add_smul]
  abel

/-- `P_x^⊥` commutes with scalar multiplication in the vector argument. -/
theorem tangentialProjector_smul (x : Eucl d) (c : ℝ) (v : Eucl d) :
    tangentialProjector x (c • v) = c • tangentialProjector x v := by
  simp only [tangentialProjector, inner_smul_right, smul_sub, smul_smul]

/-- `P_x^⊥` annihilates `x` itself when `x` is a unit vector. -/
theorem tangentialProjector_self {x : Eucl d} (hx : x ∈ sphere d) :
    tangentialProjector x x = 0 := by
  have h : ⟪x, x⟫ = 1 := inner_self_eq_one_of_mem_sphere hx
  rw [tangentialProjector, h, one_smul, sub_self]

/-- Symmetry: `⟪P_x^⊥ u, v⟫ = ⟪u, P_x^⊥ v⟫`. -/
theorem tangentialProjector_symm (x u v : Eucl d) :
    ⟪tangentialProjector x u, v⟫ = ⟪u, tangentialProjector x v⟫ := by
  simp only [tangentialProjector, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, real_inner_comm x u, RCLike.conj_to_real]
  ring

/-- Idempotence on the unit sphere: `P_x^⊥ (P_x^⊥ v) = P_x^⊥ v`. -/
theorem tangentialProjector_idem {x : Eucl d} (hx : x ∈ sphere d) (v : Eucl d) :
    tangentialProjector x (tangentialProjector x v) = tangentialProjector x v := by
  have h : ⟪x, x⟫ = 1 := inner_self_eq_one_of_mem_sphere hx
  simp only [tangentialProjector, inner_sub_right, inner_smul_right, h]
  module

/-- The key quadratic identity (L1): for a unit vector `x`,
`⟪P_x^⊥ v, v⟫ = ‖v‖² - ⟪x, v⟫²`. This is the scalar that appears in the gate ODE (B.5)
and the barycenter ODE (B.9). -/
theorem projector_inner_sub_sq {x : Eucl d} (hx : x ∈ sphere d) (v : Eucl d) :
    ⟪tangentialProjector x v, v⟫ = ‖v‖ ^ 2 - ⟪x, v⟫ ^ 2 := by
  have h : ⟪x, x⟫ = 1 := inner_self_eq_one_of_mem_sphere hx
  simp only [tangentialProjector, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq]
  ring

end MeasureToMeasure
