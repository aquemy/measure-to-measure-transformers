import ForMathlib.TangentialProjector
import MeasureToMeasure.Foundations.Sphere

/-!
# The tangential projector `P_x^⊥ = I - x xᵀ`

Layer normalization in the Transformer continuity equation (1.2)-(1.3) projects the velocity
field onto the tangent space `T_x 𝕊^{d-1}`. For a unit vector `x`, the orthogonal projector onto
`{x}^⊥` is `P_x^⊥ = I_d - x xᵀ`, i.e. `P_x^⊥ v = v - ⟪x, v⟫ x`.

This file specializes `tangentialProjector` to `Eucl d` (an `abbrev` for
`InnerProductGeometry.tangentialProjector`, not a re-declared def -- there is exactly one definition)
and records the algebraic identities used throughout (`L1` in the project ledger): symmetry,
idempotence, that it annihilates `x`, and the key quadratic identity `⟪P_x^⊥ v, v⟫ = ‖v‖² - ⟪x, v⟫²`
for `‖x‖ = 1`, which drives the gate ODE (B.5) and the barycenter ODE (B.9). The proofs delegate to
the generic versions in `ForMathlib.TangentialProjector` (namespace `InnerProductGeometry`), which
state the same facts for an arbitrary real inner product space.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The tangential projector `P_x^⊥ v = v - ⟪x, v⟫ x` on `Eucl d`. For `‖x‖ = 1` this is the
orthogonal projection onto the tangent space `{x}^⊥`. An `abbrev` for
`InnerProductGeometry.tangentialProjector`, specialized to this file's ambient space. -/
noncomputable abbrev tangentialProjector (x v : Eucl d) : Eucl d :=
  InnerProductGeometry.tangentialProjector x v

@[simp] theorem tangentialProjector_apply (x v : Eucl d) :
    tangentialProjector x v = v - (⟪x, v⟫) • x := rfl

/-- `P_x^⊥` is linear in the vector argument (additivity). -/
theorem tangentialProjector_add (x v w : Eucl d) :
    tangentialProjector x (v + w) = tangentialProjector x v + tangentialProjector x w :=
  InnerProductGeometry.tangentialProjector_add x v w

/-- `P_x^⊥` commutes with scalar multiplication in the vector argument. -/
theorem tangentialProjector_smul (x : Eucl d) (c : ℝ) (v : Eucl d) :
    tangentialProjector x (c • v) = c • tangentialProjector x v :=
  InnerProductGeometry.tangentialProjector_smul x c v

/-- `P_x^⊥` annihilates `x` itself when `x` is a unit vector. -/
theorem tangentialProjector_self {x : Eucl d} (hx : x ∈ sphere d) :
    tangentialProjector x x = 0 :=
  InnerProductGeometry.tangentialProjector_self_of_norm_eq_one (norm_eq_one_of_mem_sphere hx)

/-- Symmetry: `⟪P_x^⊥ u, v⟫ = ⟪u, P_x^⊥ v⟫`. -/
theorem tangentialProjector_symm (x u v : Eucl d) :
    ⟪tangentialProjector x u, v⟫ = ⟪u, tangentialProjector x v⟫ :=
  InnerProductGeometry.tangentialProjector_symm x u v

/-- Idempotence on the unit sphere: `P_x^⊥ (P_x^⊥ v) = P_x^⊥ v`. -/
theorem tangentialProjector_idem {x : Eucl d} (hx : x ∈ sphere d) (v : Eucl d) :
    tangentialProjector x (tangentialProjector x v) = tangentialProjector x v :=
  InnerProductGeometry.tangentialProjector_idem_of_norm_eq_one (norm_eq_one_of_mem_sphere hx) v

/-- The key quadratic identity (L1): `⟪P_x^⊥ v, v⟫ = ‖v‖² - ⟪x, v⟫²`, for ANY `x` (the identity is
unconditional; no unit-vector hypothesis is needed — matching the ForMathlib generalization). This is
the scalar that appears in the gate ODE (B.5) and the barycenter ODE (B.9), both stated for `x` on the
sphere. -/
theorem projector_inner_sub_sq (x : Eucl d) (v : Eucl d) :
    ⟪tangentialProjector x v, v⟫ = ‖v‖ ^ 2 - ⟪x, v⟫ ^ 2 :=
  InnerProductGeometry.inner_tangentialProjector_self_eq_norm_sq_sub_inner_sq x v

end MeasureToMeasure
