/-
Copyright (c) 2026 Alexandre Quemy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Quemy
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The tangential projector `P_x v = v - ⟪x, v⟫ • x`

For a unit vector `x` in a real inner product space, `P_x v = v - ⟪x, v⟫ • x` is the orthogonal
projection of `v` onto the hyperplane `{x}ᗮ` (the tangent space to the unit sphere at `x`). This
file records the elementary algebraic identities: linearity in the vector argument, that `P_x`
annihilates `x`, self-adjointness, idempotence, and the quadratic identity
`⟪P_x v, v⟫ = ‖v‖² - ⟪x, v⟫²`.

These are stated for a general `[NormedAddCommGroup E] [InnerProductSpace ℝ E]`, with unit-vector
hypotheses written as `‖x‖ = 1`. Mathlib packages the general orthogonal projection onto a
subspace as `Submodule.starProjection`; the bridge lemma `tangentialProjector_eq_starProjection`
identifies this file's closed-form rank-one-complement special case, which is what appears
explicitly in layer-normalized dynamics on the sphere, with `(ℝ ∙ x)ᗮ.starProjection`.

*Preparation only:* staged for possible upstreaming, not contributed to Mathlib.
-/

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The tangential projector `P_x v = v - ⟪x, v⟫ • x`. For `‖x‖ = 1` this is the orthogonal
projection onto the hyperplane `{x}ᗮ`. -/
noncomputable def tangentialProjector (x v : E) : E := v - (⟪x, v⟫) • x

/-- Unfolding lemma for `tangentialProjector`; the `@[simp]` normal form. -/
@[simp] theorem tangentialProjector_apply (x v : E) :
    tangentialProjector x v = v - (⟪x, v⟫) • x := rfl

/-- `P_x` is additive in the vector argument. -/
theorem tangentialProjector_add (x v w : E) :
    tangentialProjector x (v + w) = tangentialProjector x v + tangentialProjector x w := by
  simp only [tangentialProjector, inner_add_right, add_smul]
  abel

/-- `P_x` commutes with scalar multiplication in the vector argument. -/
theorem tangentialProjector_smul (x : E) (c : ℝ) (v : E) :
    tangentialProjector x (c • v) = c • tangentialProjector x v := by
  simp only [tangentialProjector, inner_smul_right, smul_sub, smul_smul]

/-- `P_x` annihilates a unit vector `x`. -/
theorem tangentialProjector_self_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) :
    tangentialProjector x x = 0 := by
  have h : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; ring
  rw [tangentialProjector, h, one_smul, sub_self]

/-- Self-adjointness: `⟪P_x u, v⟫ = ⟪u, P_x v⟫`. -/
theorem tangentialProjector_symm (x u v : E) :
    ⟪tangentialProjector x u, v⟫ = ⟪u, tangentialProjector x v⟫ := by
  simp only [tangentialProjector, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, real_inner_comm x u, RCLike.conj_to_real]
  ring

/-- Idempotence for a unit vector: `P_x (P_x v) = P_x v`. -/
theorem tangentialProjector_idem_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) (v : E) :
    tangentialProjector x (tangentialProjector x v) = tangentialProjector x v := by
  have h : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; ring
  simp only [tangentialProjector, inner_sub_right, inner_smul_right, h]
  module

/-- The quadratic identity `⟪P_x v, v⟫ = ‖v‖² - ⟪x, v⟫²` (no unit-vector hypothesis needed). -/
theorem inner_tangentialProjector_self_eq_norm_sq_sub_inner_sq (x v : E) :
    ⟪tangentialProjector x v, v⟫ = ‖v‖ ^ 2 - ⟪x, v⟫ ^ 2 := by
  simp only [tangentialProjector, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq]
  ring

/-- For a unit vector `x`, the tangential projector agrees with Mathlib's star projection onto
the orthogonal complement of `ℝ ∙ x`. This ties the closed form `v - ⟪x, v⟫ • x` to the bundled
`Submodule.starProjection` API. -/
theorem tangentialProjector_eq_starProjection {x : E} (hx : ‖x‖ = 1) (v : E) :
    tangentialProjector x v = (ℝ ∙ x)ᗮ.starProjection v := by
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hx, tangentialProjector_apply]

end InnerProductGeometry
