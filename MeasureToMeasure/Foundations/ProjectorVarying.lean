import MeasureToMeasure.Foundations.Projector

/-!
# Tangential projector with a varying argument (M3b existence, leaf E2a-3)

Groundwork toward discharging `exists_meanFieldFlow`. The frozen attention field is
`normCutoff x • P_x^⊥ (rawFieldBall p ν x)`, a scalar cutoff times the tangential projector applied
to a field `w(x) = rawFieldBall p ν x` that **varies with the base point** `x`. To assemble it as a
globally-Lipschitz `Block` (via `GatedBlock.lipschitzWith_smul_of_vanishing`), we need the projector
factor `x ↦ P_x^⊥ (w x)` to be bounded and Lipschitz *on the ball of radius 2* (off which the cutoff
kills it).

`GatedBlock.lean` proved the analogous estimates only for a **constant** unit direction `ω`
(`tangentialProjector_norm_le`, `tangentialProjector_lipschitz_onBall`). Here we record the
generalizations this leaf needs, all field-independent geometry (`-- ForMathlib candidate:`):

* `norm_tangentialProjector_le_general` — `‖P_x^⊥ v‖ ≤ (1 + ‖x‖²)‖v‖`, any `x, v`;
* `norm_tangentialProjector_sub_point_le_general` — `‖P_x^⊥ v - P_y^⊥ v‖ ≤ (‖x‖+‖y‖)‖v‖‖x-y‖`, any
  `x, y, v` (generalizing the sphere-only `MeanFieldWellPosed.norm_tangentialProjector_sub_point_le`);
* `norm_tangentialProjector_comp_le_onBall` / `norm_tangentialProjector_comp_sub_le_onBall` — the
  **varying-argument** composite `x ↦ P_x^⊥ (w x)`, for a field `w` bounded by `C` and `L`-Lipschitz,
  is bounded by `5C` and `(5L + 4C)`-Lipschitz on the ball of radius `2`. The Lipschitz split is
  `P_x^⊥(w x - w y)` (linearity in the argument, projector bound `5` on the ball) plus
  `P_x^⊥(w y) - P_y^⊥(w y)` (base-point modulus, `‖x‖ + ‖y‖ ≤ 4`).

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open scoped RealInnerProductSpace

namespace MeasureToMeasure

variable {d : ℕ}

/-- **General projector bound:** `‖P_x^⊥ v‖ ≤ (1 + ‖x‖²)·‖v‖`, with no unit assumption on `x`
(the `‖x‖ = 1` case, where this is `‖v‖`, is `MeanFieldWellPosed.norm_tangentialProjector_le`). -/
theorem norm_tangentialProjector_le_general (x v : Eucl d) :
    ‖tangentialProjector x v‖ ≤ (1 + ‖x‖ ^ 2) * ‖v‖ := by
  have hcs : |⟪x, v⟫| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
  calc ‖tangentialProjector x v‖ = ‖v - ⟪x, v⟫ • x‖ := by rw [tangentialProjector_apply]
    _ ≤ ‖v‖ + ‖⟪x, v⟫ • x‖ := norm_sub_le _ _
    _ = ‖v‖ + |⟪x, v⟫| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖v‖ + (‖x‖ * ‖v‖) * ‖x‖ := by gcongr
    _ = (1 + ‖x‖ ^ 2) * ‖v‖ := by ring

/-- **General projector base-point modulus:** `‖P_x^⊥ v - P_y^⊥ v‖ ≤ (‖x‖ + ‖y‖)·‖v‖·‖x - y‖`, with no
unit assumption (generalizes the sphere-only `MeanFieldWellPosed.norm_tangentialProjector_sub_point_le`,
where `‖x‖ = ‖y‖ = 1` gives the constant `2`). Writing `P_x^⊥ v - P_y^⊥ v = ⟪y-x,v⟫•y + ⟪x,v⟫•(y-x)`
and bounding each inner product by Cauchy–Schwarz. -/
theorem norm_tangentialProjector_sub_point_le_general (x y v : Eucl d) :
    ‖tangentialProjector x v - tangentialProjector y v‖ ≤ (‖x‖ + ‖y‖) * ‖v‖ * ‖x - y‖ := by
  have key : tangentialProjector x v - tangentialProjector y v
      = (⟪y - x, v⟫ : ℝ) • y + (⟪x, v⟫ : ℝ) • (y - x) := by
    simp only [tangentialProjector_apply, inner_sub_left, sub_smul, smul_sub]; abel
  have h1 : ‖(⟪y - x, v⟫ : ℝ) • y‖ ≤ ‖x - y‖ * ‖v‖ * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hle : |(⟪y - x, v⟫ : ℝ)| ≤ ‖x - y‖ * ‖v‖ := by
      calc |(⟪y - x, v⟫ : ℝ)| ≤ ‖y - x‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ = ‖x - y‖ * ‖v‖ := by rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have h2 : ‖(⟪x, v⟫ : ℝ) • (y - x)‖ ≤ ‖x‖ * ‖v‖ * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, norm_sub_rev y x]
    exact mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
  calc ‖tangentialProjector x v - tangentialProjector y v‖
      = ‖(⟪y - x, v⟫ : ℝ) • y + (⟪x, v⟫ : ℝ) • (y - x)‖ := by rw [key]
    _ ≤ ‖(⟪y - x, v⟫ : ℝ) • y‖ + ‖(⟪x, v⟫ : ℝ) • (y - x)‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖v‖ * ‖y‖ + ‖x‖ * ‖v‖ * ‖x - y‖ := add_le_add h1 h2
    _ = (‖x‖ + ‖y‖) * ‖v‖ * ‖x - y‖ := by ring

/-- Linearity of the tangential projector in its argument on a difference (proved inline to keep this
file's dependencies to `Projector`; the same identity is `MeanFieldWellPosed.tangentialProjector_sub`). -/
private theorem tangentialProjector_sub_arg (x a b : Eucl d) :
    tangentialProjector x (a - b) = tangentialProjector x a - tangentialProjector x b := by
  simp only [tangentialProjector_apply, inner_sub_right, sub_smul]; abel

/-- **Composite bound on the ball:** for a field `w` with `‖w x‖ ≤ C`, the projector-of-varying-argument
`x ↦ P_x^⊥ (w x)` is bounded by `5C` on the ball of radius `2` (`1 + ‖x‖² ≤ 5`). -/
theorem norm_tangentialProjector_comp_le_onBall {w : Eucl d → Eucl d} {C : ℝ} {x : Eucl d}
    (hwB : ‖w x‖ ≤ C) (hx : ‖x‖ ≤ 2) :
    ‖tangentialProjector x (w x)‖ ≤ 5 * C := by
  calc ‖tangentialProjector x (w x)‖ ≤ (1 + ‖x‖ ^ 2) * ‖w x‖ :=
        norm_tangentialProjector_le_general _ _
    _ ≤ 5 * C := by
        apply mul_le_mul _ hwB (norm_nonneg _) (by norm_num)
        nlinarith [norm_nonneg x, hx]

/-- **Composite base-point modulus on the ball:** for a field `w` bounded by `C` (globally) and with
`‖w x - w y‖ ≤ L‖x - y‖`, the projector-of-varying-argument `x ↦ P_x^⊥ (w x)` is `(5L + 4C)`-Lipschitz
on the ball of radius `2`. The difference splits as `P_x^⊥(w x - w y)` (linearity in the argument,
projector bound `5`) plus `P_x^⊥(w y) - P_y^⊥(w y)` (base-point modulus, `‖x‖ + ‖y‖ ≤ 4`). -/
theorem norm_tangentialProjector_comp_sub_le_onBall {w : Eucl d → Eucl d} {C L : ℝ} {x y : Eucl d}
    (hwB : ∀ z, ‖w z‖ ≤ C) (hwL : ‖w x - w y‖ ≤ L * ‖x - y‖) (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2) :
    ‖tangentialProjector x (w x) - tangentialProjector y (w y)‖ ≤ (5 * L + 4 * C) * ‖x - y‖ := by
  have hsplit : tangentialProjector x (w x) - tangentialProjector y (w y)
      = tangentialProjector x (w x - w y)
        + (tangentialProjector x (w y) - tangentialProjector y (w y)) := by
    rw [tangentialProjector_sub_arg]; abel
  have hB1 : ‖tangentialProjector x (w x - w y)‖ ≤ 5 * L * ‖x - y‖ := by
    calc ‖tangentialProjector x (w x - w y)‖ ≤ (1 + ‖x‖ ^ 2) * ‖w x - w y‖ :=
          norm_tangentialProjector_le_general _ _
      _ ≤ 5 * (L * ‖x - y‖) := by
          apply mul_le_mul _ hwL (norm_nonneg _) (by norm_num)
          nlinarith [norm_nonneg x, hx]
      _ = 5 * L * ‖x - y‖ := by ring
  have hB2 : ‖tangentialProjector x (w y) - tangentialProjector y (w y)‖ ≤ 4 * C * ‖x - y‖ := by
    have hfac : (‖x‖ + ‖y‖) * ‖w y‖ ≤ 4 * C :=
      mul_le_mul (by linarith) (hwB y) (norm_nonneg _) (by norm_num)
    calc ‖tangentialProjector x (w y) - tangentialProjector y (w y)‖
        ≤ (‖x‖ + ‖y‖) * ‖w y‖ * ‖x - y‖ := norm_tangentialProjector_sub_point_le_general _ _ _
      _ ≤ 4 * C * ‖x - y‖ := mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
  calc ‖tangentialProjector x (w x) - tangentialProjector y (w y)‖
      = ‖tangentialProjector x (w x - w y)
          + (tangentialProjector x (w y) - tangentialProjector y (w y))‖ := by rw [hsplit]
    _ ≤ ‖tangentialProjector x (w x - w y)‖
          + ‖tangentialProjector x (w y) - tangentialProjector y (w y)‖ := norm_add_le _ _
    _ ≤ 5 * L * ‖x - y‖ + 4 * C * ‖x - y‖ := add_le_add hB1 hB2
    _ = (5 * L + 4 * C) * ‖x - y‖ := by ring

end MeasureToMeasure
