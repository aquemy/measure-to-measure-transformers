import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The radial retraction onto the closed unit ball (M3b existence, leaf E2a-1)

Groundwork for discharging `exists_meanFieldFlow`. To build the frozen attention field as a genuine
globally-Lipschitz `Block` (the well-posedness datum Picard–Lindelöf needs), we precompose the
softmax argument with the **radial retraction onto the closed unit ball** `ballProj`. Because the
project's softmax point-modulus (`AttentionEstimates.attnAvg_sub_le_of_norm_le`) and bound
(`norm_attnAvg_le`) hold on the unit ball `‖x‖ ≤ 1`, and `ballProj` is `1`-Lipschitz and lands in
that ball while fixing the sphere, `attnAvg ∘ ballProj` is globally Lipschitz and bounded *directly*
from the banked estimates — no re-derivation on a neighborhood.

Mathlib has the orthogonal projection onto a *subspace* (`Submodule.lipschitzWith_orthogonalProjection`)
but not the metric projection onto the closed unit ball, so we prove its nonexpansiveness here via
firm nonexpansiveness (`ballProj_variational` + Cauchy–Schwarz).

`-- ForMathlib candidate:` the whole file is generic (any real inner product space), independent of
the paper's construction.
-/

open scoped RealInnerProductSpace

namespace MeasureToMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **radial retraction** onto the closed unit ball: the identity inside the ball, and `x/‖x‖`
outside. (The metric projection of `x` onto `{y | ‖y‖ ≤ 1}`.) -/
noncomputable def ballProj (x : E) : E := (‖x‖ ⊔ 1)⁻¹ • x

/-- On the closed unit ball `ballProj` is the identity (in particular on the unit sphere). -/
theorem ballProj_eq_self {x : E} (hx : ‖x‖ ≤ 1) : ballProj x = x := by
  rw [ballProj, max_eq_right hx, inv_one, one_smul]

/-- `ballProj` always lands in the closed unit ball. -/
theorem norm_ballProj_le (x : E) : ‖ballProj x‖ ≤ 1 := by
  rw [ballProj, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (le_trans zero_le_one (le_max_right _ _)),
    inv_mul_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_right _ _)), mul_one]
  exact le_max_left _ _

/-- **Projection variational inequality.** For any `a` and any `w` in the closed unit ball,
`⟪a - ballProj a, ballProj a - w⟫ ≥ 0`: outside the ball `a - ballProj a` is a nonnegative multiple
of `ballProj a`, and `⟪ballProj a, w⟫ ≤ ‖ballProj a‖ = 1`. -/
theorem ballProj_variational (a : E) {w : E} (hw : ‖w‖ ≤ 1) :
    0 ≤ ⟪a - ballProj a, ballProj a - w⟫ := by
  rcases le_or_gt ‖a‖ 1 with h | h
  · rw [ballProj_eq_self h, sub_self, inner_zero_left]
  · have hpos : (0 : ℝ) < ‖a‖ := lt_trans zero_lt_one h
    have hmax : (‖a‖ ⊔ 1) = ‖a‖ := max_eq_left h.le
    have hnorm_fa : ‖ballProj a‖ = 1 := by
      rw [ballProj, hmax, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos,
        inv_mul_cancel₀ (ne_of_gt hpos)]
    have hfa : a - ballProj a = (‖a‖ - 1) • ballProj a := by
      rw [ballProj, hmax, smul_smul,
        show (‖a‖ - 1) * ‖a‖⁻¹ = 1 - ‖a‖⁻¹ by field_simp, sub_smul, one_smul]
    rw [hfa, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_mul_norm, hnorm_fa]
    have hcs : ⟪ballProj a, w⟫ ≤ 1 :=
      le_trans (real_inner_le_norm _ _) (by rw [hnorm_fa, one_mul]; exact hw)
    have h1 : (0 : ℝ) ≤ ‖a‖ - 1 := by linarith
    nlinarith [hcs, h1]

/-- **The radial retraction is `1`-Lipschitz** (nonexpansive), the metric-projection property. Proved
by firm nonexpansiveness: `‖ballProj x - ballProj y‖² ≤ ⟪x - y, ballProj x - ballProj y⟫`, from the
two variational inequalities, then Cauchy–Schwarz. -/
theorem lipschitzWith_ballProj : LipschitzWith 1 (ballProj (E := E)) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  set fx := ballProj x with hfx
  set fy := ballProj y with hfy
  have hexpand : ⟪x - y, fx - fy⟫ - ‖fx - fy‖ ^ 2 =
      ⟪x - fx, fx - fy⟫ + ⟪y - fy, fy - fx⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm fy fx]
    ring
  have h1 : (0 : ℝ) ≤ ⟪x - fx, fx - fy⟫ := ballProj_variational x (norm_ballProj_le y)
  have h2 : (0 : ℝ) ≤ ⟪y - fy, fy - fx⟫ := ballProj_variational y (norm_ballProj_le x)
  have hfirm : ‖fx - fy‖ ^ 2 ≤ ⟪x - y, fx - fy⟫ := by nlinarith [hexpand, h1, h2]
  have hcs : ⟪x - y, fx - fy⟫ ≤ ‖x - y‖ * ‖fx - fy‖ := real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (fx - fy)) with h0 | h0
  · rw [← h0]; positivity
  · nlinarith [le_trans hfirm hcs, norm_nonneg (x - y), h0]

end MeasureToMeasure
