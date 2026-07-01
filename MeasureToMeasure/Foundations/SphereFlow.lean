import MeasureToMeasure.Foundations.Projector

/-!
# Sphere invariance of the layer-normalized flow

The continuity equation (1.2)-(1.3) of Geshkovski-Rigollet-Ruiz-Balet transports mass by the
characteristic ODE `ẋ = P_x^⊥ (g(t, x))`, where `P_x^⊥` is the tangential projector
(`Foundations/Projector.lean`). Layer normalization *projects* the raw velocity onto the tangent
space, and the paper's whole construction lives on the unit sphere `𝕊^{d-1}`. This file proves the
foundational fact that makes that legitimate: **an integral curve of the projected field that starts
on the sphere stays on the sphere**.

The subtlety is that the projected field is only genuinely tangent *on* the sphere: for a raw field
`g` one has `⟪x, P_x^⊥ g⟫ = ⟪x, g⟫ (1 - ‖x‖²)`, which vanishes exactly when `‖x‖ = 1`. So one cannot
argue "the norm derivative is zero" directly. Instead `u(t) = ‖x t‖² - 1` satisfies the *linear
homogeneous* ODE `u' = c(t) u` with `u(0) = 0`, and Grönwall's inequality forces `u ≡ 0`. That is the
content of `norm_sq_eq_one_of_radial_tangent`; `sphere_invariant` is the projected-field wrapper.

This is reusable infrastructure: the same invariance underlies the mean-field flow (M3) and the
LaSalle/Lyapunov convergence analysis (M6).
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace
open Set

variable {d : ℕ}

/-- The tangential projector is radially tangent: `⟪x, P_x^⊥ w⟫ = ⟪x, w⟫ (1 - ‖x‖²)`. On the unit
sphere (`‖x‖ = 1`) this is `0`, i.e. `P_x^⊥ w` is tangent; off the sphere it measures the radial
drift that the Grönwall argument controls. -/
theorem inner_tangentialProjector_left (x w : Eucl d) :
    ⟪x, tangentialProjector x w⟫ = ⟪x, w⟫ * (1 - ‖x‖ ^ 2) := by
  simp only [tangentialProjector, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- The derivative of `t ↦ ‖x t‖² - 1` along an integral curve is `2 ⟪x t, v t⟫`. -/
theorem hasDerivAt_norm_sq_sub_one {x v : ℝ → Eucl d} {t : ℝ} (hx : HasDerivAt x (v t) t) :
    HasDerivAt (fun s => ‖x s‖ ^ 2 - 1) (2 * ⟪x t, v t⟫) t := by
  have hinner : HasDerivAt (fun s => (⟪x s, x s⟫ : ℝ)) (⟪x t, v t⟫ + ⟪v t, x t⟫) t :=
    hx.inner ℝ hx
  have h2 : (⟪x t, v t⟫ + ⟪v t, x t⟫ : ℝ) = 2 * ⟪x t, v t⟫ := by
    rw [real_inner_comm (v t) (x t)]; ring
  rw [h2] at hinner
  have hnorm : HasDerivAt (fun s => ‖x s‖ ^ 2) (2 * ⟪x t, v t⟫) t := by
    simpa only [real_inner_self_eq_norm_sq] using hinner
  simpa using hnorm.sub_const 1

/-- **Radial-tangency invariance (Grönwall core).** If an integral curve `ẋ = v` satisfies the
radial identity `⟪x t, v t⟫ = c t (‖x t‖² - 1)` with `|2 c t|` uniformly bounded on `[0, T]`, and
starts with unit norm, then it keeps unit norm on `[0, T]`.

The proof applies Grönwall to `u(t) = ‖x t‖² - 1`: it solves `u' = (2 c t) u`, so `‖u t‖ ≤
gronwallBound 0 K 0 t = 0`. -/
theorem norm_sq_eq_one_of_radial_tangent {x v : ℝ → Eucl d} {c : ℝ → ℝ} {K T : ℝ}
    (hx' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x (v t) t)
    (hrad : ∀ t ∈ Icc (0 : ℝ) T, (⟪x t, v t⟫ : ℝ) = c t * (‖x t‖ ^ 2 - 1))
    (hK : ∀ t ∈ Icc (0 : ℝ) T, |2 * c t| ≤ K)
    (hx0 : ‖x 0‖ = 1) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t‖ = 1 := by
  set u : ℝ → ℝ := fun t => ‖x t‖ ^ 2 - 1 with hu
  -- `u` is differentiable on `[0, T]` with derivative `(2 c t) * u t`.
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (2 * c t * u t) t := by
    intro t ht
    have h := hasDerivAt_norm_sq_sub_one (hx' t ht)
    have : (2 * ⟪x t, v t⟫ : ℝ) = 2 * c t * u t := by
      rw [hrad t ht]; simp only [hu]; ring
    rwa [this] at h
  -- Grönwall bound: `‖u t‖ ≤ gronwallBound 0 K 0 (t - 0) = 0`.
  have hcont : ContinuousOn u (Icc 0 T) := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hu0 : ‖u 0‖ ≤ 0 := by
    simp only [hu, hx0]; norm_num
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, ‖(2 * c t * u t : ℝ)‖ ≤ K * ‖u t‖ + 0 := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
    rw [add_zero, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hK t htc) (abs_nonneg _)
  intro t ht
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s hs => (hderiv s (Ico_subset_Icc_self hs)).hasDerivWithinAt) hu0 hbound t ht
  rw [gronwallBound_ε0_δ0] at hgron
  -- `‖u t‖ ≤ 0` forces `u t = 0`, i.e. `‖x t‖² = 1`, i.e. `‖x t‖ = 1`.
  have hut : u t = 0 := by
    have := norm_nonneg (u t)
    have h0 : ‖u t‖ = 0 := le_antisymm hgron (norm_nonneg _)
    simpa using h0
  have hsq : ‖x t‖ ^ 2 = 1 := by simpa only [hu, sub_eq_zero] using hut
  have := norm_nonneg (x t)
  nlinarith [hsq, norm_nonneg (x t)]

/-- **Sphere invariance of the layer-normalized flow.** An integral curve of the projected field
`ẋ = P_x^⊥ (g t)` that starts on the unit sphere stays on the unit sphere throughout `[0, T]`,
provided the raw radial drift `⟪x t, g t⟫` is uniformly bounded on the interval (automatic when `g`
is bounded, e.g. the attention field on the compact sphere).

This is the geometric core of the continuity equation's well-posedness on `𝕊^{d-1}`. -/
theorem sphere_invariant {x g : ℝ → Eucl d} {K T : ℝ}
    (hx' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x (tangentialProjector (x t) (g t)) t)
    (hK : ∀ t ∈ Icc (0 : ℝ) T, |2 * -⟪x t, g t⟫| ≤ K)
    (hx0 : x 0 ∈ sphere d) :
    ∀ t ∈ Icc (0 : ℝ) T, x t ∈ sphere d := by
  have hrad : ∀ t ∈ Icc (0 : ℝ) T,
      (⟪x t, tangentialProjector (x t) (g t)⟫ : ℝ) = (-⟪x t, g t⟫) * (‖x t‖ ^ 2 - 1) := by
    intro t _
    rw [inner_tangentialProjector_left]; ring
  have hnorm := norm_sq_eq_one_of_radial_tangent hx' hrad hK
    (norm_eq_one_of_mem_sphere hx0)
  intro t ht
  have : ‖x t‖ = 1 := hnorm t ht
  simpa [sphere, Metric.mem_sphere, dist_eq_norm] using this

end MeasureToMeasure
