import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import MeasureToMeasure.Foundations.Sphere

/-!
# The logistic reaching estimate (Lemma B.2, eq. B.5-B.7)

The gated characteristic of Appendix B.2 obeys the scalar ODE `d/dt ⟪x,ω⟫ = g·(1 - ⟪x,ω⟫²)` (eq. B.5,
leaf L2 `gate_hasDerivAt_inner`), a logistic equation with a nonnegative gate `g`. On the active region
`g ≥ c₀ > 0`, so `u = ⟪x,ω⟫` is driven toward `1` (i.e. `x → ω`). This file proves the finite-time
reaching estimate the retention bound (B.7) rests on.

The key device is the **log-odds substitution** `w = log((1+u)/(1-u))` (`= 2·artanh u`): along the
flow its derivative is exactly `2g` (the `1-u²` factor cancels), so `w` grows at rate `≥ 2c₀` and hence
`w(T) ≥ w(0) + 2c₀T`. Since `s ↦ log((1+s)/(1-s))` is increasing on `(-1,1)`, this transfers to a lower
bound `u(T) ≥ b` for any target `b < 1` once `T` is large enough. The range `u ∈ (-1,1)` is supplied by
the geometry (strict Cauchy-Schwarz for distinct unit vectors), not the ODE, so it is a hypothesis here.
-/

namespace MeasureToMeasure

open Set

variable {u g : ℝ → ℝ}

/-- The **log-odds** `logOdds s = log((1+s)/(1-s))`, the integrating factor of the logistic ODE. -/
noncomputable def logOdds (s : ℝ) : ℝ := Real.log ((1 + s) / (1 - s))

/-- Derivative of the log-odds at an interior point: `logOdds' s = 2/(1 - s²)`. -/
theorem hasDerivAt_logOdds {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt logOdds (2 / (1 - s ^ 2)) s := by
  obtain ⟨hs1, hs2⟩ := hs
  have hp : (0 : ℝ) < 1 + s := by linarith
  have hm : (0 : ℝ) < 1 - s := by linarith
  have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 s := by simpa using (hasDerivAt_id s).const_add 1
  have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) s := by simpa using (hasDerivAt_id s).const_sub 1
  have hdiv : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y))
      ((1 * (1 - s) - (1 + s) * -1) / (1 - s) ^ 2) s := hnum.div hden hm.ne'
  have hpos : (0 : ℝ) < (1 + s) / (1 - s) := div_pos hp hm
  have hlog := hdiv.log hpos.ne'
  have hne2 : (1 : ℝ) - s ^ 2 ≠ 0 := by nlinarith
  show HasDerivAt (fun y => Real.log ((1 + y) / (1 - y))) (2 / (1 - s ^ 2)) s
  convert hlog using 1
  field_simp
  ring

/-- Along the logistic flow `u' = g·(1-u²)` with `u ∈ (-1,1)`, the log-odds derivative is `2g`. -/
theorem hasDerivAt_logOdds_comp {t : ℝ} (hu : HasDerivAt u (g t * (1 - (u t) ^ 2)) t)
    (hur : u t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s => logOdds (u s)) (2 * g t) t := by
  have hc := (hasDerivAt_logOdds hur).comp t hu
  have hne : (1 : ℝ) - (u t) ^ 2 ≠ 0 := by obtain ⟨h1, h2⟩ := hur; nlinarith
  have hval : 2 / (1 - (u t) ^ 2) * (g t * (1 - (u t) ^ 2)) = 2 * g t := by
    field_simp
  rwa [hval] at hc

/-- **Log-odds lower bound (eq. B.5-B.6).** Along the logistic flow with gate `g ≥ c₀` on `[0,T]` and
`u` staying in `(-1,1)`, the log-odds grows at rate at least `2c₀`:
`logOdds(u T) ≥ logOdds(u 0) + 2c₀·T`. -/
theorem logistic_flow_logOdds_le {T c₀ : ℝ} (hT : 0 ≤ T)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (g t * (1 - (u t) ^ 2)) t)
    (hur : ∀ t ∈ Icc (0 : ℝ) T, u t ∈ Ioo (-1 : ℝ) 1)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, c₀ ≤ g t) :
    logOdds (u 0) + 2 * c₀ * T ≤ logOdds (u T) := by
  set F : ℝ → ℝ := fun t => logOdds (u t) - 2 * c₀ * t with hF
  have hFderiv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt F (2 * g t - 2 * c₀) t := by
    intro t ht
    have h1 := hasDerivAt_logOdds_comp (hu t ht) (hur t ht)
    have h2 : HasDerivAt (fun t : ℝ => 2 * c₀ * t) (2 * c₀) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * c₀)
    exact h1.sub h2
  have hcont : ContinuousOn F (Icc 0 T) := fun t ht => (hFderiv t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Icc 0 T)) := by
    rw [interior_Icc]
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact (hFderiv t htc).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn F (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hcont hdiff
    intro t ht
    rw [interior_Icc] at ht
    have htc : t ∈ Icc (0 : ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [(hFderiv t htc).deriv]
    have := hg t htc; linarith
  have hle := hmono (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  have h0 : F 0 = logOdds (u 0) := by simp [hF]
  have hTe : F T = logOdds (u T) - 2 * c₀ * T := by simp [hF]
  rw [h0, hTe] at hle
  linarith

/-- **Reaching a target (eq. B.7).** Under the flow hypotheses, if `T` is large enough that the target
log-odds `logOdds b` is reached (`logOdds b ≤ logOdds(u 0) + 2c₀T`), then `u T ≥ b`. Combined with the
geometry `u = ⟪x,ω⟫` and `b = cos η₁`, this says the flow drives `x` into the cap `B(ω, η₁)`. -/
theorem logistic_flow_reach {T c₀ b : ℝ} (hT : 0 ≤ T)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (g t * (1 - (u t) ^ 2)) t)
    (hur : ∀ t ∈ Icc (0 : ℝ) T, u t ∈ Ioo (-1 : ℝ) 1)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, c₀ ≤ g t)
    (hb : b ∈ Ioo (-1 : ℝ) 1) (hreach : logOdds b ≤ logOdds (u 0) + 2 * c₀ * T) :
    b ≤ u T := by
  have hlog : logOdds b ≤ logOdds (u T) := le_trans hreach (logistic_flow_logOdds_le hT hu hur hg)
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hu1, hu2⟩ := hur T (right_mem_Icc.mpr hT)
  have hb2' : (0 : ℝ) < 1 - b := by linarith
  have hu2' : (0 : ℝ) < 1 - u T := by linarith
  have hpb : (0 : ℝ) < (1 + b) / (1 - b) := div_pos (by linarith) hb2'
  have hqu : (0 : ℝ) < (1 + u T) / (1 - u T) := div_pos (by linarith) hu2'
  have hle : (1 + b) / (1 - b) ≤ (1 + u T) / (1 - u T) := by
    have h := hlog; simp only [logOdds] at h
    calc (1 + b) / (1 - b) = Real.exp (Real.log ((1 + b) / (1 - b))) := (Real.exp_log hpb).symm
      _ ≤ Real.exp (Real.log ((1 + u T) / (1 - u T))) := Real.exp_le_exp.mpr h
      _ = (1 + u T) / (1 - u T) := Real.exp_log hqu
  have hcross := (div_le_div_iff₀ hb2' hu2').mp hle
  nlinarith

end MeasureToMeasure
