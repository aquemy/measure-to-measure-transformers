import MeasureToMeasure.Foundations.GatedBlock

/-!
# Elementary gathering convergence, no Hartman-Grobman needed (Proposition 4.2, Step 2)

The paper's Proposition 4.2 proof (App. p.21, eq. (4.6)) invokes the Hartman-Grobman theorem for an
*exponential-rate* estimate of a gated block's trajectory settling near its drift target. This leaf
shows the theorem is not actually needed for what the construction consumes downstream (eq. (4.7),
a finite-time entry into a target cap, not the rate itself): the gate factor is always nonnegative
and `(1-⟪x,ω⟫²) ≥ 0` always on the sphere, so `⟪x(t),ω⟫` is non-decreasing under a `gatedField`
flow (`inner_gatedField_omega_nonneg`) -- combined with a uniform lower bound on the derivative
whenever the trajectory has not yet entered the target cap, a direct integration argument (not
LaSalle, not Hartman-Grobman) gives finite-time entry.

**The starting-bound subtlety.** The paper's construction picks the drift target
`ω₊ := cos(π/8)•ω + sin(π/8)•γ` from anchors `γ ⊥ ω` (both unit) set up in Step 1. For the uniform
derivative bound to hold throughout, `⟪x(t),ω₊⟫` must stay bounded away from `-1` (else
`1-⟪x(t),ω₊⟫²` degenerates). `inner_omegaPlus_ge` shows this is automatic and needs no extra
non-degeneracy hypothesis: for any `x0` on the sphere with `⟪γ,x0⟫ ≥ 0` (the gate's own "on"
condition), decomposing `⟪x0,ω₊⟫ = cos(π/8)⟪x0,ω⟫ + sin(π/8)⟪x0,γ⟫` and bounding each term
(`⟪x0,ω⟫ ≥ -1` by Cauchy-Schwarz, `⟪x0,γ⟫ ≥ 0` by hypothesis, both coefficients nonnegative) gives
`⟪x0,ω₊⟫ ≥ -cos(π/8)` unconditionally -- a clean, `ε`-independent bound, not merely "generically
true". Since `cos(π/8) < 1`, this is bounded well away from the degenerate `-1` case.

M3b/mid-level staging: consumed when `prop_4_2` is discharged; see `Statements/MidLevel.lean`. Note:
`prop_4_2`'s OWN discharge is currently blocked on a separate, harder issue (Step 2's
separating-direction construction has a verified counterexample for certain colinear configurations
of the inactive points) -- this leaf is banked independently as a genuinely reusable fact regardless
of how that issue resolves.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- **The gated field never decreases `⟪x,ω⟫`** (on the sphere): the gate factor and the
projector's self-inner-product `1-⟪x,ω⟫²` are both nonnegative. -/
theorem inner_gatedField_omega_nonneg {z ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ} (x : Eucl d)
    (hx : x ∈ sphere d) :
    0 ≤ ⟪gatedField z ω cosR x, ω⟫ := by
  rw [gatedField, real_inner_smul_left, tangentialProjector_apply, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hω]
  have h1 : ⟪x, ω⟫ * ⟪x, ω⟫ ≤ 1 := by
    have hcs := abs_real_inner_le_norm x ω
    rw [norm_eq_one_of_mem_sphere hx, hω, mul_one] at hcs
    rw [abs_le] at hcs
    nlinarith [hcs.1, hcs.2]
  have hgate : 0 ≤ gateFactor z cosR x := mul_nonneg (normCutoff_nonneg x) (reluGate_nonneg z cosR x)
  nlinarith [hgate]

/-- **The starting-bound is automatic, no extra hypothesis needed.** For `x0` on the sphere with
`⟪γ,x0⟫ ≥ 0` (the gate's own "on" condition) and orthonormal anchors `γ, ω`, the drift target
`ω₊ := cos(π/8)•ω + sin(π/8)•γ` satisfies `⟪x0,ω₊⟫ ≥ -cos(π/8)` -- bounded well away from the
degenerate antipodal case `-1`, since `cos(π/8) < 1`. -/
theorem inner_omegaPlus_ge {γ ω x0 : Eucl d} (hω : ‖ω‖ = 1) (hx0 : x0 ∈ sphere d)
    (hγx0 : 0 ≤ ⟪γ, x0⟫) :
    -Real.cos (Real.pi / 8) ≤ ⟪x0, Real.cos (Real.pi / 8) • ω + Real.sin (Real.pi / 8) • γ⟫ := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hωx0 : -1 ≤ ⟪x0, ω⟫ := by
    have hcs := abs_real_inner_le_norm x0 ω
    rw [norm_eq_one_of_mem_sphere hx0, hω, mul_one, abs_le] at hcs
    exact hcs.1
  have hγx0' : 0 ≤ ⟪x0, γ⟫ := by rwa [real_inner_comm] at hγx0
  have hs8 : 0 ≤ Real.sin (Real.pi / 8) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hc8 : 0 ≤ Real.cos (Real.pi / 8) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  nlinarith [mul_le_mul_of_nonneg_left hωx0 hc8, mul_nonneg hs8 hγx0']

end MeasureToMeasure.Leaves
