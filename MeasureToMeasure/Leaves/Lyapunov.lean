import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Leaf L5: the Lyapunov function of Example 6.1

On the circle (`d = 2`) the clustering dynamics reduce, in the angle variable, to
`θ'(t) = -α sin θ(t)` with `α ≥ 0`. The paper uses `E(θ) = 1 - cos θ` as a Lyapunov function and
computes `Ė = sin θ · θ' = -α sin² θ ≤ 0`, so `E` is nonincreasing along the flow and the particle
converges to the cluster direction.

We kernel-check both halves: the derivative identity along the flow, and its sign.
-/

namespace MeasureToMeasure.Leaves

/-- L5 (derivative of the Lyapunov function along the flow): if `θ` solves `θ' = -α sin θ` at `t`,
then `E(s) = 1 - cos θ(s)` has derivative `-α sin²(θ t)` at `t`. -/
theorem lyapunov_hasDerivAt (α : ℝ) (θ : ℝ → ℝ) (t θ' : ℝ)
    (hθ : HasDerivAt θ θ' t) (hode : θ' = -α * Real.sin (θ t)) :
    HasDerivAt (fun s => 1 - Real.cos (θ s)) (-α * Real.sin (θ t) ^ 2) t := by
  have hcos : HasDerivAt (fun s => Real.cos (θ s)) (-Real.sin (θ t) * θ') t :=
    (Real.hasDerivAt_cos (θ t)).comp t hθ
  have h : HasDerivAt (fun s => 1 - Real.cos (θ s)) (0 - (-Real.sin (θ t) * θ')) t :=
    (hasDerivAt_const t 1).sub hcos
  convert h using 1
  rw [hode]; ring

/-- L5 (sign): the Lyapunov derivative is nonpositive when `α ≥ 0`. -/
theorem lyapunov_deriv_nonpos {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    -α * Real.sin s ^ 2 ≤ 0 := by
  have : 0 ≤ α * Real.sin s ^ 2 := mul_nonneg hα (sq_nonneg _)
  linarith

end MeasureToMeasure.Leaves
