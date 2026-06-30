import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Leaf L9: the ball-chain induction of Lemma B.1

Lemma B.1 transfers mass through a chain of `K` overlapping balls, each step (Lemma B.2) retaining
at least a factor `(1 - ε)` of the mass. Stripped of its measure-theoretic content, the bookkeeping
is a clean induction: if a nonnegative sequence `a` starts above `m` and satisfies
`a (k+1) ≥ (1 - ε) · a k`, then `a K ≥ (1 - ε)^K · m`. This is kernel-checked here and is the
arithmetic core the paper's backward induction relies on.
-/

namespace MeasureToMeasure.Leaves

/-- L9: geometric retention through a chain. With retention factor `1 - ε ∈ [0, 1]` per step and
initial mass at least `m ≥ 0`, after `K` steps at least `(1 - ε)^K · m` remains. -/
theorem ball_chain_geom {ε : ℝ} (hε1 : ε ≤ 1) (a : ℕ → ℝ) {m : ℝ}
    (h0 : m ≤ a 0) (hstep : ∀ k, (1 - ε) * a k ≤ a (k + 1)) :
    ∀ K : ℕ, (1 - ε) ^ K * m ≤ a K := by
  have h1ε : (0 : ℝ) ≤ 1 - ε := by linarith
  intro K
  induction K with
  | zero => simpa using h0
  | succ n ih =>
    calc (1 - ε) ^ (n + 1) * m
        = (1 - ε) * ((1 - ε) ^ n * m) := by ring
      _ ≤ (1 - ε) * a n := by exact mul_le_mul_of_nonneg_left ih h1ε
      _ ≤ a (n + 1) := hstep n

end MeasureToMeasure.Leaves
