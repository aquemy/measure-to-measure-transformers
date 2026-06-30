import MeasureToMeasure.Leaves.GateODE

/-!
# Leaf L6: the barycenter ODE (eq. B.9)

In Lemma 3.3 the disentangling field is `P_x^⊥(⟪𝔼_μ[x], α⟫ • α)`, and the barycenter component
`⟪x(t), α⟫` evolves (eq. B.9) as

    d/dt ⟪x(t), α⟫ = c · (1 - ⟪x(t), α⟫²),     c = ⟪𝔼_μ[x], α⟫.

Treating `c` as a constant of fixed sign (the paper shows it is sign-preserved), this is the same
logistic identity as the gate ODE. We record the derivative (an instance of `gate_hasDerivAt_inner`)
and the strict-increase sign that drives `⟪x, α⟫ → 1`, i.e. `x → α`.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- L6 (derivative, eq. B.9): along `x'(t) = P_{x(t)}^⊥ (c • α)` with `α` a unit vector, the
component `⟪x(t), α⟫` evolves as `c(1 - ⟪x(t), α⟫²)`. -/
theorem barycenter_hasDerivAt_inner {x : ℝ → Eucl d} {α : Eucl d} {t : ℝ} {x' : Eucl d}
    (hx : HasDerivAt x x' t) (hxs : x t ∈ sphere d) (hα : α ∈ sphere d) (c : ℝ)
    (hode : x' = tangentialProjector (x t) (c • α)) :
    HasDerivAt (fun s => (⟪x s, α⟫ : ℝ)) (c * (1 - ⟪x t, α⟫ ^ 2)) t :=
  gate_hasDerivAt_inner hx hxs hα c hode

/-- L6 (sign / strict increase): when the barycenter coefficient `c` is positive and the component
is strictly inside `(-1, 1)`, the component strictly increases. This is the dissipation that pushes
`⟪x, α⟫` toward `1`. -/
theorem barycenter_deriv_pos {c y : ℝ} (hc : 0 < c) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < c * (1 - y ^ 2) := by
  obtain ⟨h1, h2⟩ := hy
  have hy2 : y ^ 2 < 1 := by nlinarith
  have : 0 < 1 - y ^ 2 := by linarith
  positivity

end MeasureToMeasure.Leaves
