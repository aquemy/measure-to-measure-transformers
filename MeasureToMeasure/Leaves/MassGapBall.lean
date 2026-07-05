import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import MeasureToMeasure.Foundations.Sphere

/-!
# Leaf L3-ball (Lemma 3.4 Part 1): distinct measures differ on some closed ball

The App. B.3 Part 1 construction opens with "there exists an open ball `B` with `μ₀(B) ≠ ν₀(B)`". An
*open set* with different mass is immediate from `μ ≠ ν` (regularity), but the perceptron gate acts on
a **cap = ball**, so we need a *ball* specifically — which is the measure-differentiation theorem.

We prove the closed-ball form via Besicovitch differentiation. The trick that keeps it to one clean
argument (no Lebesgue-decomposition bookkeeping) is to differentiate against the **common dominating
measure `ρ = μ + ν`**: both `μ ≪ ρ` and `ν ≪ ρ`, so each equals `ρ.withDensity (·.rnDeriv ρ)` with no
singular part. If `μ` and `ν` agreed on *every* closed ball, the ratios
`μ(closedBall x r)/ρ(closedBall x r)` and `ν(closedBall x r)/ρ(closedBall x r)` would be identical for
every `x, r`, so `Besicovitch.ae_tendsto_rnDeriv` forces `μ.rnDeriv ρ = ν.rnDeriv ρ` `ρ`-a.e., whence
`μ = ν`. `Eucl d = EuclideanSpace ℝ (Fin d)` is finite-dimensional, so it carries
`HasBesicovitchCovering` — we differentiate in the ambient space, not the sphere subspace.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Metric Filter

variable {d : ℕ}

/-- **L3-ball.** Two distinct finite Borel measures on `Eucl d` differ on some closed ball. The
contrapositive of "measures agreeing on all closed balls are equal", proved by Besicovitch
differentiation against the common dominating measure `μ + ν`. -/
theorem exists_closedBall_measure_ne {μ ν : Measure (Eucl d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hne : μ ≠ ν) :
    ∃ (x : Eucl d) (r : ℝ), μ (closedBall x r) ≠ ν (closedBall x r) := by
  by_contra h
  simp only [ne_eq, not_exists, not_not] at h
  -- `h : ∀ x r, μ (closedBall x r) = ν (closedBall x r)`
  refine hne ?_
  set ρ : Measure (Eucl d) := μ + ν with hρ
  have hμρ : μ ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hνρ : ν ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hμ := Besicovitch.ae_tendsto_rnDeriv μ ρ
  have hν := Besicovitch.ae_tendsto_rnDeriv ν ρ
  have hderiv : μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ := by
    filter_upwards [hμ, hν] with x hx hx'
    have hcongr : (fun r => μ (closedBall x r) / ρ (closedBall x r))
        = (fun r => ν (closedBall x r) / ρ (closedBall x r)) := by
      funext r; rw [h x r]
    rw [hcongr] at hx
    exact tendsto_nhds_unique hx hx'
  calc μ = ρ.withDensity (μ.rnDeriv ρ) := (Measure.withDensity_rnDeriv_eq μ ρ hμρ).symm
    _ = ρ.withDensity (ν.rnDeriv ρ) := withDensity_congr_ae hderiv
    _ = ν := Measure.withDensity_rnDeriv_eq ν ρ hνρ

end MeasureToMeasure.Leaves
