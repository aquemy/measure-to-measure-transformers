import Regression.NonVacuity.DisentangleResolvingAsym

/-!
# Non-vacuity witness for `disentangle_insert_noncolinear_avoiding`

The FULL application demanded by the witness rule: every hypothesis of the avoiding non-colinear
insertion step (`MeasureToMeasure/Leaves/DisentangleInductionStepAsym.lean`) is instantiated
concretely and the theorem is applied to completion with its conclusion type ascribed. The step
guards the induction over `N` (its two avoidance conjuncts are the geometric invariants the
assembly consumes), so a partial application would not do: it would silently stop guarding if a
later PR added an unsatisfiable hypothesis (the exact hole that hid finding F22).

**The data.** Reuses `Regression.NonVacuity.DisentangleResolvingAsym`'s two-Dirac family `resFam`
(`d = 2`, `N = 2`, `k = 0`, empty prior schedule): index `0` (the member being placed) at
`resQ = (4/5, 3/5)`, index `1` at `resP = (3/5, 4/5)`. Unlike the resolving witness, here the
family must be PAIRWISE NON-COLINEAR (`hnoncol` is the non-colinear branch's blanket hypothesis):
`resQ = c • resP` would force `c = 4/3` from the first coordinate and `c = 3/4` from the second,
and symmetrically for the other direction, so both fail for every `c`. The avoided-point family is
the singleton `pts = ![resP]`, distinct from member `0`'s barycenter direction
`‖resQ‖⁻¹ • resQ = resQ` (unit norm) since the first coordinates differ, exercising the new
`hpts` hypothesis non-vacuously (`m = 1`, not the degenerate `m = 0`).
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Leaves MeasureToMeasure.Foundations
open MeasureToMeasure.Statements

/-- The barycenter of a Dirac is its atom. -/
theorem barycenter_dirac (x : Eucl 2) :
    MeasureToMeasure.Leaves.barycenter (Measure.dirac x) = x := by
  rw [MeasureToMeasure.Leaves.barycenter, integral_dirac]

/-- `resQ` is a unit vector (it lies on the unit sphere). -/
theorem resQ_norm : ‖resQ‖ = 1 := by
  have h := resQ_mem_sphere
  rwa [MeasureToMeasure.sphere, Metric.mem_sphere, dist_zero_right] at h

/-- `resQ` is no scalar multiple of `resP`: coordinates force `c = 4/3` and `c = 3/4` at once. -/
theorem resQ_ne_smul_resP : ∀ c : ℝ, resQ ≠ c • resP := by
  intro c hEq
  have h0 : (4/5 : ℝ) = c * (3/5) := by
    have h := congrArg (fun v : Eucl 2 => v 0) hEq
    simpa [resQ, resP, pt, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h
  have h1 : (3/5 : ℝ) = c * (4/5) := by
    have h := congrArg (fun v : Eucl 2 => v 1) hEq
    simpa [resQ, resP, pt, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h
  linarith

/-- The other direction, by the symmetric coordinate computation. -/
theorem resP_ne_smul_resQ : ∀ c : ℝ, resP ≠ c • resQ := by
  intro c hEq
  have h0 : (3/5 : ℝ) = c * (4/5) := by
    have h := congrArg (fun v : Eucl 2 => v 0) hEq
    simpa [resQ, resP, pt, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h
  have h1 : (4/5 : ℝ) = c * (3/5) := by
    have h := congrArg (fun v : Eucl 2 => v 1) hEq
    simpa [resQ, resP, pt, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h
  linarith

/-- The two-Dirac family is pairwise non-colinear after the empty schedule. -/
theorem resFam_noncolinear : Pairwise (fun i j : Fin 2 => ∀ c : ℝ,
    MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam i))
      ≠ c • MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam j))) := by
  have h01 : ∀ c : ℝ,
      MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam 0))
        ≠ c • MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam 1)) := by
    intro c
    rw [Foundations.attnMeasureFlow_nil, Foundations.attnMeasureFlow_nil,
      show resFam 0 = Measure.dirac resQ from rfl, show resFam 1 = Measure.dirac resP from rfl,
      barycenter_dirac, barycenter_dirac]
    exact resQ_ne_smul_resP c
  have h10 : ∀ c : ℝ,
      MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam 1))
        ≠ c • MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam 0)) := by
    intro c
    rw [Foundations.attnMeasureFlow_nil, Foundations.attnMeasureFlow_nil,
      show resFam 0 = Measure.dirac resQ from rfl, show resFam 1 = Measure.dirac resP from rfl,
      barycenter_dirac, barycenter_dirac]
    exact resP_ne_smul_resQ c
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact h01
  · exact h10
  · exact absurd rfl hab

/-- **Non-vacuity of `disentangle_insert_noncolinear_avoiding`**: the FULL application, with the
conclusion type ascribed and a NON-degenerate avoided-point family (`m = 1`). -/
theorem disentangleAvoidingInsert_nonvacuity_witness : True := by
  have hk : (0 : ℕ) < 2 := by norm_num
  have hpts : ∀ l : Fin 1, (![resP] : Fin 1 → Eucl 2) l ≠
      ‖MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam ⟨0, hk⟩))‖⁻¹ •
        MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam ⟨0, hk⟩)) := by
    intro l
    rw [Foundations.attnMeasureFlow_nil, show resFam ⟨0, hk⟩ = Measure.dirac resQ from rfl,
      barycenter_dirac, resQ_norm]
    fin_cases l
    simpa using resP_ne_resQ
  -- the FULL application, with the conclusion type ascribed
  have _h : ∃ θ' : AttnSchedule 2, AttnSchedule.durationSum θ' = 1 ∧
      ∃ (ω : Eucl 2) (ε : ℝ), 0 < ε ∧ ‖ω‖ = 1 ∧
        (∀ l : Fin 1, (![resP] : Fin 1 → Eucl 2) l ∉ Metric.closedBall ω ε) ∧
        (∀ i : Fin 2, i ≠ (⟨0, hk⟩ : Fin 2) → ∀ c : ℝ,
          c • MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam i))
            ∉ Metric.closedBall ω ε) ∧
        (∀ i : Fin 2, i ≠ (⟨0, hk⟩ : Fin 2) →
          attnMeasureFlow (([] : AttnSchedule 2) ++ θ') (resFam i)
            = attnMeasureFlow [] (resFam i)) ∧
        DisentangledPrefix 2 2 (0 + 1) resFam (([] : AttnSchedule 2) ++ θ')
          (Fin.snoc Fin.elim0 ω) (Fin.snoc Fin.elim0 ε) :=
    disentangle_insert_noncolinear_avoiding hk resFam resFam_prob resFam_sphere
      [] Fin.elim0 Fin.elim0 resFam_prefix resFam_noncolinear (fun i => i.elim0)
      (![resP]) hpts 1 one_pos
  trivial

end Regression.NonVacuity
