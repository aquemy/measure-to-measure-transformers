import Regression.NonVacuity.MidLevel
import MeasureToMeasure.Leaves.DisentangleInductionStepAsym

/-!
# Non-vacuity witness for `disentangle_insert_colinear_resolving_asym`

The FULL application demanded by the witness rule: every hypothesis of the static-cap re-based
resolving insertion step (`MeasureToMeasure/Leaves/DisentangleInductionStepAsym.lean`) is
instantiated concretely and the theorem is applied to completion with its conclusion type
ascribed. This is what the theorem's gated sibling (`disentangle_insert_colinear_resolving`,
threaded through the kernel-refuted `GenRestNearBall`, finding F22) never had and never could
have: its gate made it kernel-clean but invocable on NO input. The point of this file is that the
replacement's exclusive-point gate IS satisfiable, so the re-based step is genuinely consumable
by the induction over `N`.

**The data.** `d = 2`, `N = 2`, `k = 0`, empty prior schedule, carrier `U := orthant 2`, closed
bad set `K := {resQ}`. The family is two Diracs at distinct points of `sphere 2 ∩ orthant 2` from
the rational points `pt` of `Regression.NonVacuity.MidLevel`: index `0` (the member being placed,
the `K`-carried side) at `resQ = (4/5, 3/5)`, index `1` (the unplaced colinear partner `j`, the
exclusive-point side) at `resP = (3/5, 4/5)`. The exclusive point is `resP` itself:
`(Measure.dirac resP).support = {resP}` (`support_dirac_eq`) and `resP ∉ {resQ}` since the first
coordinates differ. At `N = 2` there are no bystanders (every index is `j` or `k`), so `hKbys`,
`hbys` and `hrest` are vacuous, and at `k = 0` there are no placed members, so `hsepU` is vacuous
and `DisentangledPrefix` reduces to sphere/orthant support of the two Diracs.
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Leaves MeasureToMeasure.Foundations
open MeasureToMeasure.Statements

/-- The exclusive-point side (index `1`, the unplaced colinear partner `j`). -/
noncomputable def resP : Eucl 2 := pt (3/5) (4/5)

/-- The `K`-carried side (index `0`, the member being placed). -/
noncomputable def resQ : Eucl 2 := pt (4/5) (3/5)

/-- The two-Dirac witness family: index `0` at `resQ`, index `1` at `resP`. -/
noncomputable def resFam : Fin 2 → Measure (Eucl 2) := fun i => Measure.dirac (![resQ, resP] i)

theorem resP_mem_sphere : resP ∈ MeasureToMeasure.sphere 2 := pt_mem_sphere (by norm_num)
theorem resQ_mem_sphere : resQ ∈ MeasureToMeasure.sphere 2 := pt_mem_sphere (by norm_num)
theorem resP_mem_orthant : resP ∈ orthant 2 := pt_mem_orthant (by norm_num) (by norm_num)
theorem resQ_mem_orthant : resQ ∈ orthant 2 := pt_mem_orthant (by norm_num) (by norm_num)
theorem resP_ne_resQ : resP ≠ resQ := pt_ne_of_fst (by norm_num)

/-- A Dirac at an orthant point is orthant-supported. -/
theorem dirac_supportedIn_orthant2 {x : Eucl 2} (hx : x ∈ orthant 2) :
    supportedIn (Measure.dirac x) (orthant 2) := by
  show Measure.dirac x (orthant 2)ᶜ = 0
  rw [Measure.dirac_apply' _ orthant_two_measurableSet.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx)]

theorem resFam_prob : ∀ i, IsProbabilityMeasure (resFam i) := fun i => by
  show IsProbabilityMeasure (Measure.dirac (![resQ, resP] i))
  infer_instance

theorem resFam_sphere : ∀ i, supportedIn (resFam i) (MeasureToMeasure.sphere 2) := by
  intro i
  fin_cases i
  · exact dirac_supportedIn_sphere resQ_mem_sphere
  · exact dirac_supportedIn_sphere resP_mem_sphere

theorem resFam_orthant : ∀ i, supportedIn (resFam i) (orthant 2) := by
  intro i
  fin_cases i
  · exact dirac_supportedIn_orthant2 resQ_mem_orthant
  · exact dirac_supportedIn_orthant2 resP_mem_orthant

/-- `DisentangledPrefix` at `k = 0`: nothing is placed, only sphere/orthant support. -/
theorem resFam_prefix :
    DisentangledPrefix 2 2 0 resFam [] Fin.elim0 Fin.elim0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [Foundations.attnMeasureFlow_nil]
    exact resFam_sphere i
  · intro i
    rw [Foundations.attnMeasureFlow_nil]
    exact resFam_orthant i
  · intro i hik
    exact absurd hik (Nat.not_lt_zero _)
  · intro a b _
    exact a.elim0
  · intro i hik
    exact absurd hik (Nat.not_lt_zero _)

/-- **Non-vacuity of `disentangle_insert_colinear_resolving_asym`**: the FULL application, with
the conclusion type ascribed. -/
theorem disentangleResolvingAsym_nonvacuity_witness : True := by
  have hk : (0 : ℕ) < 2 := by norm_num
  -- there are no bystanders at `N = 2`: every index is `1 = j` or `⟨0, hk⟩ = k`
  have hvac : ∀ i : Fin 2, i ≠ (1 : Fin 2) → i ≠ (⟨0, hk⟩ : Fin 2) → False := by
    intro i h1 h0
    fin_cases i
    · exact h0 rfl
    · exact h1 rfl
  have hjU : supportedIn (attnMeasureFlow [] (resFam 1)) (orthant 2) := by
    rw [Foundations.attnMeasureFlow_nil]
    exact resFam_orthant 1
  have hkU : supportedIn (attnMeasureFlow [] (resFam ⟨0, hk⟩)) (orthant 2) := by
    rw [Foundations.attnMeasureFlow_nil]
    exact resFam_orthant 0
  have hkK : (attnMeasureFlow [] (resFam ⟨0, hk⟩)).support ⊆ {resQ} := by
    rw [Foundations.attnMeasureFlow_nil]
    rw [show resFam ⟨0, hk⟩ = Measure.dirac resQ from rfl, support_dirac_eq]
  have hexcl : ∃ x0, x0 ∈ (attnMeasureFlow [] (resFam 1)).support ∧
      x0 ∉ ({resQ} : Set (Eucl 2)) := by
    refine ⟨resP, ?_, ?_⟩
    · rw [Foundations.attnMeasureFlow_nil,
        show resFam 1 = Measure.dirac resP from rfl, support_dirac_eq]
      exact Set.mem_singleton _
    · simpa using resP_ne_resQ
  have hrest : Pairwise fun i i' : Fin 2 => i ≠ (1 : Fin 2) → i ≠ (⟨0, hk⟩ : Fin 2) →
      i' ≠ (1 : Fin 2) → i' ≠ (⟨0, hk⟩ : Fin 2) →
      ∀ c : ℝ, MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam i))
        ≠ c • MeasureToMeasure.Leaves.barycenter (attnMeasureFlow [] (resFam i')) := by
    intro a b _ h1 h0 _ _
    exact (hvac a h1 h0).elim
  -- the FULL application, with the conclusion type ascribed
  have _h : ∃ ψ ψ' : AttnSchedule 2, AttnSchedule.durationSum (ψ ++ ψ') = 1 ∧
      Pairwise (fun i i' : Fin 2 => ∀ c : ℝ,
        MeasureToMeasure.Leaves.barycenter (attnMeasureFlow (([] : AttnSchedule 2) ++ ψ) (resFam i))
          ≠ c • MeasureToMeasure.Leaves.barycenter
            (attnMeasureFlow (([] : AttnSchedule 2) ++ ψ) (resFam i'))) ∧
      ∃ (ω : Eucl 2) (ε : ℝ), 0 < ε ∧
        DisentangledPrefix 2 2 (0 + 1) resFam (([] : AttnSchedule 2) ++ (ψ ++ ψ'))
          (Fin.snoc Fin.elim0 ω) (Fin.snoc Fin.elim0 ε) :=
    disentangle_insert_colinear_resolving_asym (le_refl 2) hk resFam resFam_prob resFam_sphere
      [] Fin.elim0 Fin.elim0 resFam_prefix 1 (by decide)
      (orthant 2) isOpen_orthant (subset_refl _) hjU hkU
      {resQ} isClosed_singleton
      (fun i h1 h0 => (hvac i h1 h0).elim) hkK hexcl
      (fun i h1 h0 => (hvac i h1 h0).elim) hrest
      (fun i => i.elim0) 1 one_pos
  trivial

end Regression.NonVacuity
