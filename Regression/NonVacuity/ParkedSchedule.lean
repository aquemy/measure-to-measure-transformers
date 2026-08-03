import MeasureToMeasure.Statements.ParkedSchedule
import Regression.NonVacuity.MidLevel

/-!
# Non-vacuity witness for the map-targets parked schedule

FULL application of `exists_parked_schedule_of_map_targets` with its conclusion type ascribed,
per the witness rule: a partial application would silently stop guarding if a later PR made the
hypothesis bundle unsatisfiable (the F22 lesson). The data mirror the `exists_parked_schedule`
witness in `Regression/NonVacuity/MidLevel.lean`: `d = 3` (the smallest dimension the statement
admits), the singleton family `N = 1` of the Dirac at a basis sphere point, the identity map as
the per-member target map (`S = id`, so the target is the member itself), horizon `T = 1`,
tolerance `ε = 1`. Every hypothesis is exercised concretely: probability and sphere support of
the Dirac, `DisjointSupports` via the singleton carrier, measurability of `id`, and a.e.
sphere-valuedness from the Dirac's own support. This guards the intended application shape
BEFORE any consumer rewires onto the companion (the kernel-clean-not-applicable trap).
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)

/-- Full application of `exists_parked_schedule_of_map_targets`, conclusion type ascribed:
the singleton Dirac family with identity target maps on `𝕊² ⊂ ℝ³`. -/
example : True := by
  have hdisj : DisjointSupports (fun _ : Fin 1 => Measure.dirac (unitE 3 0)) := by
    refine ⟨fun _ => {unitE 3 0}, fun i => ?_,
      fun i j hij => absurd (Subsingleton.elim i j) hij⟩
    show Measure.dirac (unitE 3 0) ({unitE 3 0} : Set (Eucl 3))ᶜ = 0
    rw [Measure.dirac_apply' _ (measurableSet_singleton _).compl,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (Set.mem_singleton (unitE 3 0)))]
  have hSs : ∀ i : Fin 1, ∀ᵐ y ∂(fun _ : Fin 1 => Measure.dirac (unitE 3 0)) i,
      (fun _ : Fin 1 => (id : Eucl 3 → Eucl 3)) i y ∈ MeasureToMeasure.sphere 3 := fun _ =>
    mem_ae_iff.mpr (dirac_supportedIn_sphere (unitE_mem_sphere 3 0))
  have _h : ∃ Θ : AttnSchedule 3, AttnSchedule.durationSum Θ = 1 ∧
      ∀ i : Fin 1, Axioms.W2
        (attnMeasureFlow Θ ((fun _ : Fin 1 => Measure.dirac (unitE 3 0)) i))
        (((fun _ : Fin 1 => Measure.dirac (unitE 3 0)) i).map
          ((fun _ : Fin 1 => (id : Eucl 3 → Eucl 3)) i)) ≤ 1 :=
    exists_parked_schedule_of_map_targets (le_refl 3)
      (fun _ : Fin 1 => Measure.dirac (unitE 3 0))
      (fun _ : Fin 1 => (id : Eucl 3 → Eucl 3)) 1 1 one_pos one_pos
      (fun _ => inferInstance)
      (fun _ => dirac_supportedIn_sphere (unitE_mem_sphere 3 0))
      hdisj (fun _ => measurable_id) hSs
  trivial

end Regression.NonVacuity
