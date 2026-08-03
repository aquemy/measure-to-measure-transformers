import MeasureToMeasure.Statements.Lemma54

/-!
# Non-vacuity witness for the lemma 5.4 finite-range core

FULL application of `lemma_5_4_of_finite_range` with its conclusion type ascribed, per the
witness rule: a partial application would silently stop guarding if a later PR made the
hypothesis bundle unsatisfiable (the F22 lesson). The data: `d = 3` (the smallest dimension the
repaired `lemma_5_4` admits), the Dirac at a basis sphere point, and the constant map to that
point, whose range is the singleton finite set. Every hypothesis of the core (probability,
sphere support, measurability, a.e. sphere values, the finite on-sphere range) is exercised
concretely.
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Foundations MeasureToMeasure.Statements
open MeasureToMeasure.Leaves

/-- A basis sphere point in `Eucl 3`. -/
noncomputable def e3 : Eucl 3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

theorem e3_mem_sphere : e3 ∈ MeasureToMeasure.sphere 3 := by
  have h : ‖e3‖ = 1 := by
    rw [e3]
    rw [show ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = ‖(1 : ℝ)‖ from
      PiLp.norm_single 2 _ 0 1]
    exact norm_one
  simpa [MeasureToMeasure.sphere, Metric.mem_sphere, dist_zero_right] using h

/-- **Full application of the finite-range core**, conclusion type ascribed. The flow conjunct
is the universal transport-map clause: one map for every sphere-supported probability measure. -/
example : ∃ (θ : AttnSchedule 3) (ψε : Eucl 3 → Eucl 3),
    AttnSchedule.durationSum θ = 1 ∧
    (∀ ν : Measure (Eucl 3), [IsProbabilityMeasure ν] →
      supportedIn ν (MeasureToMeasure.sphere 3) → attnMeasureFlow θ ν = ν.map ψε) ∧
    Measurable ψε ∧
    Integrable (fun x => ‖(fun _ : Eucl 3 => e3) x - ψε x‖ ^ 2) (Measure.dirac e3) ∧
    Real.sqrt (∫ x, ‖(fun _ : Eucl 3 => e3) x - ψε x‖ ^ 2 ∂(Measure.dirac e3)) ≤ 1 :=
  lemma_5_4_of_finite_range (by norm_num) (Measure.dirac e3) (fun _ => e3) 1 1
    one_pos one_pos (supportedIn_dirac e3_mem_sphere) measurable_const
    (ae_of_all _ fun _ => e3_mem_sphere)
    ⟨{e3}, fun z hz => by rw [Finset.mem_singleton.mp hz]; exact e3_mem_sphere,
      fun _ => Finset.mem_singleton_self e3⟩

end Regression.NonVacuity
