import MeasureToMeasure.Leaves.MergeTolerantRelocation
import Regression.NonVacuity.MidLevel

/-!
# Non-vacuity witnesses for the G7 merge-tolerant relocation leaves

FULL applications, per the witness rule: every hypothesis of
`exists_merge_tolerant_relocation` (the corridor-gated Phase-2 engine) and of
`exists_landing_pole_avoiding` (the landing-pole geometry) is instantiated concretely and each
theorem is applied to completion with its conclusion type ascribed. The engine's corridor bundle
(`hcap`/`hab`/`hb2`/`hgate_src`/`hgate_land`/`hland`) will gate the G8 assembly, so a partial
application would not do: it would silently stop guarding if a later PR made the bundle
unsatisfiable (the F22 lesson).

**The data.** Two antipodal source balls on the circle (`d = 2`, `N = 2`): `relocC 0 = (1, 0)`
and `relocC 1 = (-1, 0)`, staging radius `ρ = 1/8`, one trivial hop each (`Mc = 1`, chain
constant at the source, capture `a = 1/8`, gate `b = 1/4`), targets equal to the sources with
`δ = 1/2`. Every avoidance pair is exercised non-vacuously: `dist (relocC 0) (relocC 1) = 2`
clears the gate-vs-ball budget `1/4 + 1/8`. For the landing pole, the avoided family is a single
ball of radius `1/16` sitting exactly ON the target `(1, 0)` with `δ = 1`: the pole must dodge
the ball covering the target itself, the interesting merge case. -/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Foundations MeasureToMeasure.Leaves
open MeasureToMeasure.Statements

/-- The two antipodal source centres `(1, 0)` and `(-1, 0)`. -/
noncomputable def relocC : Fin 2 → Eucl 2 := ![pt 1 0, pt (-1) 0]

/-- One hop per ball. -/
def relocMc : Fin 2 → ℕ := fun _ => 1

/-- Constant hop chains: each ball relocates in place. -/
noncomputable def relocW : ∀ i : Fin 2, Fin (relocMc i + 1) → Eucl 2 := fun i _ => relocC i

/-- Capture radii. -/
noncomputable def relocA : ∀ i : Fin 2, Fin (relocMc i) → ℝ := fun _ _ => 1/8

/-- Gate radii. -/
noncomputable def relocB : ∀ i : Fin 2, Fin (relocMc i) → ℝ := fun _ _ => 1/4

/-- Both centres are on the circle. -/
theorem relocC_sphere : ∀ i, relocC i ∈ MeasureToMeasure.sphere 2 := by
  intro i
  fin_cases i
  · exact pt_mem_sphere (by norm_num)
  · exact pt_mem_sphere (by norm_num)

/-- The two centres are antipodal: distance exactly `2`. -/
theorem relocC_dist : dist (relocC 0) (relocC 1) = 2 := by
  simp only [relocC, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, pt_apply_zero, pt_apply_one, dist_self]
  rw [show dist (1 : ℝ) (-1) = 2 by rw [Real.dist_eq]; norm_num]
  rw [show (2 : ℝ) ^ 2 + 0 ^ 2 = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem relocC_dist' : dist (relocC 1) (relocC 0) = 2 := by
  rw [dist_comm]; exact relocC_dist

/-- Gates of the earlier chain clear the later source ball. -/
theorem reloc_gate_src : ∀ i j : Fin 2, i < j → ∀ t : Fin (relocMc i),
    Disjoint (Metric.ball (relocW i t.succ) (relocB i t))
      (Metric.ball (relocW j 0) (1/8 : ℝ)) := by
  intro i j hij t
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · refine Metric.ball_disjoint_ball ?_
    show (1:ℝ)/4 + 1/8 ≤ dist (relocC 0) (relocC 1)
    rw [relocC_dist]; norm_num
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

/-- Gates of the later chain clear the earlier landing ball. -/
theorem reloc_gate_land : ∀ i j : Fin 2, j < i → ∀ t : Fin (relocMc i),
    Disjoint (Metric.ball (relocW i t.succ) (relocB i t))
      (Metric.ball (relocW j (Fin.last (relocMc j))) (1/8 : ℝ)) := by
  intro i j hji t
  fin_cases i <;> fin_cases j
  · exact absurd hji (by decide)
  · exact absurd hji (by decide)
  · refine Metric.ball_disjoint_ball ?_
    show (1:ℝ)/4 + 1/8 ≤ dist (relocC 1) (relocC 0)
    rw [relocC_dist']; norm_num
  · exact absurd hji (by decide)

/-- **Full application of the relocation engine**, conclusion type ascribed. -/
example : ∃ θ : AttnSchedule 2, AttnSchedule.durationSum θ = (∑ i, (relocMc i : ℝ)) * 1 ∧
    (∀ j, ∀ ν : Measure (Eucl 2), [IsProbabilityMeasure ν] →
      supportedIn ν (MeasureToMeasure.sphere 2) →
      supportedIn ν (Metric.ball (relocW j 0) (1/8 : ℝ)) →
      supportedIn (attnMeasureFlow θ ν) (Metric.ball (relocC j) (1/2 : ℝ))) ∧
    (∀ F : Set (Eucl 2),
      (∀ i, ∀ t : Fin (relocMc i), Disjoint F (Metric.ball (relocW i t.succ) (relocB i t))) →
      ∀ ν : Measure (Eucl 2), [IsProbabilityMeasure ν] →
      supportedIn ν (MeasureToMeasure.sphere 2) →
      supportedIn ν F → attnMeasureFlow θ ν = ν) ∧
    (∃ f : Eucl 2 → Eucl 2, Measurable f ∧
      Set.MapsTo f (MeasureToMeasure.sphere 2) (MeasureToMeasure.sphere 2) ∧
      ∀ ν : Measure (Eucl 2), [IsProbabilityMeasure ν] →
        supportedIn ν (MeasureToMeasure.sphere 2) → attnMeasureFlow θ ν = ν.map f) :=
  exists_merge_tolerant_relocation relocMc relocW (fun i _ => relocC_sphere i)
    (by norm_num : (0:ℝ) < 1/8) relocA relocB
    (fun i t => by
      show dist (relocC i) (relocC i) + 1/8 ≤ relocA i t
      rw [dist_self, relocA]
      norm_num)
    (fun i t => by rw [relocA, relocB]; norm_num)
    (fun i t => by rw [relocB]; norm_num)
    reloc_gate_src reloc_gate_land relocC
    (fun j => Metric.ball_subset_ball (by norm_num))
    (by norm_num : (0:ℝ) < 1)

/-- **Full application of the landing-pole geometry**, conclusion type ascribed: the single
avoided ball sits exactly on the target, the interesting merge case. -/
example : ∃ (z' : Eucl 2) (r' : ℝ), z' ∈ MeasureToMeasure.sphere 2 ∧ 0 < r' ∧
    Metric.closedBall z' r' ⊆ Metric.ball (pt 1 0) ((1 : ℝ) / 2) ∧
    ∀ i : Fin 1, Disjoint (Metric.closedBall z' r')
      (Metric.closedBall ((fun _ => pt 1 0) i) ((fun _ => (1/16 : ℝ)) i)) :=
  exists_landing_pole_avoiding (by norm_num) (pt_mem_sphere (by norm_num))
    (by norm_num) (by norm_num) (fun _ => pt 1 0) (fun _ => 1/16)
    (fun i => by norm_num) (fun i j hij => absurd (Subsingleton.elim i j) hij)

end Regression.NonVacuity
