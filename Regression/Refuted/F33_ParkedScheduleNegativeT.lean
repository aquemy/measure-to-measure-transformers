import Regression.OldStatements

/-!
# F33: `exists_parked_schedule` is inconsistent without horizon positivity (negative horizon)

The parking axiom `exists_parked_schedule` (one shared schedule steers a disjointly supported
family, each member within `ε` of its target) was stated without the paper's horizon positivity.
That shape is not merely too strong; it is INCONSISTENT: at `N = 0` the disjoint-supports and
per-member steering hypotheses are both vacuous (every `Fin 0`-indexed obligation is
`Fin.elim0`), yet the conclusion still demands a schedule `Θ` with `durationSum Θ = T` for the
ARBITRARY real `T`. Instantiating `d = 3`, `N = 0`, `T = -1` forces a schedule of total duration
`-1`, contradicting the kernel-checked `AttnSchedule.durationSum_nonneg` (durations are
nonnegative by the `AttnParams` structure itself). Unlike the F11/F12/F31 class (false axioms
refuted by a crafted witness), this one needs no witness data at all: the empty family plus a
negative horizon is a two-line `linarith` disproof.

Repaired by adding `hT : 0 < T` (finding F33), the paper's OWN quantifier: Proposition 2.2
states "Then for any 𝑇 > 0 and 𝜀 > 0 there exist piecewise constant (W, U, 𝑏) : [0, 𝑇] → ..."
(pp. 11-12, arXiv:2411.04551v3); the hypothesis was dropped in error at admission. This file
kernel-checks `Regression.OldParkedScheduleNoHorizonSig → False`; the repaired axiom carries
`0 < T`, so it cannot reproduce this signature (must-fail adapter:
`Refutations/F33_exists_parked_schedule_negative_horizon.lean`). The `N = 0, T > 0` corner of
the repaired axiom is satisfiable, not vacuous: any single positive-duration block gives
`durationSum = T` with the member clauses vacuous.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureToMeasure MeasureToMeasure.Foundations

/-- The pre-F33 (horizon-free) parking schema yields `False`: instantiate the empty family at
`d = 3` with horizon `T = -1`; the produced schedule's total duration would be `-1`,
contradicting `durationSum_nonneg`. -/
theorem oldParkedScheduleNoHorizon_false (h : Regression.OldParkedScheduleNoHorizonSig) :
    False := by
  obtain ⟨Θ, hdur⟩ :=
    h (d := 3) (N := 0) (le_refl 3) Fin.elim0 Fin.elim0 (-1) 0 Fin.elim0
      ⟨Fin.elim0, fun i => i.elim0, by intro i; exact i.elim0⟩ (fun i => i.elim0)
  have hnn := AttnSchedule.durationSum_nonneg Θ
  linarith

end Regression.Refuted
