import MeasureToMeasure.Leaves.CollapseColinearityAvoidance
import MeasureToMeasure.Leaves.PoleGeometry
import MeasureToMeasure.Leaves.GenRestNearBall
import MeasureToMeasure.Leaves.DisentangleInductionStep
import Regression.NonVacuity.MidLevel

/-!
# `hgenRest` is unconditionally unsatisfiable (`phase4_final_pole_pigeonhole_assembly`, G1)

`barycenter_nonColinear_of_massGapCollapse_meanField_callerCap` (PR #273,
`MeasureToMeasure/Leaves/Lemma34Part1MeanField.lean`) and its non-`callerCap` sibling
`barycenter_nonColinear_of_massGapCollapse_meanField` both carry a hypothesis `hgenRest`: for
**every** unit `w` orthogonal to `z`, the rest-component `Leaves.restComp z w q` (`q` the leftover
-mass integral of `ν` outside the cap) is nonzero, plus a non-parallelism clause. Both theorems are
kernel-clean, but this file records the hand-verified finding that `hgenRest`'s core clause is
**unconditionally false** for every unit `z` and every `q` -- not merely hard to discharge in some
regime, but never satisfiable at all.

The reason: `Leaves.restComp z w v = v - ⟪z,v⟫•z - ⟪w,v⟫•w`. Write `r := q - ⟪z,q⟫•z` for `q`'s
component orthogonal to `z`. Since any unit `w ⊥ z` also has `⟪w,q⟫ = ⟪w,r⟫` (the `z`-component of
`q` drops out), `restComp z w q = r - ⟪w,r⟫•w` for every such `w`.

* If `r = 0` (`q` parallel to `z`, or `q = 0`): `restComp z w q = 0` for **every** unit `w ⊥ z`, so
  `hgenRest`'s `∀ w, ... ≠ 0` clause fails at every witness (`2 ≤ d` supplies at least one, via
  `Leaves.exists_unit_orthogonal`).
* If `r ≠ 0`: taking `w := ‖r‖⁻¹ • r` (still unit and `⊥ z`, since `⟪z,r⟫ = 0`) gives
  `⟪w,r⟫ = ‖r‖`, so `restComp z w q = r - ‖r‖ • (‖r‖⁻¹ • r) = r - r = 0`.

Either way a witnessing `w` exists with `restComp z w q = 0`, refuting the universally-quantified
`≠ 0` clause -- so `hgenRest` can never be supplied, for any `z, q`. `callerCap` (PR #273) and
`barycenter_nonColinear_of_massGapCollapse_meanField` are therefore true and kernel-clean but
**never actually invocable**: an instance of this project's own kernel-clean-not-applicable
pattern (see project memory `kernel-clean-not-applicable`). This is a bookkeeping record, not a
refutation of a Sig transcribed for the `Regression/OldStatements.lean` must-fail-adapter
machinery -- `hgenRest` is a live hypothesis of a currently-standing theorem, not a rejected axiom
draft, so there is no `Refutations/` adapter to pair with it. Recording it here (matching the
`Regression.Refuted` convention of PRs #272/#280) prevents a future session from re-attempting to
wire pole-avoidance machinery into `callerCap` as an invocation route: no choice of `w` can ever
make `hgenRest` hold, so any such route is doomed before it starts.

Two corollaries (added 2026-07-27, finding F22) state the previously prose-only entailment in the
kernel: `lemma_3_4_part2_hgenRest_unsatisfiable` shows the EXACT `∀ z, ∀ cosR, ∀ w` hypothesis
bundle of `Statements/MidLevel.lean`'s `lemma_3_4_part2` (and of
`barycenter_nonColinear_of_massGapCollapse_meanField`) is false for EVERY measure pair at every
`2 ≤ d` -- so the 2026-07-19 discharge of `lemma_3_4_part2` (PR #260) is vacuously true; and
`genRestNearBall_false` refutes `GenRestNearBall 2` outright, instantiating it at the admissible
part-2 witness pair (`Regression/NonVacuity/MidLevel.lean`'s `partTwoMu`/`partTwoNu`: distinct,
sphere- and orthant-supported, ball-confined, colinear-unequal barycenters). Everything gated on
`GenRestNearBall` (`exists_phase3_of_genRestNearBall`, `exists_phase3_nonColinear_symm`,
`exists_phase23_nonColinear`, `disentangle_insert_colinear_resolving`) is therefore kernel-clean
but vacuous until Phase 3's non-degeneracy condition is replaced.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureToMeasure MeasureToMeasure.Leaves
open scoped RealInnerProductSpace

/-- **The refutation.** For every dimension `d ≥ 2`, every unit `z`, and every `q`, there is a unit
`w` orthogonal to `z` with `Leaves.restComp z w q = 0` -- so the universally-quantified `≠ 0`
clause of `hgenRest` (`barycenter_nonColinear_of_massGapCollapse_meanField_callerCap`'s hypothesis,
PR #273, and its non-`callerCap` sibling's identical clause) can never hold. `w := normalize (q -
⟪z,q⟫•z)` zeroes `restComp z w q` whenever `q`'s component orthogonal to `z` is nonzero; when that
component is already `0`, EVERY unit `w ⊥ z` works (supplied by `Leaves.exists_unit_orthogonal`,
which needs `2 ≤ d`). -/
theorem hgenRest_unconditionally_false {d : ℕ} (hd : 2 ≤ d) (z : Eucl d) (hz : ‖z‖ = 1)
    (q : Eucl d) :
    ¬ (∀ w : Eucl d, ‖w‖ = 1 → (⟪z, w⟫ : ℝ) = 0 → Leaves.restComp z w q ≠ 0) := by
  intro hall
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hz]; norm_num
  -- `r` is `q`'s component orthogonal to `z`; `restComp z w q` depends on `q` only through `r` for
  -- any unit `w ⊥ z` (the `z`-component drops out), so the two cases below cover everything.
  set r : Eucl d := q - (⟪z, q⟫ : ℝ) • z with hr
  have hzr : (⟪z, r⟫ : ℝ) = 0 := by
    rw [hr, inner_sub_right, real_inner_smul_right, hzz, mul_one, sub_self]
  by_cases hr0 : r = 0
  · -- `q` is parallel to `z` (or zero): every unit `w ⊥ z` already zeroes `restComp z w q`.
    obtain ⟨w, hzw, hw⟩ := Leaves.exists_unit_orthogonal hd hz0
    have hqe0 : q - (⟪z, q⟫ : ℝ) • z = 0 := by rw [← hr]; exact hr0
    have hqz : q = (⟪z, q⟫ : ℝ) • z := by rw [sub_eq_zero] at hqe0; exact hqe0
    have hwq : (⟪w, q⟫ : ℝ) = 0 := by
      conv_lhs => rw [hqz]
      rw [real_inner_smul_right, real_inner_comm z w, hzw, mul_zero]
    apply hall w hw hzw
    unfold Leaves.restComp
    rw [hwq, zero_smul, sub_zero]
    exact hqe0
  · -- `q` has a nonzero orthogonal-to-`z` component `r`: `w := normalize r` zeroes `restComp z w q`.
    set w : Eucl d := ‖r‖⁻¹ • r with hw
    have hrnormne : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr0
    have hwnorm : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, norm_norm]
      field_simp
    have hzw : (⟪z, w⟫ : ℝ) = 0 := by
      rw [hw, real_inner_smul_right, hzr, mul_zero]
    have hrq : (⟪r, q⟫ : ℝ) = ‖r‖ ^ 2 := by
      have e1 : (⟪r, q⟫ : ℝ) = ⟪q, q⟫ - (⟪z, q⟫ : ℝ) * ⟪z, q⟫ := by
        rw [hr, inner_sub_left, real_inner_smul_left]
      have e2 : (⟪r, r⟫ : ℝ) = ⟪q, q⟫ - (⟪z, q⟫ : ℝ) * ⟪z, q⟫ := by
        rw [hr, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
          real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, hzz]
        rw [real_inner_comm q z]
        ring
      rw [real_inner_self_eq_norm_sq] at e2
      rw [e1, e2]
    have hwq : (⟪w, q⟫ : ℝ) = ‖r‖ := by
      rw [hw, real_inner_smul_left, hrq]
      field_simp
    apply hall w hwnorm hzw
    unfold Leaves.restComp
    rw [hwq, hw, smul_smul]
    have hinv : ‖r‖ * ‖r‖⁻¹ = 1 := mul_inv_cancel₀ hrnormne
    rw [hinv, one_smul, ← hr, sub_self]

/-- **The `lemma_3_4_part2` hypothesis bundle is unsatisfiable** (finding F22). For every `d ≥ 2`
and EVERY measure pair `μ, ν`, the exact `hgenRest` hypothesis carried by
`Statements/MidLevel.lean`'s `lemma_3_4_part2` (and by
`barycenter_nonColinear_of_massGapCollapse_meanField`) is false: instantiate the outer quantifiers
at `z := unitE d 0` and `cosR := 3/4`, then `hgenRest_unconditionally_false` refutes the inner
`∀ w, … ≠ 0` clause with `q` the leftover-mass integral of `ν`. Consequence: the discharge of
`lemma_3_4_part2` (PR #260) is vacuously true -- no instantiation can ever satisfy its hypotheses
-- so the statement is effectively OPEN pending a re-discharge with satisfiable hypotheses. -/
theorem lemma_3_4_part2_hgenRest_unsatisfiable {d : ℕ} (hd : 2 ≤ d)
    (μ ν : MeasureTheory.Measure (Eucl d)) :
    ¬ (∀ z : Eucl d, ‖z‖ = 1 → ∀ cosR : ℝ, cosR ∈ Set.Ioo (1 / 2 : ℝ) 1 →
      ∀ w : Eucl d, ‖w‖ = 1 → (⟪z, w⟫ : ℝ) = 0 →
      Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν) ≠ 0 ∧
      ∀ c : ℝ, Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ)
        ≠ c • Leaves.restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν)) := by
  intro hall
  have hd0 : 0 < d := by omega
  have hz := Regression.NonVacuity.unitE_norm d ⟨0, hd0⟩
  have h34 : (3 / 4 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
    rw [Set.mem_Ioo]; constructor <;> norm_num
  exact hgenRest_unconditionally_false hd _ hz
    (∫ x in {x : Eucl d | (3 / 4 : ℝ) < (⟪Regression.NonVacuity.unitE d ⟨0, hd0⟩, x⟫ : ℝ)}ᶜ, x ∂ν)
    (fun w hw hzw => (hall _ hz (3 / 4) h34 w hw hzw).1)

/-- **`GenRestNearBall` is refuted** (finding F22). The Phase-3-regime non-degeneracy predicate
(`Leaves/GenRestNearBall.lean`) is false at `d = 2`: instantiating its universal quantifiers at the
admissible part-2 witness pair (`Regression/NonVacuity/MidLevel.lean`'s `partTwoMu`/`partTwoNu` --
distinct, sphere- and orthant-supported, confined to `Metric.ball 0 2`, colinear-unequal
barycenters with `γ = 85/91`) yields exactly the hypothesis bundle refuted by
`lemma_3_4_part2_hgenRest_unsatisfiable`. So every theorem gated on `hgen : GenRestNearBall d`
(`exists_phase3_of_genRestNearBall` and the `DisentangleInductionStep.lean` colinear-resolving
chain) is kernel-clean but vacuous at `d = 2`; the same construction generalizes to any `d ≥ 2`
with a dimension-parametric witness pair, so the gate is not usable at any dimension. -/
theorem genRestNearBall_false : ¬ Leaves.GenRestNearBall 2 := by
  intro hgen
  exact lemma_3_4_part2_hgenRest_unsatisfiable (le_refl 2)
    Regression.NonVacuity.partTwoMu Regression.NonVacuity.partTwoNu
    (hgen 0 2 (by norm_num)
      Regression.NonVacuity.partTwoMu Regression.NonVacuity.partTwoNu
      Regression.NonVacuity.partTwoMu_ne_partTwoNu
      Regression.NonVacuity.partTwoMu_supportedIn_sphere
      Regression.NonVacuity.partTwoNu_supportedIn_sphere
      Regression.NonVacuity.partTwoMu_supportedIn_orthant
      Regression.NonVacuity.partTwoNu_supportedIn_orthant
      (Leaves.supportedIn_ball_two_of_sphere Regression.NonVacuity.partTwoMu_supportedIn_sphere)
      (Leaves.supportedIn_ball_two_of_sphere Regression.NonVacuity.partTwoNu_supportedIn_sphere)
      Regression.NonVacuity.partTwo_colinear)

end Regression.Refuted
