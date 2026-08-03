import MeasureToMeasure.Statements.MidLevel
import MeasureToMeasure.Leaves.MixtureAverage
import MeasureToMeasure.Leaves.UniversalFlowPointwise

/-!
# The map-targets parked schedule: one schedule transports a disjoint family to its pushforwards

`exists_parked_schedule_of_map_targets` is the machine-checked companion to the
`exists_parked_schedule` axiom of `Statements/MidLevel.lean`: for a family of sphere-supported
probability measures with pairwise disjoint supports whose targets are PUSHFORWARDS
`(ν i).map (S i)` of the members themselves, a single schedule of exact total duration `T`
steers every member to within `W₂`-distance `ε` of its target, with no axiom.

It lives in its own file, not in `MidLevel`, per the `Prop21.lean` precedent: the proof consumes
the leaf engines (`Leaves/MixtureAverage.lean`, `Leaves/UniversalFlowPointwise.lean`), which
`MidLevel` must not import (the leaf layer already imports the statement vocabulary).

The construction (Theorem 1.2, general case, Step 2, p.25, and Lemma 5.4, p.24, eq. (5.5),
arXiv:2411.04551v3): glue the per-member maps into ONE measurable map `g` over the disjoint
carriers (`exists_measurable_glue`, the Lemma 5.1 core), form the uniform mixture
`ν̄ = N⁻¹ ∑ i, ν i` (`Leaves.avgMeasure`), and run the UNIVERSAL `lemma_5_4` engine on `(ν̄, g)`
at tolerance `ε / √N`: its transport map `ψε` is measure-independent (`V = 0` blocks), so the one
schedule pushes every member through the same `ψε`, and the member-level `L²` error is controlled
by `N` times the mixture-level error (`integral_le_card_mul_avg`), which the `√N` tolerance
absorbs exactly. The coupling bound `W2_map_le_L2` (Lemma 5.2) converts `L²` to `W₂`.

Two honesty notes on scope:

* **Why this does not collide with finding F28** (`lemma33_no_universal_map`: no single map can
  simultaneously reproduce targets that split a shared atom): here the members have pairwise
  DISJOINT carriers, so no bystander shares an atom with an acted member -- each member's target
  is its own pushforward, prescribed only on its own carrier, and the glued `g` realizes all of
  them at once. The F28 obstruction needs two measures giving positive mass to the SAME point
  with conflicting images, which `DisjointSupports` rules out.
* **Why the axiom stays**: `exists_parked_schedule` takes ARBITRARY target measures reachable by
  arbitrary (`V ≠ 0`) per-member schedules at EXACT tolerance `ε`, plus a summed switch budget.
  Reproducing an arbitrary mean-field endpoint as a pushforward of the source is the
  twice-recorded wall (the "restrict to `V = 0`" attempts of 2026-07-09 and 2026-07-14 broke
  `theorem_1_1`/`theorem_1_2` via `cluster_to_point`/`lemma_5_4` needing nonzero attention), so
  the companion covers exactly the map-shaped uses; the axiom keeps the general form. The
  companion deliberately has NO switches conjunct: both intended consumers discard it.
-/

set_option autoImplicit false

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **Parked schedule for map targets** (Theorem 1.2 general proof, Step 2, p.25; Lemma 5.4,
p.24, eq. (5.5), arXiv:2411.04551v3). A family of sphere-supported probability measures with
pairwise disjoint supports, each targeting its own pushforward under a measurable a.e.
sphere-valued map, is steered by ONE schedule of exact total duration `T` to within `ε` of every
target simultaneously. Machine-checked end to end: glue (`exists_measurable_glue`) + mixture
(`Leaves.avgMeasure`) + the universal `lemma_5_4` transport map at tolerance `ε / √N` + the
coupling bound (`W2_map_le_L2`), with the `N = 0` corner served by the parked pad block. See the
file docstring for why this companion does not collide with finding F28 and why the general
`exists_parked_schedule` axiom (arbitrary targets, exact tolerance, switch budget) remains. -/
theorem exists_parked_schedule_of_map_targets {N : ℕ} (hd : 3 ≤ d)
    (ν : Fin N → Measure (Eucl d)) (S : Fin N → Eucl d → Eucl d) (T ε : ℝ)
    (hT : 0 < T) (hε : 0 < ε)
    (hν : ∀ i, IsProbabilityMeasure (ν i))
    (hνs : ∀ i, supportedIn (ν i) (sphere d))
    (hdisj : DisjointSupports ν)
    (hSm : ∀ i, Measurable (S i))
    (hSs : ∀ i, ∀ᵐ y ∂ν i, S i y ∈ sphere d) :
    ∃ Θ : AttnSchedule d, AttnSchedule.durationSum Θ = T ∧
      ∀ i, Axioms.W2 (attnMeasureFlow Θ (ν i)) ((ν i).map (S i)) ≤ ε := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- `N = 0`: the parked pad block spends the horizon; the family clause is vacuous.
    haveI : NeZero d := ⟨by omega⟩
    obtain ⟨p, hpdur, -⟩ := Leaves.exists_parked_pad_block (d := d) hT.le
    subst hN0
    exact ⟨[p], by simp [AttnSchedule.durationSum, hpdur], fun i => i.elim0⟩
  · have hN : N ≠ 0 := hNpos.ne'
    -- Glue the per-member targets into one measurable map over the disjoint carriers.
    obtain ⟨g, hgm, hgae⟩ := exists_measurable_glue ν hdisj S hSm
    -- The uniform mixture: probability, sphere-supported, with `g` a.e. sphere-valued.
    set νb := Leaves.avgMeasure ν with hνb
    haveI : IsProbabilityMeasure νb := Leaves.isProbabilityMeasure_avgMeasure hN ν hν
    have hνbs : supportedIn νb (sphere d) := Leaves.avgMeasure_supportedIn ν fun i => hνs i
    have hgs : ∀ᵐ x ∂νb, g x ∈ sphere d := by
      apply Leaves.ae_avgMeasure_of_forall
      intro i
      filter_upwards [hgae i, hSs i] with x hgx hSx
      rw [hgx]; exact hSx
    have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
    -- The universal lemma 5.4 engine on the mixture, at tolerance `ε / √N`.
    obtain ⟨θ, ψε, hdur, hflow, hψεm, hint, hL2⟩ :=
      lemma_5_4 hd νb g T (ε / Real.sqrt N) hT (div_pos hε hsqrtN) hνbs hgm hgs
    refine ⟨θ, hdur, fun i => ?_⟩
    haveI := hν i
    -- The one transport map serves every member; the target is the same pushforward a.e.
    have hflow_i : attnMeasureFlow θ (ν i) = (ν i).map ψε := hflow (ν i) (hνs i)
    have hmapS : (ν i).map (S i) = (ν i).map g := (Measure.map_congr (hgae i)).symm
    have hint_i : Integrable (fun x => ‖ψε x - g x‖ ^ 2) (ν i) :=
      (Leaves.integrable_of_avgMeasure hN ν hint i).congr
        (Filter.Eventually.of_forall fun x => by simp only [norm_sub_rev])
    -- Member-level `L²` error through the mixture: `∫ ∂ν i ≤ N ∫ ∂ν̄ ≤ N (ε/√N)² = ε²`.
    have hIμ : ∫ x, ‖g x - ψε x‖ ^ 2 ∂ν i ≤ N * ∫ x, ‖g x - ψε x‖ ^ 2 ∂νb :=
      Leaves.integral_le_card_mul_avg hN ν (fun x => sq_nonneg _) hint i
    have hI0 : (0:ℝ) ≤ ∫ x, ‖g x - ψε x‖ ^ 2 ∂νb := integral_nonneg fun x => sq_nonneg _
    have hIbar : ∫ x, ‖g x - ψε x‖ ^ 2 ∂νb ≤ (ε / Real.sqrt N) ^ 2 := by
      calc ∫ x, ‖g x - ψε x‖ ^ 2 ∂νb
          = Real.sqrt (∫ x, ‖g x - ψε x‖ ^ 2 ∂νb) ^ 2 := (Real.sq_sqrt hI0).symm
        _ ≤ (ε / Real.sqrt N) ^ 2 := by gcongr
    have hNI : (N : ℝ) * ∫ x, ‖g x - ψε x‖ ^ 2 ∂νb ≤ ε ^ 2 := by
      have hsq : (ε / Real.sqrt N) ^ 2 = ε ^ 2 / N := by
        rw [div_pow, Real.sq_sqrt (by positivity)]
      have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      calc (N : ℝ) * ∫ x, ‖g x - ψε x‖ ^ 2 ∂νb
          ≤ N * (ε ^ 2 / N) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
            rw [← hsq]; exact hIbar
        _ = ε ^ 2 := mul_div_cancel₀ _ hNne
    -- Assemble: pushforward identities, the coupling bound, and the `√` of the `ε²` budget.
    calc Axioms.W2 (attnMeasureFlow θ (ν i)) ((ν i).map (S i))
        = Axioms.W2 ((ν i).map ψε) ((ν i).map g) := by rw [hflow_i, hmapS]
      _ ≤ Real.sqrt (∫ x, ‖ψε x - g x‖ ^ 2 ∂ν i) :=
          Axioms.W2_map_le_L2 (ν i) ψε g hψεm hgm hint_i
      _ = Real.sqrt (∫ x, ‖g x - ψε x‖ ^ 2 ∂ν i) := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
            simp only [norm_sub_rev])
      _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt (hIμ.trans hNI)
      _ = ε := Real.sqrt_sq hε.le

end MeasureToMeasure.Statements
