import MeasureToMeasure.Leaves.GatedTwoCap
import MeasureToMeasure.Leaves.GatedBlockMeanFieldBridge
import MeasureToMeasure.Statements.SupportedIn
import MeasureToMeasure.Axioms.Dynamics

/-!
# Gated pull as a reusable cap-mass transfer block

The `prop_2_1` engine (`Leaves/HemisphereCollapse.lean`) inlines a bookkeeping pattern that every
phase of the `cluster_to_point` three-pull witness needs again: a single amplitude-scaled gated
block whose flow moves all sphere mass above an inner-product level `m` (towards a pole `ω`) above
a target level `b`, so the mass LEFT below `b` after the flow is at most the mass below `m` before
it. This file extracts that pattern as a standalone lemma, `exists_gatedPull_cap_transfer`,
quantified over ALL sphere-supported probability inputs.

The quantifier order is the point: the block `p` is chosen BEFORE the measure `ν`, legal because
`exists_scaledGatedBlock_mapsTo_cap`'s amplitude choice depends only on the geometry (`ω`, the
levels `m`, `b`, the horizon `T`), never on the measure. Downstream phases can therefore fix one
block and apply it to whatever intermediate measure the previous phase produced.

The same `p` also satisfies the chordal form (the `HemisphereCollapse.lean` conversion
`‖y-ω‖² = 2-2⟪y,ω⟫ ≤ 2(1-b)` on the sphere): the flowed mass outside the closed chordal ball
`B(ω, √(2(1-b)))` obeys the same bound, so consumers closing in `W₂` via
`W2_dirac_le_of_closedBall_mass` never redo the conversion.

This file is deliberately a THIN application layer: the ODE/flow content lives entirely in the
banked `GatedTwoCap.lean` (amplitude choice) and `GatedBlockMeanFieldBridge.lean` (mean-field =
linear pushforward on the sphere); nothing is re-elaborated here. `NeZero d` is derived from the
unit-vector hypothesis (`d = 0` has only the zero vector), not assumed, per the `Prop21.lean`
precedent.
-/

set_option autoImplicit false

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Axioms MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **Gated pull as a cap-mass transfer, measure-free block choice.** For a unit pole `ω`, levels
`-1 < m < 1` and `b ∈ (-1,1)`, and any horizon `T > 0`, ONE attention block `p` of duration
exactly `T` works for EVERY sphere-supported probability measure `ν`: after the flow, the mass
below the target level `b` (equivalently, outside the closed chordal ball `B(ω, √(2(1-b)))`) is
at most the mass `ν` had below the entry level `m`.

Witness: `pParkScaled A ω ω (-1) T` with gate level `cosR = -1` (open on the whole sphere minus
the antipode) and the amplitude `A` of `exists_scaledGatedBlock_mapsTo_cap`, which pulls the
closed sub-cap `{m ≤ ⟪·,ω⟫}` above `b` in time `T`; the block depends only on `ω`, `m`, `b`, `T`.
The bound is pushforward bookkeeping through the mean-field bridge: the preimage of `{⟪·,ω⟫ < b}`
misses the pulled sub-cap, so it sits inside `(sphere)ᶜ ∪ {⟪·,ω⟫ < m}`, and sphere support kills
the first piece. The chordal form follows since on the sphere `⟪y,ω⟫ ≥ b` reads as
`‖y-ω‖ ≤ √(2(1-b))`. -/
theorem exists_gatedPull_cap_transfer {ω : Eucl d} (hω : ‖ω‖ = 1)
    {m b : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    {T : ℝ} (hT : 0 < T) :
    ∃ p : AttnParams d, p.duration = T ∧
      ∀ (ν : Measure (Eucl d)) [IsProbabilityMeasure ν], supportedIn ν (sphere d) →
        (attnMeasureFlow [p] ν) {y | (⟪y, ω⟫ : ℝ) < b} ≤ ν {x | (⟪x, ω⟫ : ℝ) < m} ∧
        (attnMeasureFlow [p] ν) (Metric.closedBall ω (Real.sqrt (2 * (1 - b))))ᶜ
          ≤ ν {x | (⟪x, ω⟫ : ℝ) < m} := by
  haveI : NeZero d := ⟨by
    intro hd
    subst hd
    have h0 : ω = 0 := by ext i; exact i.elim0
    rw [h0, norm_zero] at hω
    exact zero_ne_one hω⟩
  have hcosR : (-1 : ℝ) ≤ -1 := le_rfl
  -- amplitude meeting the rim budget at horizon exactly `T`; depends only on geometry, not `ν`
  obtain ⟨A, hA, hmaps⟩ := exists_scaledGatedBlock_mapsTo_cap (ω := ω) hω
    (cosR := -1) hcosR hT hm.1 hm.2 hb
  set B : Block d := scaledGatedBlock hA hω hω hcosR hT.le with hBdef
  refine ⟨pParkScaled A ω ω (-1) T hT.le, rfl, ?_⟩
  intro ν _inst hνs
  rw [supportedIn] at hνs
  -- mean-field bridge: the attention flow of `p` IS the linear pushforward by `B.blockFlow T`
  have hbr : attnMeasureFlow [pParkScaled A ω ω (-1) T hT.le] ν = measureFlow [B] T ν :=
    attnMeasureFlow_pParkScaled_eq_measureFlow_scaledGatedBlock hA hω hω hcosR hT.le hνs
  set ν' : Measure (Eucl d) := measureFlow [B] T ν with hν'def
  have hν'S : ν' (sphere d)ᶜ = 0 := measureFlow_supportedIn_sphere _ hT.le hνs
  have hν'map : ν' = ν.map (B.blockFlow T) := by
    rw [hν'def, measureFlow_map, flowMap_cons, flowMap_nil, Function.id_comp]
  have hcontb : Continuous (fun y : Eucl d => (⟪y, ω⟫ : ℝ)) :=
    continuous_id.inner continuous_const
  have hSMb : MeasurableSet {y : Eucl d | (⟪y, ω⟫ : ℝ) < b} :=
    measurableSet_lt hcontb.measurable measurable_const
  -- pushforward bookkeeping: mass below level `b` after the flow is below the level-`m` mass
  have hsub : ν' {y : Eucl d | (⟪y, ω⟫ : ℝ) < b} ≤ ν {x : Eucl d | (⟪x, ω⟫ : ℝ) < m} := by
    rw [hν'map, Measure.map_apply (B.measurable_blockFlow hT.le) hSMb]
    have hpre : (B.blockFlow T) ⁻¹' {y : Eucl d | (⟪y, ω⟫ : ℝ) < b}
        ⊆ (sphere d)ᶜ ∪ {x : Eucl d | (⟪x, ω⟫ : ℝ) < m} := by
      intro x hx
      by_cases hxs : x ∈ sphere d
      · refine Set.mem_union_right _ ?_
        by_contra hxm
        have hxm' : m ≤ (⟪x, ω⟫ : ℝ) := not_lt.mp fun h => hxm h
        have hcap := hmaps (show x ∈ {x : Eucl d | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)}
          from ⟨hxs, hxm'⟩)
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx hcap
        linarith
      · exact Set.mem_union_left _ hxs
    calc ν ((B.blockFlow T) ⁻¹' {y : Eucl d | (⟪y, ω⟫ : ℝ) < b})
        ≤ ν ((sphere d)ᶜ ∪ {x : Eucl d | (⟪x, ω⟫ : ℝ) < m}) := measure_mono hpre
      _ ≤ ν (sphere d)ᶜ + ν {x : Eucl d | (⟪x, ω⟫ : ℝ) < m} := measure_union_le _ _
      _ = ν {x : Eucl d | (⟪x, ω⟫ : ℝ) < m} := by rw [hνs, zero_add]
  refine ⟨by rw [hbr]; exact hsub, ?_⟩
  rw [hbr]
  -- chordal cap: on the sphere, `b ≤ ⟪y,ω⟫` puts `y` in the closed ball of radius `√(2(1-b))`
  set R : ℝ := Real.sqrt (2 * (1 - b)) with hRdef
  have hchord : (Metric.closedBall ω R)ᶜ
      ⊆ (sphere d)ᶜ ∪ {y : Eucl d | (⟪y, ω⟫ : ℝ) < b} := by
    intro y hy
    by_cases hys : y ∈ sphere d
    · refine Set.mem_union_right _ ?_
      by_contra hyb
      have hyb' : b ≤ (⟪y, ω⟫ : ℝ) := not_lt.mp fun h => hyb h
      refine hy ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hyn : ‖y‖ = 1 := norm_eq_one_of_mem_sphere hys
      have hsq : ‖y - ω‖ ^ 2 = 2 - 2 * (⟪y, ω⟫ : ℝ) := by
        rw [norm_sub_sq_real, hyn, hω]; ring
      have h2 : ‖y - ω‖ ^ 2 ≤ 2 * (1 - b) := by rw [hsq]; linarith
      calc ‖y - ω‖ = Real.sqrt (‖y - ω‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (2 * (1 - b)) := Real.sqrt_le_sqrt h2
    · exact Set.mem_union_left _ hys
  calc ν' (Metric.closedBall ω R)ᶜ
      ≤ ν' ((sphere d)ᶜ ∪ {y : Eucl d | (⟪y, ω⟫ : ℝ) < b}) := measure_mono hchord
    _ ≤ ν' (sphere d)ᶜ + ν' {y : Eucl d | (⟪y, ω⟫ : ℝ) < b} := measure_union_le _ _
    _ = ν' {y : Eucl d | (⟪y, ω⟫ : ℝ) < b} := by rw [hν'S, zero_add]
    _ ≤ ν {x : Eucl d | (⟪x, ω⟫ : ℝ) < m} := hsub

end MeasureToMeasure.Leaves
