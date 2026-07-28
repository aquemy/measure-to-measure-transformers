import MeasureToMeasure.Leaves.GatedPullTransfer
import MeasureToMeasure.Leaves.HemisphereCollapse
import MeasureToMeasure.Leaves.PoleGeometry

/-!
# Three-pull chain: hemisphere mass to any prescribed sphere point

The mathematical heart of the `cluster_to_point` discharge. `cluster_to_point` asks for a schedule
driving a sphere-supported probability measure carried by the open hemisphere `{0 < ⟪e,·⟫}`
`W₂`-within `ε` of the Dirac at ANY prescribed sphere point `z`, with duration exactly `T`. The
paper composes Proposition 2.1 (cluster at the hemisphere pole) with Proposition 4.2 (steer the
point to `z`); on the mean-field layer the same effect is a chain of THREE gated pulls, relaying
the concentrated cap `e → α → z` through a unit vector `α` orthogonal to BOTH `e` and `z`
(`exists_unit_orthogonal_two`, the only consumer of `3 ≤ d`; the relay handles `z = e` and
`z = -e` uniformly, no case split).

Assembly, all pieces previously banked:

* **Mass split** (`hemisphere_subcap_mass_le`): all but `ε²/8` of the mass clears some entry level
  `m ∈ (0,1)` towards `e`. This budget does NOT accumulate along the chain: each pull maps
  off-cap-after inside off-entry-before, and each hand-off maps off-entry-before inside the
  previous pull's off-cap.
* **Three pulls** (`exists_gatedPull_cap_transfer`, blocks chosen before the measures, each of
  duration `T/3`): pull 1 towards `e` from level `m` to `7/8`; pull 2 towards `α` from `-(1/2)`
  to `7/8`; pull 3 towards `z` from `-(1/2)` to `b₃ := max (1-ε²/4) 0`.
* **Two hand-offs** (`inner_orthogonal_ge_of_mem_cap`): a sphere point of the tight cap
  `{7/8 ≤ ⟪·,u⟫}` has inner product `≥ -(1/2)` against any orthogonal unit pole, so the mass
  concentrated by each pull automatically clears the next pull's entry level.
* **Closer** (`W2_dirac_le_of_closedBall_mass`): pull 3's chordal conjunct leaves at most `ε²/8`
  outside `B(z, √(2(1-b₃)))`, and `√(2(1-b₃) + 4·ε²/8) ≤ √(ε²/2 + ε²/2) = ε`.

The threading invariants (probability + sphere support along the chain) come from
`isProbabilityMeasure_attnMeasureFlow` / `attnMeasureFlow_supportedIn_sphere`, and the schedule
composes by `attnMeasureFlow_append`. The conclusion shape (`durationSum = T`, three constant
pieces, `W₂ ≤ ε` to `dirac z`) is exactly `cluster_to_point`'s, with `θ.length = 3` sharpening
its `switches θ ≤ 7` budget.
-/

set_option autoImplicit false

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Axioms MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **Three-pull cluster to a prescribed sphere point.** A sphere-supported probability measure
carried by the open hemisphere `{0 < ⟪e,·⟫}` is driven `W₂`-within `ε` of the Dirac at ANY chosen
sphere point `z` by a schedule of exactly THREE constant pieces, of total duration exactly `T`:
pull towards the hemisphere pole `e`, relay towards a unit `α ⊥ e, z` (this is where `3 ≤ d` is
consumed), then pull towards `z`. Each pull's `ε²/8` budget is handed off, not accumulated: the
tight `7/8`-cap of one pull clears the next pull's `-(1/2)` entry level around any orthogonal
pole. -/
theorem exists_three_pull_cluster_to_target (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hd : 3 ≤ d) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (z e : Eucl d) (hz : z ∈ sphere d) (he : ‖e‖ = 1)
    (hμs : supportedIn μ (sphere d)) (hhemi : supportedIn μ {x | 0 < ⟪e, x⟫}) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧ θ.length = 3 ∧
      Axioms.W2 (attnMeasureFlow θ μ) (Measure.dirac z) ≤ ε := by
  have hzn : ‖z‖ = 1 := norm_eq_one_of_mem_sphere hz
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hzn; exact zero_ne_one hzn
  -- the relay pole: a unit vector orthogonal to BOTH z and e (needs 3 ≤ d)
  obtain ⟨α, hzα, heα, hα⟩ := exists_unit_orthogonal_two hd hz0 e
  have hαz : (⟪α, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzα
  have hT3 : 0 < T / 3 := by positivity
  -- mass split: all but ε²/8 of the mass clears pull 1's entry level m
  obtain ⟨m, hm0, hm1, hμm⟩ := hemisphere_subcap_mass_le μ hhemi
    (budget := ENNReal.ofReal (ε ^ 2 / 8)) (ENNReal.ofReal_pos.mpr (by positivity))
  -- final cap level b3: within Ioo (-1) 1 with deficit 1 - b3 ≤ ε²/4
  set b3 : ℝ := max (1 - ε ^ 2 / 4) 0 with hb3def
  have hb3 : b3 ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    · apply max_lt _ one_pos
      nlinarith
  have hb3ge : 1 - ε ^ 2 / 4 ≤ b3 := le_max_left _ _
  have hb31 : 1 - b3 ≤ ε ^ 2 / 4 := by linarith
  have hhalf : (-(1 / 2) : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have h78 : (7 / 8 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  -- the three pulls, each of duration T/3, blocks chosen before the measures
  obtain ⟨p1, hp1d, hp1⟩ := exists_gatedPull_cap_transfer he
    (m := m) (b := 7 / 8) ⟨by linarith, hm1⟩ h78 hT3
  obtain ⟨p2, hp2d, hp2⟩ := exists_gatedPull_cap_transfer hα
    (m := -(1 / 2)) (b := 7 / 8) hhalf h78 hT3
  obtain ⟨p3, hp3d, hp3⟩ := exists_gatedPull_cap_transfer hzn
    (m := -(1 / 2)) (b := b3) hhalf hb3 hT3
  refine ⟨[p1, p2, p3], ?_, rfl, ?_⟩
  · simp only [AttnSchedule.durationSum, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, hp1d, hp2d, hp3d]
    ring
  -- the measure chain and its threading invariants
  have hμsc : μ (sphere d)ᶜ = 0 := hμs
  set μ1 : Measure (Eucl d) := attnMeasureFlow [p1] μ with hμ1def
  haveI : IsProbabilityMeasure μ1 := isProbabilityMeasure_attnMeasureFlow [p1] μ hμsc
  have hμ1S : μ1 (sphere d)ᶜ = 0 := attnMeasureFlow_supportedIn_sphere [p1] μ hμsc
  have hμ1s' : supportedIn μ1 (sphere d) := hμ1S
  set μ2 : Measure (Eucl d) := attnMeasureFlow [p2] μ1 with hμ2def
  haveI : IsProbabilityMeasure μ2 := isProbabilityMeasure_attnMeasureFlow [p2] μ1 hμ1S
  have hμ2S : μ2 (sphere d)ᶜ = 0 := attnMeasureFlow_supportedIn_sphere [p2] μ1 hμ1S
  have hμ2s' : supportedIn μ2 (sphere d) := hμ2S
  set μ3 : Measure (Eucl d) := attnMeasureFlow [p3] μ2 with hμ3def
  haveI : IsProbabilityMeasure μ3 := isProbabilityMeasure_attnMeasureFlow [p3] μ2 hμ2S
  have hμ3S : μ3 (sphere d)ᶜ = 0 := attnMeasureFlow_supportedIn_sphere [p3] μ2 hμ2S
  have hflow : attnMeasureFlow [p1, p2, p3] μ = μ3 := by
    have hsplit : ([p1, p2, p3] : AttnSchedule d) = [p1] ++ ([p2] ++ [p3]) := rfl
    rw [hsplit, attnMeasureFlow_append, attnMeasureFlow_append]
  -- pull 1: off-cap mass around e at level 7/8 drops to the budget
  have hμ1cap : μ1 {y : Eucl d | (⟪y, e⟫ : ℝ) < 7 / 8} ≤ ENNReal.ofReal (ε ^ 2 / 8) := by
    refine le_trans (hp1 μ hμs).1 ?_
    have hset : {x : Eucl d | (⟪x, e⟫ : ℝ) < m} = {x : Eucl d | (⟪e, x⟫ : ℝ) < m} := by
      ext x
      simp only [Set.mem_setOf_eq, real_inner_comm]
    rw [hset]
    exact hμm
  -- hand-off 1 → 2: the tight cap around e clears p2's entry level -(1/2) around α
  have hhand12 : μ1 {x : Eucl d | (⟪x, α⟫ : ℝ) < -(1 / 2)}
      ≤ μ1 {y : Eucl d | (⟪y, e⟫ : ℝ) < 7 / 8} := by
    have hsub : {x : Eucl d | (⟪x, α⟫ : ℝ) < -(1 / 2)}
        ⊆ (sphere d)ᶜ ∪ {y : Eucl d | (⟪y, e⟫ : ℝ) < 7 / 8} := by
      intro x hx
      by_cases hxs : x ∈ sphere d
      · refine Set.mem_union_right _ ?_
        by_contra hxc
        have hxc' : (7 / 8 : ℝ) ≤ ⟪x, e⟫ := not_lt.mp hxc
        have hge := inner_orthogonal_ge_of_mem_cap he hα heα le_rfl hxs hxc'
        simp only [Set.mem_setOf_eq] at hx
        linarith
      · exact Set.mem_union_left _ hxs
    calc μ1 {x : Eucl d | (⟪x, α⟫ : ℝ) < -(1 / 2)}
        ≤ μ1 ((sphere d)ᶜ ∪ {y : Eucl d | (⟪y, e⟫ : ℝ) < 7 / 8}) := measure_mono hsub
      _ ≤ μ1 (sphere d)ᶜ + μ1 {y : Eucl d | (⟪y, e⟫ : ℝ) < 7 / 8} := measure_union_le _ _
      _ = μ1 {y : Eucl d | (⟪y, e⟫ : ℝ) < 7 / 8} := by rw [hμ1S, zero_add]
  -- pull 2: off-cap mass around α at level 7/8 stays within the budget
  have hμ2cap : μ2 {y : Eucl d | (⟪y, α⟫ : ℝ) < 7 / 8} ≤ ENNReal.ofReal (ε ^ 2 / 8) :=
    le_trans (hp2 μ1 hμ1s').1 (le_trans hhand12 hμ1cap)
  -- hand-off 2 → 3: the tight cap around α clears p3's entry level -(1/2) around z
  have hhand23 : μ2 {x : Eucl d | (⟪x, z⟫ : ℝ) < -(1 / 2)}
      ≤ μ2 {y : Eucl d | (⟪y, α⟫ : ℝ) < 7 / 8} := by
    have hsub : {x : Eucl d | (⟪x, z⟫ : ℝ) < -(1 / 2)}
        ⊆ (sphere d)ᶜ ∪ {y : Eucl d | (⟪y, α⟫ : ℝ) < 7 / 8} := by
      intro x hx
      by_cases hxs : x ∈ sphere d
      · refine Set.mem_union_right _ ?_
        by_contra hxc
        have hxc' : (7 / 8 : ℝ) ≤ ⟪x, α⟫ := not_lt.mp hxc
        have hge := inner_orthogonal_ge_of_mem_cap hα hzn hαz le_rfl hxs hxc'
        simp only [Set.mem_setOf_eq] at hx
        linarith
      · exact Set.mem_union_left _ hxs
    calc μ2 {x : Eucl d | (⟪x, z⟫ : ℝ) < -(1 / 2)}
        ≤ μ2 ((sphere d)ᶜ ∪ {y : Eucl d | (⟪y, α⟫ : ℝ) < 7 / 8}) := measure_mono hsub
      _ ≤ μ2 (sphere d)ᶜ + μ2 {y : Eucl d | (⟪y, α⟫ : ℝ) < 7 / 8} := measure_union_le _ _
      _ = μ2 {y : Eucl d | (⟪y, α⟫ : ℝ) < 7 / 8} := by rw [hμ2S, zero_add]
  -- pull 3, chordal form: mass outside the closed ball around z stays within the budget
  have hmass : μ3 (Metric.closedBall z (Real.sqrt (2 * (1 - b3))))ᶜ
      ≤ ENNReal.ofReal (ε ^ 2 / 8) :=
    le_trans (hp3 μ2 hμ2s').2 (le_trans hhand23 hμ2cap)
  -- close in W₂: √(2(1-b3) + 4·ε²/8) ≤ √(ε²/2 + ε²/2) = ε
  have hW2 := MeasureToMeasure.W2_dirac_le_of_closedBall_mass μ3 hμ3S z hz
    (Real.sqrt (2 * (1 - b3))) (ε ^ 2 / 8) (Real.sqrt_nonneg _) (by positivity) hmass
  have hRsq : Real.sqrt (2 * (1 - b3)) ^ 2 = 2 * (1 - b3) :=
    Real.sq_sqrt (by nlinarith [hb3.2])
  have harg : Real.sqrt (2 * (1 - b3)) ^ 2 + 4 * (ε ^ 2 / 8) ≤ ε ^ 2 := by
    rw [hRsq]; nlinarith
  have hsqrt : Real.sqrt (Real.sqrt (2 * (1 - b3)) ^ 2 + 4 * (ε ^ 2 / 8)) ≤ ε := by
    calc Real.sqrt (Real.sqrt (2 * (1 - b3)) ^ 2 + 4 * (ε ^ 2 / 8))
        ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt harg
      _ = ε := Real.sqrt_sq hε.le
  rw [hflow]
  show (MeasureToMeasure.W2 μ3 (Measure.dirac z)).toReal ≤ ε
  calc (MeasureToMeasure.W2 μ3 (Measure.dirac z)).toReal
      ≤ (ENNReal.ofReal (Real.sqrt (Real.sqrt (2 * (1 - b3)) ^ 2 + 4 * (ε ^ 2 / 8)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hW2
    _ = Real.sqrt (Real.sqrt (2 * (1 - b3)) ^ 2 + 4 * (ε ^ 2 / 8)) :=
        ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
    _ ≤ ε := hsqrt

end MeasureToMeasure.Leaves
