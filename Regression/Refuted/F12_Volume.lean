import Regression.OldStatements
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# F12: the unrestricted `lemma_3_2` / `lemma_3_3` are false (Lebesgue volume)

The pre-F12 statements quantified over EVERY measure. Instantiating with `volume` on `Eucl 1`
(an infinite open-positive Haar measure) refutes them: the linear flow map is a continuous
bijection, so the preimage of a nonempty open subset of the claimed support's complement is
nonempty open, hence of positive volume. Repaired in PR #66 (finding F12).

The mean-field variant `oldAttnLemma33_false` refutes the current-layer `lemma_3_3` with its
measure hypotheses removed: a non-conforming measure makes `attnMeasureFlow` the junk identity,
and `volume` is not supported in any ball.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow attnStep)

/-- If `measureFlow θ T volume` were supported in `S`, then no nonempty open set can sit inside
`Sᶜ`: its preimage under the (continuous, surjective) flow map would be a nonempty open set of
volume zero. -/
theorem no_volume_flow_support {θ : Params 1} {T : ℝ} (hT : 0 ≤ T) {S U : Set (Eucl 1)}
    (hUopen : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ Sᶜ)
    (hsupp : supportedIn (measureFlow θ T (volume : Measure (Eucl 1))) S) : False := by
  have hU0 : measureFlow θ T (volume : Measure (Eucl 1)) U = 0 :=
    measure_mono_null hUS hsupp
  have hmap : (volume : Measure (Eucl 1)).map (flowMap θ T) U = 0 := hU0
  rw [Measure.map_apply (MeasureToMeasure.measurable_flowMap θ hT)
    hUopen.measurableSet] at hmap
  obtain ⟨K, hK⟩ := MeasureToMeasure.exists_lipschitzWith_flowMap θ T
  have hpre_open : IsOpen (flowMap θ T ⁻¹' U) := hUopen.preimage hK.continuous
  obtain ⟨y, hy⟩ := hUne
  obtain ⟨x, hx⟩ := (MeasureToMeasure.flowMap_bijective θ T).surjective y
  have hpre_ne : (flowMap θ T ⁻¹' U).Nonempty := ⟨x, by simpa [Set.mem_preimage, hx] using hy⟩
  exact absurd hmap (hpre_open.measure_pos volume hpre_ne).ne'

/-- The open negative half-line of `Eucl 1` is nonempty, open, and misses the orthant. -/
theorem negHalfLine_facts :
    IsOpen {x : Eucl 1 | x 0 < 0} ∧ ({x : Eucl 1 | x 0 < 0}).Nonempty ∧
      {x : Eucl 1 | x 0 < 0} ⊆ (orthant 1)ᶜ := by
  refine ⟨isOpen_lt ((EuclideanSpace.proj (0 : Fin 1)).continuous) continuous_const, ?_, ?_⟩
  · exact ⟨EuclideanSpace.single 0 (-1), by norm_num [Set.mem_setOf_eq, PiLp.single_apply]⟩
  · intro x hx hmem
    exact absurd (hmem 0) (not_lt.mpr hx.le)

/-- F12: the unrestricted `lemma_3_2` is false -- `volume` cannot be flowed into the orthant. -/
theorem oldLemma32_false (ax : Regression.OldLemma32Sig) : False := by
  obtain ⟨θ, hsupp⟩ := ax (volume : Measure (Eucl 1)) 1 one_pos
  obtain ⟨hopen, hne, hsub⟩ := negHalfLine_facts
  exact no_volume_flow_support one_pos.le hopen hne hsub hsupp

/-- The complement of any closed unit ball of `Eucl 1` is nonempty and open. -/
theorem closedBall_compl_facts (α : Eucl 1) :
    IsOpen (Metric.closedBall α 1)ᶜ ∧ ((Metric.closedBall α 1)ᶜ).Nonempty := by
  refine ⟨Metric.isClosed_closedBall.isOpen_compl, ⟨α + EuclideanSpace.single 0 2, ?_⟩⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm,
    add_sub_cancel_left]
  rw [PiLp.norm_single]
  norm_num

/-- F12: the unrestricted linear `lemma_3_3` is false -- `volume` cannot be flowed into any
unit ball (historical record; the current `lemma_3_3` lives on the mean-field layer). -/
theorem oldLemma33Linear_false (ax : Regression.OldLemma33LinearSig) : False := by
  obtain ⟨θ, α, hsupp⟩ := ax (volume : Measure (Eucl 1)) 1 1 one_pos one_pos
  obtain ⟨hopen, hne⟩ := closedBall_compl_facts α
  exact no_volume_flow_support one_pos.le hopen hne
    (Set.compl_subset_compl.mpr Metric.ball_subset_closedBall) hsupp

/-- A measure with mass off the sphere is fixed by every attention step (the junk-identity
branch of `attnStep`). -/
theorem attnMeasureFlow_of_compl_sphere_ne_zero {d : ℕ} (θ : AttnSchedule d)
    {μ : Measure (Eucl d)} (h : μ (MeasureToMeasure.sphere d)ᶜ ≠ 0) :
    attnMeasureFlow θ μ = μ := by
  induction θ with
  | nil => rfl
  | cons p rest ih =>
    have hstep : attnStep p μ = μ :=
      dif_neg fun hc => h hc.2
    show attnMeasureFlow (p :: rest) μ = μ
    calc attnMeasureFlow (p :: rest) μ
        = attnMeasureFlow rest (attnStep p μ) := rfl
      _ = attnMeasureFlow rest μ := by rw [hstep]
      _ = μ := ih

/-- Lebesgue volume on `Eucl 1` has (infinite, in particular nonzero) mass off the unit
sphere. -/
theorem volume_compl_sphere_ne_zero :
    (volume : Measure (Eucl 1)) (MeasureToMeasure.sphere 1)ᶜ ≠ 0 := by
  have hopen : IsOpen (MeasureToMeasure.sphere 1)ᶜ :=
    (Metric.isClosed_sphere (x := (0 : Eucl 1)) (ε := 1)).isOpen_compl
  have hne : ((MeasureToMeasure.sphere 1)ᶜ).Nonempty := by
    refine ⟨0, ?_⟩
    simp only [MeasureToMeasure.sphere, Set.mem_compl_iff, Metric.mem_sphere,
      dist_self]
    norm_num
  exact (hopen.measure_pos volume hne).ne'

/-- F12 (mean-field layer): `lemma_3_3` with its measure hypotheses removed is false --
`volume` is non-conforming, so the flow is the junk identity, and `volume` is not supported
in any ball. -/
theorem oldAttnLemma33_false (ax : Regression.OldAttnLemma33Sig) : False := by
  obtain ⟨θ, α, hsupp⟩ := ax (volume : Measure (Eucl 1)) 1 1 one_pos one_pos
  rw [attnMeasureFlow_of_compl_sphere_ne_zero θ volume_compl_sphere_ne_zero] at hsupp
  obtain ⟨hopen, hne⟩ := closedBall_compl_facts α
  have h0 : (volume : Measure (Eucl 1)) (Metric.closedBall α 1)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr Metric.ball_subset_closedBall) hsupp
  exact absurd h0 (hopen.measure_pos volume hne).ne'

end Regression.Refuted
