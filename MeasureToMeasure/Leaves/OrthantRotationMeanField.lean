import MeasureToMeasure.Leaves.OrthantRotation
import MeasureToMeasure.Leaves.GatedBlockMeanFieldBridge

/-!
# The two-phase rotation into the positive orthant — mean-field form (Lemma 3.2's dynamical core)

`exists_twoPhase_mapsTo_orthant` (`Leaves/OrthantRotation.lean`) is machine-checked on the LINEAR
layer: a two-block schedule `[B₁, B₂]` (both `scaledGatedBlock`s) rotates any sphere point missing a
direction `ω` into the orthant. `exists_disentangling_balls`'s own induction needs this fact on the
MEAN-FIELD layer. This file reproduces `exists_twoPhase_mapsTo_orthant`'s ENTIRE geometric
construction (all real-number/vector algebra, no flow dependence) verbatim, and swaps only the final
two-block flow composition for the mean-field `pParkScaled` pair: `attnMeasureFlow_two_eq_map_comp`
composes two single-step mean-field flows into one pushforward, then
`GatedBlockMeanFieldBridge.lean`'s scaled bridge is applied ONCE PER PHASE to identify each mean-field
step with its `scaledGatedBlock` counterpart.

M3b/mid-level staging: consumed when `exists_disentangling_balls` is discharged.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure
open scoped RealInnerProductSpace
open MeasureToMeasure.Foundations MeasureToMeasure.Axioms

variable {d : ℕ}

/-- Composing two mean-field steps into a single pushforward, exposing each step's own
`IsMeanFieldFlow` witness (not just the raw map) so downstream bridges can be applied. -/
theorem attnMeasureFlow_two_eq_map_comp (p₁ p₂ : AttnParams d) {μ0 : Measure (Eucl d)}
    [IsProbabilityMeasure μ0] (hμ0S : μ0 (sphere d)ᶜ = 0) :
    ∃ (Φ₁ Φ₂ : ℝ → Eucl d → Eucl d), IsMeanFieldFlow p₁ μ0 Φ₁ ∧
      IsMeanFieldFlow p₂ (μ0.map (Φ₁ p₁.duration)) Φ₂ ∧
      attnMeasureFlow [p₁, p₂] μ0 = μ0.map (Φ₂ p₂.duration ∘ Φ₁ p₁.duration) := by
  have hex₁ := @exists_meanFieldFlow d p₁ μ0 ‹_› hμ0S
  set Φ₁ := hex₁.choose with hΦ₁def
  have hΦ₁spec : IsMeanFieldFlow p₁ μ0 Φ₁ := hex₁.choose_spec
  have hΦ₁m : Measurable (Φ₁ p₁.duration) :=
    hΦ₁spec.measurable p₁.duration ⟨p₁.duration_nonneg, le_rfl⟩
  have hΦ₁maps : Set.MapsTo (Φ₁ p₁.duration) (sphere d) (sphere d) :=
    (hΦ₁spec.sphere_bijOn p₁.duration ⟨p₁.duration_nonneg, le_rfl⟩).mapsTo
  have hstep1 : attnStep p₁ μ0 = μ0.map (Φ₁ p₁.duration) := by
    unfold attnStep; rw [dif_pos ⟨‹_›, hμ0S⟩]
  set ν : Measure (Eucl d) := μ0.map (Φ₁ p₁.duration) with hνdef
  haveI hνprob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hΦ₁m.aemeasurable
  have hνS : ν (sphere d)ᶜ = 0 := by
    have hmscompl : MeasurableSet (sphere d)ᶜ := Metric.isClosed_sphere.measurableSet.compl
    rw [hνdef, Measure.map_apply hΦ₁m hmscompl]
    apply measure_mono_null _ hμ0S
    intro x hx hxs
    exact hx (hΦ₁maps hxs)
  have hex₂ := @exists_meanFieldFlow d p₂ ν hνprob hνS
  set Φ₂ := hex₂.choose with hΦ₂def
  have hΦ₂spec : IsMeanFieldFlow p₂ ν Φ₂ := hex₂.choose_spec
  have hΦ₂m : Measurable (Φ₂ p₂.duration) :=
    hΦ₂spec.measurable p₂.duration ⟨p₂.duration_nonneg, le_rfl⟩
  have hstep2 : attnStep p₂ ν = ν.map (Φ₂ p₂.duration) := by
    unfold attnStep; rw [dif_pos ⟨‹_›, hνS⟩]
  refine ⟨Φ₁, Φ₂, hΦ₁spec, hΦ₂spec, ?_⟩
  show attnMeasureFlow [p₁, p₂] μ0 = _
  have hflow2 : attnMeasureFlow [p₁, p₂] μ0 = attnStep p₂ (attnStep p₁ μ0) := rfl
  rw [hflow2, hstep1, hstep2, hνdef, Measure.map_map hΦ₂m hΦ₁m]

variable [NeZero d]

set_option maxHeartbeats 1200000 in
/-- **The two-phase rotation, mean-field form.** For `d ≥ 2`, a unit missing direction `ω`, a gap
`δ ∈ (0,1]`, and any horizon `T > 0`, there is a two-block MEAN-FIELD schedule `θ` such that for
every sphere-supported probability measure, the composed flow map carries every point missing `ω`
by the gap `δ` into the orthant. Both phases run for time `T` (`pParkScaled`'s own `duration`
field), so the total `durationSum θ = 2 * T`, exposed for callers that need to hit an exact
horizon. -/
theorem exists_twoPhase_attnMapsTo_orthant (hd : 2 ≤ d) {ω : Eucl d} (hω : ‖ω‖ = 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {T : ℝ} (hT : 0 < T) :
    ∃ θ : AttnSchedule d, AttnSchedule.switches θ = 2 ∧ AttnSchedule.durationSum θ = 2 * T ∧
      ∀ μ0 : Measure (Eucl d), [IsProbabilityMeasure μ0] → μ0 (sphere d)ᶜ = 0 →
      ∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ μ0 = μ0.map Φ ∧
        Set.MapsTo Φ (sphere d) (sphere d) ∧
        ∀ x ∈ sphere d, (⟪ω, x⟫ : ℝ) ≤ 1 - δ → ∀ i, 0 < Φ x i := by
  obtain ⟨α, c, hα, hc, hcoord, hαω⟩ := exists_unit_orthant_ne hd ω
  have hωs : ω ∈ sphere d := by
    rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hω
  have hαs : α ∈ sphere d := by
    rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hα
  set η : ℝ := 1 - ⟪α, ω⟫ with hη_def
  have hinner_le : (⟪α, ω⟫ : ℝ) ≤ 1 := by
    have := abs_real_inner_le_norm α ω
    rw [hα, hω, one_mul] at this
    exact (abs_le.mp this).2
  have hinner_ge : (-1 : ℝ) ≤ ⟪α, ω⟫ := by
    have := abs_real_inner_le_norm α ω
    rw [hα, hω, one_mul] at this
    exact (abs_le.mp this).1
  have hη0 : 0 < η := by
    rcases eq_or_ne α (-ω) with hneg | hneg
    · have : (⟪α, ω⟫ : ℝ) = -1 := by
        rw [hneg, inner_neg_left, inner_self_eq_one_of_mem_sphere hωs]
      rw [hη_def, this]; norm_num
    · have := inner_mem_Ioo_of_ne hαs hωs hαω hneg
      rw [hη_def]; linarith [this.2]
  have hη2 : η ≤ 2 := by rw [hη_def]; linarith
  have hc1 : c ≤ 1 := by
    have hi0 : (0 : ℕ) < d := lt_of_lt_of_le two_pos hd
    have hcs := abs_real_inner_le_norm (EuclideanSpace.single (⟨0, hi0⟩ : Fin d) (1 : ℝ)) α
    have hsingle : ⟪EuclideanSpace.single (⟨0, hi0⟩ : Fin d) (1 : ℝ), α⟫ = α ⟨0, hi0⟩ := by
      simp [EuclideanSpace.inner_single_left]
    have hnorm1 : ‖EuclideanSpace.single (⟨0, hi0⟩ : Fin d) (1 : ℝ)‖ = 1 := by
      simp
    rw [hsingle, hnorm1, one_mul, hα] at hcs
    have := (abs_le.mp hcs).2
    linarith [hcoord ⟨0, hi0⟩]
  have hnegω : ‖-ω‖ = 1 := by rw [norm_neg]; exact hω
  have hm₁R : (-1 : ℝ) < δ - 1 := by linarith
  have hm₁1 : δ - 1 < 1 := by linarith
  have hb₁ : (1 - η ^ 2 / 8 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨A₁, hA₁, hMaps₁⟩ :=
    exists_scaledGatedBlock_mapsTo_cap hnegω (le_refl (-1 : ℝ)) hT hm₁R hm₁1 hb₁
  have hm₂R : (-1 : ℝ) < η / 2 - 1 := by linarith
  have hm₂1 : η / 2 - 1 < 1 := by linarith
  have hb₂ : (1 - c ^ 2 / 8 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨A₂, hA₂, hMaps₂⟩ :=
    exists_scaledGatedBlock_mapsTo_cap hα (le_refl (-1 : ℝ)) hT hm₂R hm₂1 hb₂
  set B₁ := scaledGatedBlock hA₁ hnegω hnegω (le_refl (-1 : ℝ)) hT.le with hB₁
  set B₂ := scaledGatedBlock hA₂ hα hα (le_refl (-1 : ℝ)) hT.le with hB₂
  set p₁ := pParkScaled A₁ (-ω) (-ω) (-1 : ℝ) T hT.le with hp₁
  set p₂ := pParkScaled A₂ α α (-1 : ℝ) T hT.le with hp₂
  have hp₁dur : p₁.duration = T := rfl
  have hp₂dur : p₂.duration = T := rfl
  have hdursum : AttnSchedule.durationSum ([p₁, p₂] : AttnSchedule d) = 2 * T := by
    simp only [AttnSchedule.durationSum, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, hp₁dur, hp₂dur]
    ring
  refine ⟨[p₁, p₂], rfl, hdursum, ?_⟩
  intro μ0 _ hμ0S
  obtain ⟨Φ₁, Φ₂, hΦ₁spec, hΦ₂spec, hcomp⟩ := attnMeasureFlow_two_eq_map_comp p₁ p₂ hμ0S
  refine ⟨Φ₂ p₂.duration ∘ Φ₁ p₁.duration, ?_, hcomp, ?_, ?_⟩
  · exact (hΦ₂spec.measurable p₂.duration ⟨p₂.duration_nonneg, le_rfl⟩).comp
      (hΦ₁spec.measurable p₁.duration ⟨p₁.duration_nonneg, le_rfl⟩)
  · exact (hΦ₂spec.sphere_bijOn p₂.duration ⟨p₂.duration_nonneg, le_rfl⟩).mapsTo.comp
      (hΦ₁spec.sphere_bijOn p₁.duration ⟨p₁.duration_nonneg, le_rfl⟩).mapsTo
  intro x hxs hxgap i
  -- phase 1: identify the mean-field step with `B₁.blockFlow T` on the sphere
  have hΦ₁eq : Φ₁ p₁.duration x = B₁.blockFlow T x := by
    rw [hp₁dur]
    exact attnFlow_eq_blockFlow_scaledGatedBlock hA₁ hnegω hnegω (le_refl (-1 : ℝ)) hT.le hμ0S
      Φ₁ hΦ₁spec hxs ⟨hT.le, le_rfl⟩
  set y := B₁.blockFlow T x with hy_def
  have hx₁ : x ∈ {z | z ∈ sphere d ∧ (δ - 1 : ℝ) ≤ ⟪z, -ω⟫} := by
    refine ⟨hxs, ?_⟩
    rw [inner_neg_right]
    rw [real_inner_comm]
    linarith
  have hy₁ := hMaps₁ hx₁
  have hys : y ∈ sphere d := B₁.blockFlow_mem_sphere hxs hT.le
  have hy_cap : (1 - (η / 2) ^ 2 / 2 : ℝ) ≤ ⟪-ω, y⟫ := by
    have h8 : ((η / 2) ^ 2 / 2 : ℝ) = η ^ 2 / 8 := by ring
    rw [h8]
    rw [real_inner_comm]
    exact hy₁
  have hnegωs : -ω ∈ sphere d := by
    rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hnegω
  have hηhalf : (0 : ℝ) < η / 2 := by linarith
  have hy_dist : dist y (-ω) ≤ η / 2 :=
    dist_le_of_inner_cap hnegω hys hηhalf hy_cap
  have hy₂ : y ∈ {z | z ∈ sphere d ∧ (η / 2 - 1 : ℝ) ≤ ⟪z, α⟫} := by
    refine ⟨hys, ?_⟩
    have hsplit : (⟪α, y⟫ : ℝ) = ⟪α, -ω⟫ + ⟪α, y - -ω⟫ := by
      rw [inner_sub_right]; ring
    have hfirst : (⟪α, -ω⟫ : ℝ) = η - 1 := by
      rw [inner_neg_right, hη_def]; ring
    have hsecond : -(‖y - -ω‖) ≤ (⟪α, y - -ω⟫ : ℝ) := by
      have hcs := abs_real_inner_le_norm α (y - -ω)
      rw [hα, one_mul] at hcs
      linarith [(abs_le.mp hcs).1]
    have hnorm_le : ‖y - -ω‖ ≤ η / 2 := by
      rw [← dist_eq_norm]; exact hy_dist
    have : (η - 1) - η / 2 ≤ (⟪α, y⟫ : ℝ) := by
      rw [hsplit, hfirst]
      linarith
    rw [real_inner_comm]
    linarith
  -- phase 2: identify the second mean-field step with `B₂.blockFlow T` on the sphere
  have hΦ₂eq : Φ₂ p₂.duration y = B₂.blockFlow T y := by
    rw [hp₂dur]
    haveI : IsProbabilityMeasure (μ0.map (Φ₁ p₁.duration)) :=
      Measure.isProbabilityMeasure_map
        (hΦ₁spec.measurable p₁.duration ⟨p₁.duration_nonneg, le_rfl⟩).aemeasurable
    have hνS : (μ0.map (Φ₁ p₁.duration)) (sphere d)ᶜ = 0 := by
      have hmscompl : MeasurableSet (sphere d)ᶜ := Metric.isClosed_sphere.measurableSet.compl
      rw [Measure.map_apply (hΦ₁spec.measurable p₁.duration ⟨p₁.duration_nonneg, le_rfl⟩) hmscompl]
      apply measure_mono_null _ hμ0S
      intro w hw hws
      exact hw ((hΦ₁spec.sphere_bijOn p₁.duration ⟨p₁.duration_nonneg, le_rfl⟩).mapsTo hws)
    exact attnFlow_eq_blockFlow_scaledGatedBlock hA₂ hα hα (le_refl (-1 : ℝ)) hT.le hνS
      Φ₂ hΦ₂spec hys ⟨hT.le, le_rfl⟩
  have hz₁ := hMaps₂ hy₂
  set z := B₂.blockFlow T y with hz_def
  have hzs : z ∈ sphere d := B₂.blockFlow_mem_sphere hys hT.le
  have hz_cap : (1 - c ^ 2 / 8 : ℝ) ≤ ⟪α, z⟫ := by
    rw [real_inner_comm]
    exact hz₁
  show 0 < (Φ₂ p₂.duration (Φ₁ p₁.duration x)) i
  rw [hΦ₁eq, hΦ₂eq]
  exact cap_pos_coords hα hc hcoord hzs hz_cap i

end MeasureToMeasure.Leaves
