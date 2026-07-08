import MeasureToMeasure.Foundations.TrajectoryFlowPushforward
import MeasureToMeasure.Foundations.MeanFieldWellPosed

/-!
# The self-consistency step map, continuous in time (M3b existence, leaf E3i)

Assembles leaf E3h's `pushforwardAt` into a genuine `ContinuousMap`
`selfConsistencyStepCM : C([0,T], SphereProb d)`, the object the outer Picard self-consistency map
`Ξ` (E3+) will act on: `selfConsistencyStep p hT η μ₀ hμ₀ t := pushforwardAt p hT η μ₀ hμ₀ t.2`,
i.e. the trial trajectory `η` pushed forward through its own frozen-field flow, evaluated at each
time `t`, starting from the fixed initial datum `μ₀`.

The continuity argument is a coupling-bound + dominated-convergence combination, entirely parallel
to the mean-field UNIQUENESS Grönwall machinery already banked in `MeanFieldWellPosed.lean`
(`meanFlowDist_continuousOn`, `W1_toReal_map_le_integral_norm`), but for the *trajectory-composed*
flow instead of two competing `IsMeanFieldFlow` solutions:

* `dist_pushforwardAt_le_integral` -- the `W₁`-coupling bound (`W1_toReal_map_le_integral_norm`)
  turns the target `dist` into a `μ₀`-averaged pointwise displacement integral;
* `continuousOn_integral_norm_trajectoryFlowExt_sub` -- that integral is continuous in `t` at any
  `t₀`, by dominated convergence: the integrand is uniformly bounded by `2` (both points on the
  sphere, `norm_trajectoryFlowExt_sub_le_two`) and, `μ₀`-a.e. (i.e. on the sphere), continuous in
  `t` (`continuousOn_trajectoryFlowExt_of_mem_sphere`, from leaf E3g's `continuousOn_trajectoryFlow`
  transported through the E3h ball-extension identity);
* the integral vanishes at `t = t₀` (the integrand is identically `0`), so continuity of the
  integral gives `dist (pushforwardAt ... t) (pushforwardAt ... t₀) → 0` as `t → t₀` by `squeeze_zero`
  against the coupling bound -- exactly `Continuous` for the subtype-valued map.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

theorem continuousOn_trajectoryFlowExt_of_mem_sphere (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) :
    ContinuousOn (fun t : ℝ => trajectoryFlowExt p hT η t x) (Set.Icc (0 : ℝ) T) := by
  have heq : ∀ s ∈ Set.Icc (0 : ℝ) T, trajectoryFlowExt p hT η s x = trajectoryFlow p hT η x s :=
    fun _ _ => trajectoryFlowExt_eq_of_mem_sphere p hT η hx
  exact (continuousOn_trajectoryFlow p hT η hx).congr heq

/-- Both endpoints of the extended flow at two valid times land on the sphere (via
`trajectoryFlow_mem_sphere`), so their difference is bounded by `2` -- the domination the
continuity-in-`t` argument needs. -/
theorem norm_trajectoryFlowExt_sub_le_two (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) {x : Eucl d} (hx : x ∈ sphere d) :
    ‖trajectoryFlowExt p hT η s x - trajectoryFlowExt p hT η t x‖ ≤ 2 := by
  rw [trajectoryFlowExt_eq_of_mem_sphere p hT η hx, trajectoryFlowExt_eq_of_mem_sphere p hT η hx]
  have h1 : trajectoryFlow p hT η x s ∈ sphere d := trajectoryFlow_mem_sphere p hT η hx hs
  have h2 : trajectoryFlow p hT η x t ∈ sphere d := trajectoryFlow_mem_sphere p hT η hx ht
  calc ‖trajectoryFlow p hT η x s - trajectoryFlow p hT η x t‖
      ≤ ‖trajectoryFlow p hT η x s‖ + ‖trajectoryFlow p hT η x t‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_eq_one_of_mem_sphere h1, norm_eq_one_of_mem_sphere h2]; norm_num

/-- **Continuity in `t` of the `μ₀`-averaged displacement integral**, at any `t₀` -- the dominated-
convergence step of the coupling argument. -/
theorem continuousOn_integral_norm_trajectoryFlowExt_sub (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) :
    ContinuousWithinAt
      (fun t => ∫ x, ‖trajectoryFlowExt p hT η t x - trajectoryFlowExt p hT η t₀ x‖ ∂μ₀)
      (Set.Icc (0 : ℝ) T) t₀ := by
  refine continuousWithinAt_of_dominated (bound := fun _ => (2 : ℝ)) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((measurable_trajectoryFlowExt p hT η ht).sub
      (measurable_trajectoryFlowExt p hT η ht₀)).norm.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine ae_of_sphere_supported hμ₀ (fun x hx => ?_)
    rw [norm_norm]
    exact norm_trajectoryFlowExt_sub_le_two p hT η ht ht₀ hx
  · refine ae_of_sphere_supported hμ₀ (fun x hx => ?_)
    have h1 : ContinuousWithinAt (fun t => trajectoryFlowExt p hT η t x)
        (Set.Icc (0 : ℝ) T) t₀ :=
      continuousOn_trajectoryFlowExt_of_mem_sphere p hT η hx t₀ ht₀
    exact (h1.sub continuousWithinAt_const).norm

/-- **The `W₁` coupling bound**, specialized to the pushforward map: `dist` between the two
pushforwards is bounded by the `μ₀`-averaged pointwise displacement integral. -/
theorem dist_pushforwardAt_le_integral (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t t₀ : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T)
    (hint : Integrable (fun x => ‖trajectoryFlowExt p hT η t x - trajectoryFlowExt p hT η t₀ x‖)
      μ₀) :
    dist (pushforwardAt p hT η μ₀ hμ₀ ht) (pushforwardAt p hT η μ₀ hμ₀ ht₀)
      ≤ ∫ x, ‖trajectoryFlowExt p hT η t x - trajectoryFlowExt p hT η t₀ x‖ ∂μ₀ := by
  unfold pushforwardAt
  rw [SphereProb.dist_eq]
  exact W1_toReal_map_le_integral_norm (measurable_trajectoryFlowExt p hT η ht)
    (measurable_trajectoryFlowExt p hT η ht₀) hint

theorem integrable_norm_trajectoryFlowExt_sub (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t t₀ : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun x => ‖trajectoryFlowExt p hT η t x - trajectoryFlowExt p hT η t₀ x‖) μ₀ := by
  refine Integrable.mono' (integrable_const (2 : ℝ))
    (((measurable_trajectoryFlowExt p hT η ht).sub
      (measurable_trajectoryFlowExt p hT η ht₀)).norm.aestronglyMeasurable) ?_
  refine ae_of_sphere_supported hμ₀ (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_trajectoryFlowExt_sub_le_two p hT η ht ht₀ hx

/-- **`dist (pushforwardAt t) (pushforwardAt t₀) → 0` as `t → t₀`** -- the coupling bound squeezed
between `0` and the (vanishing-at-`t₀`, continuous) displacement integral. -/
theorem tendsto_pushforwardAt_dist (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) :
    Filter.Tendsto (fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) T} =>
        dist (pushforwardAt p hT η μ₀ hμ₀ t.2) (pushforwardAt p hT η μ₀ hμ₀ ht₀))
      (nhds (⟨t₀, ht₀⟩ : {t : ℝ // t ∈ Set.Icc (0 : ℝ) T})) (nhds 0) := by
  have hcontInt := continuousOn_integral_norm_trajectoryFlowExt_sub p hT η μ₀ hμ₀ ht₀
  have hInt0 : (∫ x, ‖trajectoryFlowExt p hT η t₀ x - trajectoryFlowExt p hT η t₀ x‖ ∂μ₀) = 0 := by
    simp
  have h2 : Filter.Tendsto (fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) T} => (t : ℝ))
      (nhds ⟨t₀, ht₀⟩) (nhdsWithin t₀ (Set.Icc (0 : ℝ) T)) := by
    rw [nhdsWithin, tendsto_inf]
    exact ⟨continuousAt_subtype_val, by rw [tendsto_principal]; filter_upwards with t; exact t.2⟩
  have hcontIntAtVal : Filter.Tendsto
      (fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) T} =>
        ∫ x, ‖trajectoryFlowExt p hT η t.1 x - trajectoryFlowExt p hT η t₀ x‖ ∂μ₀)
      (nhds ⟨t₀, ht₀⟩) (nhds 0) := by
    have := hcontInt.tendsto.comp h2
    rwa [hInt0] at this
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun t => dist_pushforwardAt_le_integral p hT η μ₀ hμ₀ t.2 ht₀
      (integrable_norm_trajectoryFlowExt_sub p hT η μ₀ hμ₀ t.2 ht₀))
    hcontIntAtVal

/-- **The self-consistency step**: the trial trajectory `η`, pushed forward through its own
frozen-field flow, evaluated at each time -- what the outer Picard map (E3+) iterates. -/
noncomputable def selfConsistencyStep (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) (t : Set.Icc (0 : ℝ) T) : SphereProb d :=
  pushforwardAt p hT η μ₀ hμ₀ t.2

theorem continuous_selfConsistencyStep (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) :
    Continuous (selfConsistencyStep p hT η μ₀ hμ₀) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  exact tendsto_pushforwardAt_dist p hT η μ₀ hμ₀ t₀.2

/-- **The self-consistency step, packaged as a `ContinuousMap`.** The object `Ξ` (the outer Picard
map, E3+) will send `η` to. -/
noncomputable def selfConsistencyStepCM (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) : C(Set.Icc (0 : ℝ) T, SphereProb d) :=
  ⟨selfConsistencyStep p hT η μ₀ hμ₀, continuous_selfConsistencyStep p hT η μ₀ hμ₀⟩

end MeasureToMeasure.Foundations
