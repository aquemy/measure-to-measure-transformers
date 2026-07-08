import MeasureToMeasure.Foundations.TrajectoryFlow

/-!
# The trajectory-flow pushforward map, sphere-supported and measurable (M3b existence, leaf E3h)

The outer self-consistency map `Ξ` needs, at each time `t`, to push an initial datum `μ₀` forward
along the trajectory-composed flow and land back in `SphereProb d`. Two gaps stand in the way of
`Measure.map`: `trajectoryFlow` is only defined (and only `LipschitzOnWith`) on the closed unit
ball, not globally, so it is not obviously `Measurable` as a map on all of `Eucl d`; and even given
measurability, the pushforward measure needs to be shown sphere-supported.

This leaf closes both gaps by extending `trajectoryFlow` off the ball via the radial retraction
`ballProj` (the same trick `rawFieldBall`/`attnFieldExt` used off-sphere in leaf E2a): `ballProj`
is globally `1`-Lipschitz (`lipschitzWith_ballProj`) and always lands in the closed unit ball
(`norm_ballProj_le`), so `trajectoryFlowExt := trajectoryFlow ∘ ballProj` is *globally* continuous
(via `ContinuousOn.comp_continuous`, gluing the ball's `LipschitzOnWith`-continuity to the global
retraction), hence `Measurable`, and it agrees with `trajectoryFlow` exactly on the ball (in
particular on the sphere, where the McKean-Vlasov dynamics actually happens) since `ballProj` is the
identity there.

Sphere-support of the pushforward (`sphere_supported_map_trajectoryFlowExt`) is then immediate from
`trajectoryFlow_mem_sphere` (leaf E3g) plus the agreement identity: `μ₀`-a.e. every point is on the
sphere, where `trajectoryFlowExt` agrees with the sphere-preserving `trajectoryFlow`.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **The globally-extended trajectory flow.** `trajectoryFlow` retracted through `ballProj`, making
it continuous (hence measurable) on all of `Eucl d`, while agreeing with `trajectoryFlow` on the
closed unit ball. -/
noncomputable def trajectoryFlowExt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (t : ℝ) (x : Eucl d) : Eucl d :=
  trajectoryFlow p hT η (ballProj x) t

/-- On the sphere, the extension agrees with `trajectoryFlow` (since `ballProj` fixes the ball). -/
theorem trajectoryFlowExt_eq_of_mem_sphere (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} {x : Eucl d} (hx : x ∈ sphere d) :
    trajectoryFlowExt p hT η t x = trajectoryFlow p hT η x t := by
  unfold trajectoryFlowExt
  rw [ballProj_eq_self (norm_eq_one_of_mem_sphere hx).le]

/-- **The extended trajectory flow is globally continuous** at every valid time `t`: gluing the
ball's `LipschitzOnWith`-continuity (`exists_lipschitzOnWith_trajectoryFlow`) to the globally
continuous retraction `ballProj` (`lipschitzWith_ballProj`, which always lands in the ball). -/
theorem continuous_trajectoryFlowExt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (trajectoryFlowExt p hT η t) := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_trajectoryFlow p hT η
  have hLip := hL t ht
  have hball : ∀ x, ballProj x ∈ Metric.closedBall (0 : Eucl d) (1 : ℝ≥0) := fun x => by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact_mod_cast norm_ballProj_le x
  exact hLip.continuousOn.comp_continuous lipschitzWith_ballProj.continuous hball

theorem measurable_trajectoryFlowExt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Measurable (trajectoryFlowExt p hT η t) :=
  (continuous_trajectoryFlowExt p hT η ht).measurable

/-- **The pushforward at time `t` is sphere-supported.** `μ₀`-a.e. every point is on the sphere
(`hμ₀`), where the extended flow agrees with `trajectoryFlow`, which preserves the sphere
(`trajectoryFlow_mem_sphere`). -/
theorem sphere_supported_map_trajectoryFlowExt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (μ₀.map (trajectoryFlowExt p hT η t)) (sphere d)ᶜ = 0 := by
  rw [Measure.map_apply (measurable_trajectoryFlowExt p hT η ht) (measurableSet_sphere d).compl]
  apply measure_mono_null _ hμ₀
  intro x hxmem
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hxmem ⊢
  intro hxsphere
  apply hxmem
  rw [trajectoryFlowExt_eq_of_mem_sphere p hT η hxsphere]
  exact trajectoryFlow_mem_sphere p hT η hxsphere ht

/-- **The pushforward map.** Pushing a sphere-supported probability datum `μ₀` forward along the
extended trajectory-composed flow at time `t` lands back in `SphereProb d`. This is what the outer
self-consistency map `Ξ` evaluates at each `t`. -/
noncomputable def pushforwardAt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) : SphereProb d :=
  ⟨μ₀.map (trajectoryFlowExt p hT η t),
    Measure.isProbabilityMeasure_map (measurable_trajectoryFlowExt p hT η ht).aemeasurable,
    sphere_supported_map_trajectoryFlowExt p hT η μ₀ hμ₀ ht⟩

end MeasureToMeasure.Foundations
