import MeasureToMeasure.Foundations.SelfConsistencyFixedPoint
import MeasureToMeasure.Foundations.TrajectoryFlowPadded
import Mathlib.Analysis.ODE.Gronwall

/-!
# Injectivity on the sphere, and the fixed-point self-consistency identity (M3b existence, leaf E3p)

Two more pieces towards assembling `IsMeanFieldFlow` from the E3n fixed point:

* **`trajectoryFlowPadded_injOn`**: at each time `t`, `x ↦ trajectoryFlowPadded p hT η x t` is
  injective on the sphere — the `InjOn` half of `IsMeanFieldFlow.sphere_bijOn`. Proved via
  `ODE_solution_unique_of_mem_Icc_left`: two solutions of the *same* field that agree at the
  *right* endpoint `t` of `[0,t]` agree throughout, in particular at `0` — so `Φ_t x = Φ_t x'`
  forces `x = x'`. This is the mirror image of `trajectoryFlowPadded_eq_trajectoryFlow`'s
  right-endpoint uniqueness (leaf E3o), just anchored at the other end of the interval.

* **`eta_eq_pushforward`**: the identity that makes "fixed point of `Ξ`" mean "self-consistent
  McKean-Vlasov solution" rather than just an abstract equation. If `η` is a fixed point of the
  self-consistency map (`selfConsistencyStepCM p hT η μ₀ hμ₀ = η`, leaf E3n), then `η t` really *is*
  the pushforward `(Φ_t)_#μ₀` of the point flow through `η` itself — not merely equal to some other
  measure that happens to satisfy the fixed-point equation. This is what lets `IsMeanFieldFlow.deriv`
  (which needs the velocity evaluated at `p.field (μ₀.map (Φ t)) (Φ t x)`, the *actual* current
  pushforward) be identified with `trajectoryField`'s velocity along `η` (which is evaluated at `η t`
  by definition).

`SurjOn` (the remaining half of `sphere_bijOn`) needs a genuine backward-flow construction — not yet
attempted, and scoped as its own next step (see campaign memory).

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **Injectivity on the sphere.** Two sphere-supported starting points that flow to the same place
at time `t` must have been equal, by backward ODE uniqueness (anchored at the *right* endpoint of
`[0,t]`, mirroring how leaf E3o's forward identity anchors at the left endpoint). -/
theorem trajectoryFlowPadded_injOn (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Set.InjOn (fun x => trajectoryFlowPadded p hT η x t) (sphere d) := by
  intro x hx x' hx' heq
  have hEq : Set.EqOn (trajectoryFlowPadded p hT η x) (trajectoryFlowPadded p hT η x')
      (Set.Icc (0 : ℝ) t) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := trajectoryField p hT η) (s := fun _ => Set.univ)
      (K := (Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
        + Real.toNNReal (5 * fieldBallBound p)))
    · intro s hs
      haveI := (η (Set.projIcc 0 T hT s)).property.1
      exact (attnFieldExt_lipschitz p (η (Set.projIcc 0 T hT s)).val
        (η (Set.projIcc 0 T hT s)).property.2).lipschitzOnWith
    · exact (continuousOn_trajectoryFlowPadded p hT η hx).mono
        (fun s hs => ⟨by linarith [hs.1], by linarith [ht.2, hs.2]⟩)
    · intro s hs
      have hst : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
      exact (hasDerivAt_trajectoryFlowPadded p hT η hx hst).hasDerivWithinAt
    · intro s _; trivial
    · exact (continuousOn_trajectoryFlowPadded p hT η hx').mono
        (fun s hs => ⟨by linarith [hs.1], by linarith [ht.2, hs.2]⟩)
    · intro s hs
      have hst : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
      exact (hasDerivAt_trajectoryFlowPadded p hT η hx' hst).hasDerivWithinAt
    · intro s _; trivial
    · exact heq
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_refl 0, ht.1⟩
  have := hEq h0
  rwa [trajectoryFlowPadded_zero p hT η hx, trajectoryFlowPadded_zero p hT η hx'] at this

/-- **The fixed-point self-consistency identity.** If `η` is a fixed point of the self-consistency
map, `η t` genuinely is the pushforward of `μ₀` along the point flow through `η` itself. -/
theorem eta_eq_pushforward (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T) (μ₀ : Measure (Eucl d))
    [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d))
    (hfix : selfConsistencyStepCM p hT η μ₀ hμ₀ = η)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (η ⟨t, ht⟩).val = μ₀.map (fun x => trajectoryFlow p hT η x t) := by
  have hcongr : (selfConsistencyStepCM p hT η μ₀ hμ₀) ⟨t, ht⟩ = η ⟨t, ht⟩ :=
    congrFun (congrArg (DFunLike.coe) hfix) ⟨t, ht⟩
  have hstep : (selfConsistencyStepCM p hT η μ₀ hμ₀) ⟨t, ht⟩ = pushforwardAt p hT η μ₀ hμ₀ ht := rfl
  rw [hstep] at hcongr
  rw [← hcongr]
  show μ₀.map (trajectoryFlowExt p hT η t) = μ₀.map (fun x => trajectoryFlow p hT η x t)
  apply Measure.map_congr
  apply ae_of_sphere_supported hμ₀
  intro x hx
  exact trajectoryFlowExt_eq_of_mem_sphere p hT η hx

end MeasureToMeasure.Foundations
