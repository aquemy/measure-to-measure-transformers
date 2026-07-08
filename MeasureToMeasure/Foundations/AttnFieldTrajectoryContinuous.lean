import MeasureToMeasure.Foundations.AttnFieldMeasureLipschitz
import MeasureToMeasure.Foundations.SphereProbComplete

/-!
# Continuity in time of the field along a trajectory (M3b existence, leaf E3d)

The outer Picard self-consistency map (E3+) will need to invoke Mathlib's *time-dependent*
`IsPicardLindelof` (`f : ℝ → E → E`, Lipschitz in `x` at every `t`, continuous in `t` at every `x`) for
the field `t ↦ attnFieldExt p (η t).val x`, evaluated along a candidate measure trajectory
`η : C([0,T], SphereProb d)`. Lipschitz-in-`x` (uniformly over the measure) is already banked
(`attnFieldExt_lipschitz`); this leaf supplies the missing continuity-in-`t` clause, directly from
leaf E3c's global measure modulus (`norm_attnFieldExt_sub_measure_le`) and `SphereProb.dist_eq`
(`dist μ ν = (W₁ μ.val ν.val).toReal`): since `η` is continuous into `SphereProb d` and the field is
Lipschitz in the *measure* at every fixed `x`, the composite `t ↦ attnFieldExt p (η t).val x` is
continuous by a direct `ε`-`δ` transfer (no new geometry, purely the composition of a continuous map
with a Lipschitz one).

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **The field is continuous in time along any continuous measure trajectory.** For a fixed point
`x` and a continuous path `η : C([0,T], SphereProb d)`, the composite `t ↦ attnFieldExt p (η t) x` is
continuous — the `continuousOn` clause `IsPicardLindelof` needs for the outer (measure-trajectory)
Picard map. -/
theorem continuous_attnFieldExt_comp_trajectory (p : AttnParams d) {T : ℝ}
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (x : Eucl d) :
    Continuous (fun t : Set.Icc (0 : ℝ) T => attnFieldExt p (η t).val x) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  set C := (1 + ‖x‖ ^ 2) *
    (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) with hC
  have hCnn : 0 ≤ C := by positivity
  have hcont : ContinuousAt (fun t : Set.Icc (0 : ℝ) T => dist (η t) (η t₀)) t₀ :=
    Continuous.continuousAt (Continuous.dist η.continuous continuous_const)
  have hbound : ∀ t : Set.Icc (0 : ℝ) T,
      dist (attnFieldExt p (η t).val x) (attnFieldExt p (η t₀).val x) ≤ C * dist (η t) (η t₀) := by
    intro t
    haveI := (η t).property.1
    haveI := (η t₀).property.1
    rw [dist_eq_norm]
    have hle := norm_attnFieldExt_sub_measure_le p (η t).property.2 (η t₀).property.2
      (SphereProb.w1dist_ne_top (η t) (η t₀)) x
    rw [SphereProb.dist_eq]
    calc ‖attnFieldExt p (η t).val x - attnFieldExt p (η t₀).val x‖
        ≤ (1 + ‖x‖ ^ 2) *
          (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) *
            (W1 (η t).val (η t₀).val).toReal) := hle
      _ = C * (W1 (η t).val (η t₀).val).toReal := by rw [hC]; ring
  rcases eq_or_lt_of_le hCnn with hC0 | hCpos
  · refine ⟨1, one_pos, fun t _ => ?_⟩
    calc dist (attnFieldExt p (η t).val x) (attnFieldExt p (η t₀).val x)
        ≤ C * dist (η t) (η t₀) := hbound t
      _ = 0 := by rw [← hC0]; ring
      _ < ε := hε
  · rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hδcond⟩ := hcont (ε / C) (by positivity)
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have hdist_small : dist (dist (η t) (η t₀)) (dist (η t₀) (η t₀)) < ε / C := hδcond ht
    simp only [dist_self, dist_zero_right, Real.norm_eq_abs] at hdist_small
    have hη_close : dist (η t) (η t₀) < ε / C := by rwa [abs_of_nonneg dist_nonneg] at hdist_small
    calc dist (attnFieldExt p (η t).val x) (attnFieldExt p (η t₀).val x)
        ≤ C * dist (η t) (η t₀) := hbound t
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hη_close hCpos
      _ = ε := by field_simp

end MeasureToMeasure.Foundations
