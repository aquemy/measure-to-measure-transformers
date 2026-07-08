import MeasureToMeasure.Foundations.TrajectoryFlow
import Mathlib.Analysis.ODE.Gronwall

/-!
# The padded trajectory flow: genuine `HasDerivAt` at every `t ∈ [0,T]` (M3b existence, leaf E3o)

`IsMeanFieldFlow.deriv` (`Attention.lean:128`) needs a full two-sided `HasDerivAt` at every
`t ∈ Icc 0 p.duration`, including the endpoints `t = 0` and `t = p.duration`. But `trajectoryFlow`
(leaf E3g) only supplies `HasDerivWithinAt _ (Icc 0 T)`, which does **not** upgrade to `HasDerivAt`
at the endpoints — `Icc 0 T` is never a neighborhood of `0` or `T` in `ℝ`.

This leaf closes the gap by re-running the same Picard-Lindelöf construction on a **padded**
interval `[-1, T+1]`, so that every `t ∈ [0,T]` is an *interior* point where `Icc (-1) (T+1)` genuinely
is a neighborhood (`Icc_mem_nhds`), and `HasDerivWithinAt.hasDerivAt` applies directly. The padded
flow `trajectoryFlowPadded` is then identified with the original `trajectoryFlow` on `[0,T]` via
`ODE_solution_unique_of_mem_Icc_right` (both solve the same field, agree at `t = 0`), so every
already-banked property of `trajectoryFlow` (sphere invariance, `x`-Lipschitz-ness) transfers for
free through the equality.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- Same Picard-Lindelöf data as `trajectoryField_isPicardLindelof` (leaf E3e), but on the padded
interval `[-1, T+1]` — so `t = 0` and `t = T` are interior points. -/
theorem trajectoryField_isPicardLindelof_padded (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (x₀ : Eucl d) (r : ℝ≥0) :
    IsPicardLindelof (trajectoryField p hT η) (tmin := (-1 : ℝ)) (tmax := T + 1)
      ⟨0, Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩
      x₀ (5 * fieldBallBound p * (T + 1) + r).toNNReal r (5 * fieldBallBound p).toNNReal
      (Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
        + Real.toNNReal (5 * fieldBallBound p)) where
  lipschitzOnWith := fun t _ => by
    haveI := (η (Set.projIcc 0 T hT t)).property.1
    exact (attnFieldExt_lipschitz p (η (Set.projIcc 0 T hT t)).val
      (η (Set.projIcc 0 T hT t)).property.2).lipschitzOnWith
  continuousOn := by
    intro x _
    have hcont := continuous_attnFieldExt_comp_trajectory p η x
    have hproj : Continuous (Set.projIcc 0 T hT (α := ℝ)) := continuous_projIcc
    exact (hcont.comp hproj).continuousOn
  norm_le := fun t _ x _ => by
    haveI := (η (Set.projIcc 0 T hT t)).property.1
    have h := norm_attnFieldExt_le p (η (Set.projIcc 0 T hT t)).val
      (η (Set.projIcc 0 T hT t)).property.2 x
    rw [Real.coe_toNNReal _ (five_bound_nonneg p)]
    exact h
  mul_max_le := by
    have h0 : (0 : ℝ) ≤ 5 * fieldBallBound p := five_bound_nonneg p
    have hLcoe : ((5 * fieldBallBound p).toNNReal : ℝ) = 5 * fieldBallBound p :=
      Real.coe_toNNReal _ h0
    have hmax : max ((T + 1 : ℝ) - 0) (0 - (-1)) = T + 1 := by
      have heq1 : (T + 1 : ℝ) - 0 = T + 1 := by ring
      have heq2 : (0 : ℝ) - (-1) = 1 := by ring
      rw [heq1, heq2, max_eq_left (by linarith)]
    have h1 : (0 : ℝ) ≤ 5 * fieldBallBound p * (T + 1) := mul_nonneg h0 (by linarith)
    have h2 : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
    have harg : (0 : ℝ) ≤ 5 * fieldBallBound p * (T + 1) + r := by linarith
    have hacoe : ((5 * fieldBallBound p * (T + 1) + r).toNNReal : ℝ)
        = 5 * fieldBallBound p * (T + 1) + r := Real.coe_toNNReal _ harg
    rw [hmax, hLcoe, hacoe]
    nlinarith [h1, h2]

/-- **The padded trajectory flow.** Same construction as `trajectoryFlow`, but on `[-1, T+1]`. -/
noncomputable def trajectoryFlowPadded (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) : Eucl d → ℝ → Eucl d :=
  Classical.choose
    (IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
      (trajectoryField_isPicardLindelof_padded p hT η (0 : Eucl d) 1))

theorem trajectoryFlowPadded_spec (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    (∀ x ∈ Metric.closedBall (0 : Eucl d) (1 : ℝ≥0), trajectoryFlowPadded p hT η x 0 = x ∧
        ∀ t ∈ Set.Icc (-1 : ℝ) (T + 1), HasDerivWithinAt (trajectoryFlowPadded p hT η x)
          (trajectoryField p hT η t (trajectoryFlowPadded p hT η x t))
          (Set.Icc (-1 : ℝ) (T + 1)) t) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        LipschitzOnWith L' (trajectoryFlowPadded p hT η · t)
          (Metric.closedBall (0 : Eucl d) (1 : ℝ≥0)) :=
  Classical.choose_spec
    (IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
      (trajectoryField_isPicardLindelof_padded p hT η (0 : Eucl d) 1))

@[simp] theorem trajectoryFlowPadded_zero (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) :
    trajectoryFlowPadded p hT η x 0 = x :=
  ((trajectoryFlowPadded_spec p hT η).1 x (mem_closedBall_of_mem_sphere hx)).1

/-- **The padded flow has a genuine `HasDerivAt` at every `t ∈ [0,T]`**, including the endpoints —
`Icc (-1) (T+1)` is a neighborhood of every such `t` since `[0,T]` sits in its interior. -/
theorem hasDerivAt_trajectoryFlowPadded (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (trajectoryFlowPadded p hT η x)
      (trajectoryField p hT η t (trajectoryFlowPadded p hT η x t)) t := by
  have hmem : t ∈ Set.Icc (-1 : ℝ) (T + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwithin := ((trajectoryFlowPadded_spec p hT η).1 x (mem_closedBall_of_mem_sphere hx)).2 t hmem
  have hnhds : Set.Icc (-1 : ℝ) (T + 1) ∈ 𝓝 t := Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
  exact hwithin.hasDerivAt hnhds

theorem continuousOn_trajectoryFlowPadded (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) :
    ContinuousOn (trajectoryFlowPadded p hT η x) (Set.Icc (-1 : ℝ) (T + 1)) :=
  fun _ ht => (((trajectoryFlowPadded_spec p hT η).1 x
    (mem_closedBall_of_mem_sphere hx)).2 _ ht).continuousWithinAt

/-- **The padded flow agrees with `trajectoryFlow` on `[0,T]`.** Both solve the same field and agree
at `t = 0`, so `ODE_solution_unique_of_mem_Icc_right` pins them together throughout `[0,T]`. -/
theorem trajectoryFlowPadded_eq_trajectoryFlow (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) :
    Set.EqOn (trajectoryFlowPadded p hT η x) (trajectoryFlow p hT η x) (Set.Icc (0 : ℝ) T) := by
  have hsub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (-1 : ℝ) (T + 1) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  apply ODE_solution_unique_of_mem_Icc_right
    (v := trajectoryField p hT η) (s := fun _ => Set.univ)
    (K := (Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
      + Real.toNNReal (5 * fieldBallBound p)))
  · intro t ht
    haveI := (η (Set.projIcc 0 T hT t)).property.1
    exact (attnFieldExt_lipschitz p (η (Set.projIcc 0 T hT t)).val
      (η (Set.projIcc 0 T hT t)).property.2).lipschitzOnWith
  · exact (continuousOn_trajectoryFlowPadded p hT η hx).mono hsub
  · intro t ht
    exact (hasDerivAt_trajectoryFlowPadded p hT η hx (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
  · intro t _; trivial
  · exact continuousOn_trajectoryFlow p hT η hx
  · intro t ht
    exact (hasDerivWithinAt_trajectoryFlow p hT η hx
      (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (icc_mem_nhdsWithin_ici ht)
  · intro t _; trivial
  · rw [trajectoryFlowPadded_zero p hT η hx, trajectoryFlow_zero p hT η hx]

/-- **Sphere invariance transfers to the padded flow**, via the equality-on-`[0,T]` identity. -/
theorem trajectoryFlowPadded_mem_sphere (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    trajectoryFlowPadded p hT η x t ∈ sphere d := by
  rw [trajectoryFlowPadded_eq_trajectoryFlow p hT η hx ht]
  exact trajectoryFlow_mem_sphere p hT η hx ht

/-- **The Lipschitz-in-initial-point bound also transfers**, unchanged (same `LipschitzOnWith`
witness the Picard-Lindelöf construction on the padded interval supplies). -/
theorem exists_lipschitzOnWith_trajectoryFlowPadded (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ L' : ℝ≥0, LipschitzOnWith L' (trajectoryFlowPadded p hT η · t)
      (Metric.closedBall (0 : Eucl d) (1 : ℝ≥0)) := by
  obtain ⟨L, hL⟩ := (trajectoryFlowPadded_spec p hT η).2
  exact ⟨L, hL t ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

end MeasureToMeasure.Foundations
