import MeasureToMeasure.Foundations.TrajectoryFieldSphereInvariant
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The trajectory-composed point flow, and its sphere invariance (M3b existence, leaf E3g)

Leaf E3e gave local existence of *an* integral curve of `ẋ = trajectoryField p hT η t x` through
any single starting point. This leaf packages a genuine **flow function**
`trajectoryFlow p hT η : Eucl d → ℝ → ℝ` -- Lipschitz in the initial point, defined simultaneously
for every `x` in the closed unit ball (in particular every sphere point) -- via Mathlib's
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`, and proves it
**preserves the sphere**: the outer self-consistency map needs `trajectoryFlow p hT η x t ∈ sphere d`
for every sphere-supported starting point `x`, so its pushforward at each time lands back in
`SphereProb d`.

The sphere-invariance argument needs the general radial-tangency Grönwall core
(`SphereFlow.norm_sq_eq_one_of_radial_tangent`), but that lemma is stated for `HasDerivAt` on an open
neighborhood of every point, whereas Mathlib's Picard-Lindelöf existence theorem only gives
`HasDerivWithinAt _ (Icc 0 T)` (the *closed* interval, since `t = 0`/`t = T` have no two-sided
neighborhood in `[0,T]`). `norm_sq_eq_one_of_radial_tangent_withinIcc` re-derives the same Grönwall
argument with `HasDerivWithinAt (Icc 0 T)` hypotheses throughout, using
`HasDerivWithinAt.mono_of_mem_nhdsWithin` (via `icc_mem_nhdsWithin_ici`, `Icc 0 T ∈ 𝓝[Ici t] t` for
`t ∈ Ico 0 T`) to recover the one-sided `Ici t`-derivative Mathlib's Grönwall bound
(`norm_le_gronwallBound_of_norm_deriv_right_le`) actually needs.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- `Icc 0 T` is a one-sided-right neighborhood filter-member at any `t ∈ Ico 0 T` -- the technical
step letting a two-sided-derivative-within-`Icc` hypothesis feed a Grönwall bound stated with a
one-sided `Ici`-derivative. -/
theorem icc_mem_nhdsWithin_ici {t T : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    Icc (0 : ℝ) T ∈ nhdsWithin t (Ici t) := by
  rw [mem_nhdsWithin]
  refine ⟨Iio T, isOpen_Iio, ht.2, ?_⟩
  intro y hy
  simp only [mem_inter_iff, mem_Iio, mem_Ici] at hy
  exact ⟨ht.1.trans hy.2, hy.1.le⟩

/-- **Radial-tangency invariance, `HasDerivWithinAt`-on-`Icc` version.** Re-derives
`SphereFlow.norm_sq_eq_one_of_radial_tangent`'s Grönwall argument with `HasDerivWithinAt (Icc 0 T)`
throughout, so it applies to curves obtained from Mathlib's Picard-Lindelöf existence theorem
(which only gives derivatives within the closed interval, not `HasDerivAt`). -/
theorem norm_sq_eq_one_of_radial_tangent_withinIcc {x v : ℝ → Eucl d} {c : ℝ → ℝ} {K T : ℝ}
    (hx' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt x (v t) (Icc (0 : ℝ) T) t)
    (hrad : ∀ t ∈ Icc (0 : ℝ) T, (⟪x t, v t⟫ : ℝ) = c t * (‖x t‖ ^ 2 - 1))
    (hK : ∀ t ∈ Icc (0 : ℝ) T, |2 * c t| ≤ K)
    (hx0 : ‖x 0‖ = 1) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t‖ = 1 := by
  set u : ℝ → ℝ := fun t => ‖x t‖ ^ 2 - 1 with hu
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (2 * c t * u t) (Icc (0 : ℝ) T) t := by
    intro t ht
    have h := (hx' t ht).inner ℝ (hx' t ht)
    have heq2 : (⟪x t, v t⟫ + ⟪v t, x t⟫ : ℝ) = 2 * ⟪x t, v t⟫ := by
      rw [real_inner_comm (v t) (x t)]; ring
    rw [heq2] at h
    have hnorm : HasDerivWithinAt (fun s => ‖x s‖ ^ 2) (2 * ⟪x t, v t⟫) (Icc (0 : ℝ) T) t := by
      simpa only [real_inner_self_eq_norm_sq] using h
    have hrw : (2 * ⟪x t, v t⟫ : ℝ) = 2 * c t * u t := by
      rw [hrad t ht]; simp only [hu]; ring
    rw [hrw] at hnorm
    have hsub : HasDerivWithinAt (fun s => ‖x s‖ ^ 2 - 1) (2 * c t * u t) (Icc (0 : ℝ) T) t :=
      hnorm.sub_const 1
    simpa only [hu] using hsub
  have hcont : ContinuousOn u (Icc 0 T) := fun t ht => (hderiv t ht).continuousWithinAt
  have hu0 : ‖u 0‖ ≤ 0 := by simp only [hu, hx0]; norm_num
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, ‖(2 * c t * u t : ℝ)‖ ≤ K * ‖u t‖ + 0 := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
    rw [add_zero, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hK t htc) (abs_nonneg _)
  intro t ht
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s hs => (hderiv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (icc_mem_nhdsWithin_ici hs)) hu0 hbound t ht
  rw [gronwallBound_ε0_δ0] at hgron
  have hut : u t = 0 := by
    have := norm_nonneg (u t)
    have h0 : ‖u t‖ = 0 := le_antisymm hgron (norm_nonneg _)
    simpa using h0
  have hsq : ‖x t‖ ^ 2 = 1 := by simpa only [hu, sub_eq_zero] using hut
  have := norm_nonneg (x t)
  nlinarith [hsq, norm_nonneg (x t)]

theorem mem_closedBall_of_mem_sphere {x : Eucl d} (hx : x ∈ sphere d) :
    x ∈ Metric.closedBall (0 : Eucl d) (1 : ℝ≥0) := by
  simp [Metric.mem_closedBall, dist_eq_norm, norm_eq_one_of_mem_sphere hx]

/-- **The trajectory-composed point flow.** A genuine flow function `trajectoryFlow p hT η : Eucl d
→ ℝ → Eucl d`, defined via Mathlib's Lipschitz-in-initial-point Picard-Lindelöf theorem on the
closed unit ball (so it applies uniformly to every sphere point) for the field composed with the
trial trajectory `η`. -/
noncomputable def trajectoryFlow (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) : Eucl d → ℝ → Eucl d :=
  Classical.choose
    (IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
      (trajectoryField_isPicardLindelof p hT η (0 : Eucl d) 1))

theorem trajectoryFlow_spec (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    (∀ x ∈ Metric.closedBall (0 : Eucl d) (1 : ℝ≥0), trajectoryFlow p hT η x 0 = x ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (trajectoryFlow p hT η x)
          (trajectoryField p hT η t (trajectoryFlow p hT η x t)) (Set.Icc (0 : ℝ) T) t) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Set.Icc (0 : ℝ) T,
        LipschitzOnWith L' (trajectoryFlow p hT η · t) (Metric.closedBall (0 : Eucl d) (1 : ℝ≥0)) :=
  Classical.choose_spec
    (IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
      (trajectoryField_isPicardLindelof p hT η (0 : Eucl d) 1))

@[simp] theorem trajectoryFlow_zero (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) :
    trajectoryFlow p hT η x 0 = x :=
  ((trajectoryFlow_spec p hT η).1 x (mem_closedBall_of_mem_sphere hx)).1

theorem hasDerivWithinAt_trajectoryFlow (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (trajectoryFlow p hT η x)
      (trajectoryField p hT η t (trajectoryFlow p hT η x t)) (Set.Icc (0 : ℝ) T) t :=
  ((trajectoryFlow_spec p hT η).1 x (mem_closedBall_of_mem_sphere hx)).2 t ht

theorem exists_lipschitzOnWith_trajectoryFlow (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    ∃ L' : ℝ≥0, ∀ t ∈ Set.Icc (0 : ℝ) T,
      LipschitzOnWith L' (trajectoryFlow p hT η · t) (Metric.closedBall (0 : Eucl d) (1 : ℝ≥0)) :=
  (trajectoryFlow_spec p hT η).2

theorem continuousOn_trajectoryFlow (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) :
    ContinuousOn (trajectoryFlow p hT η x) (Set.Icc (0 : ℝ) T) :=
  fun _ ht => (hasDerivWithinAt_trajectoryFlow p hT η hx ht).continuousWithinAt

/-- **Sphere invariance of the trajectory-composed point flow.** For any sphere-supported starting
point `x`, the whole trajectory `t ↦ trajectoryFlow p hT η x t` stays on the sphere throughout
`[0,T]`. This is what lets the outer self-consistency map land back in `SphereProb d`. -/
theorem trajectoryFlow_mem_sphere (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    trajectoryFlow p hT η x t ∈ sphere d := by
  have hnorm := norm_sq_eq_one_of_radial_tangent_withinIcc
    (x := trajectoryFlow p hT η x)
    (v := fun s => trajectoryField p hT η s (trajectoryFlow p hT η x s))
    (c := fun s => attnGate p (η (Set.projIcc 0 T hT s)).val (trajectoryFlow p hT η x s))
    (K := 4 * fieldBallBound p) (T := T)
    (fun s hs => hasDerivWithinAt_trajectoryFlow p hT η hx hs)
    (fun s _ => attnFieldExt_radial p (η (Set.projIcc 0 T hT s)).val (trajectoryFlow p hT η x s))
    (fun s _ => by
      haveI := (η (Set.projIcc 0 T hT s)).property.1
      exact abs_two_attnGate_le p (η (Set.projIcc 0 T hT s)).val
        (η (Set.projIcc 0 T hT s)).property.2 (trajectoryFlow p hT η x s))
    (by rw [trajectoryFlow_zero p hT η hx]; exact norm_eq_one_of_mem_sphere hx)
  have h1 := hnorm t ht
  simpa [sphere, Metric.mem_sphere, dist_eq_norm] using h1

end MeasureToMeasure.Foundations
