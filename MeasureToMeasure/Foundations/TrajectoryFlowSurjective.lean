import MeasureToMeasure.Foundations.TrajectoryFlowPadded
import Mathlib.Analysis.ODE.Gronwall

/-!
# Surjectivity on the sphere: the last piece of `sphere_bijOn` (M3b existence, leaf E3q)

The remaining gap flagged after leaf E3p: `SurjOn` for `trajectoryFlowPadded`. Given a sphere point
`y` and a time `t`, we need a sphere-supported `x` with `trajectoryFlowPadded p hT η x t = y`.

The route is a genuine **backward flow**: build a second Picard-Lindelöf instance based at time `t`
(not `0`), `trajectoryFlowPaddedAt p hT η t ht`, whose sphere invariance needs the radial-tangency
Grönwall argument run in *both* directions from the base point `t`
(`norm_sq_eq_one_of_radial_tangent_withinIcc_at`, generalizing leaf E3g's version which only ran
forward from `0`): the *forward* case reduces to the existing lemma by a time shift, and the
*backward* case reduces to it by the time-reversal substitution `s ↦ t0 - s` (which negates the
velocity and the gate, but preserves the radial-tangency identity and the gate bound). Evaluating
this backward-based flow at time `0` gives a genuine sphere-supported candidate preimage `x'`; ODE
uniqueness (`ODE_solution_unique_of_mem_Icc_right`, comparing `trajectoryFlowPadded x'` against
`trajectoryFlowPaddedAt t ht y` -- both solve the same field and agree at `0`) then shows the forward
flow from `x'` reaches exactly `y` at time `t`.

Combined with `MapsTo` (leaf E3o) and `InjOn` (leaf E3p), this completes `IsMeanFieldFlow.sphere_bijOn`.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **Bidirectional radial-tangency invariance.** Generalizes `norm_sq_eq_one_of_radial_tangent_
withinIcc` (which only propagates forward from `0`) to propagate from an arbitrary base point `t0`
in both directions: forward via a time shift, backward via the time-reversal substitution
`s ↦ t0 - s` (negates `v` and `c`, preserving both the radial-tangency identity and the gate bound). -/
theorem norm_sq_eq_one_of_radial_tangent_withinIcc_at {x v : ℝ → Eucl d} {c : ℝ → ℝ}
    {K T t0 : ℝ} (ht0 : t0 ∈ Icc (0 : ℝ) T)
    (hx' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt x (v t) (Icc (0 : ℝ) T) t)
    (hrad : ∀ t ∈ Icc (0 : ℝ) T, (⟪x t, v t⟫ : ℝ) = c t * (‖x t‖ ^ 2 - 1))
    (hK : ∀ t ∈ Icc (0 : ℝ) T, |2 * c t| ≤ K)
    (hxt0 : ‖x t0‖ = 1) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t‖ = 1 := by
  intro t ht
  rcases le_total t0 t with hle | hle
  · set y : ℝ → Eucl d := fun s => x (s + t0) with hy
    set v' : ℝ → Eucl d := fun s => v (s + t0) with hv'
    set c' : ℝ → ℝ := fun s => c (s + t0) with hc'
    have hy' : ∀ s ∈ Icc (0 : ℝ) (T - t0), HasDerivWithinAt y (v' s) (Icc (0 : ℝ) (T - t0)) s := by
      intro s hs
      have hmem : s + t0 ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.1, ht0.1], by linarith [hs.2]⟩
      have hd := hx' (s + t0) hmem
      have hcomp : HasDerivWithinAt (fun s => s + t0) (1 : ℝ) (Icc (0 : ℝ) (T - t0)) s := by
        simpa using (hasDerivWithinAt_id s (Icc (0 : ℝ) (T - t0))).add_const t0
      have hmap : Set.MapsTo (fun s => s + t0) (Icc (0 : ℝ) (T - t0)) (Icc (0 : ℝ) T) :=
        fun z hz => ⟨by linarith [hz.1, ht0.1], by linarith [hz.2]⟩
      have hcombined := hd.scomp s hcomp hmap
      rw [show (v' s) = (1 : ℝ) • v (s + t0) by rw [hv']; module]
      exact hcombined
    have hrad' : ∀ s ∈ Icc (0 : ℝ) (T - t0), (⟪y s, v' s⟫ : ℝ) = c' s * (‖y s‖ ^ 2 - 1) := by
      intro s hs
      have hmem : s + t0 ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.1, ht0.1], by linarith [hs.2]⟩
      exact hrad (s + t0) hmem
    have hK' : ∀ s ∈ Icc (0 : ℝ) (T - t0), |2 * c' s| ≤ K := by
      intro s hs
      have hmem : s + t0 ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.1, ht0.1], by linarith [hs.2]⟩
      exact hK (s + t0) hmem
    have hy0 : ‖y 0‖ = 1 := by simpa [hy] using hxt0
    have hfinal :=
      norm_sq_eq_one_of_radial_tangent_withinIcc (K := K) (T := T - t0) hy' hrad' hK' hy0
    have hmem2 : t - t0 ∈ Icc (0 : ℝ) (T - t0) := ⟨by linarith, by linarith [ht.2]⟩
    have := hfinal (t - t0) hmem2
    simpa [hy] using this
  · set y : ℝ → Eucl d := fun s => x (t0 - s) with hy
    set w : ℝ → Eucl d := fun s => (-1 : ℝ) • v (t0 - s) with hw
    set c' : ℝ → ℝ := fun s => -c (t0 - s) with hc'
    have hy' : ∀ s ∈ Icc (0 : ℝ) t0, HasDerivWithinAt y (w s) (Icc (0 : ℝ) t0) s := by
      intro s hs
      have hmem : t0 - s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [ht0.2, hs.1]⟩
      have hd := hx' (t0 - s) hmem
      have hcomp : HasDerivWithinAt (fun s => t0 - s) (-1 : ℝ) (Icc (0 : ℝ) t0) s :=
        (hasDerivWithinAt_id s _).const_sub t0
      have hmap : Set.MapsTo (fun s => t0 - s) (Icc (0 : ℝ) t0) (Icc (0 : ℝ) T) :=
        fun z hz => ⟨by linarith [hz.2, ht0.1], by linarith [ht0.2, hz.1]⟩
      exact hd.scomp s hcomp hmap
    have hrad' : ∀ s ∈ Icc (0 : ℝ) t0, (⟪y s, w s⟫ : ℝ) = c' s * (‖y s‖ ^ 2 - 1) := by
      intro s hs
      have hmem : t0 - s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [ht0.2, hs.1]⟩
      have := hrad (t0 - s) hmem
      simp only [hy, hw, hc', inner_smul_right]
      rw [this]; ring
    have hK' : ∀ s ∈ Icc (0 : ℝ) t0, |2 * c' s| ≤ K := by
      intro s hs
      have hmem : t0 - s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [ht0.2, hs.1]⟩
      have := hK (t0 - s) hmem
      simpa [hc', abs_neg] using this
    have hy0 : ‖y 0‖ = 1 := by simp only [hy, sub_zero]; exact hxt0
    have hfinal :=
      norm_sq_eq_one_of_radial_tangent_withinIcc (K := K) (T := t0) hy' hrad' hK' hy0
    have hmem2 : t0 - t ∈ Icc (0 : ℝ) t0 := ⟨by linarith, by linarith [ht.1]⟩
    have := hfinal (t0 - t) hmem2
    simpa [hy] using this

/-- Same Picard-Lindelöf data as `trajectoryField_isPicardLindelof_padded`, but based at an
arbitrary `t0 ∈ [0,T]` instead of `0`. -/
theorem trajectoryField_isPicardLindelof_padded_at (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (x₀ : Eucl d) (r : ℝ≥0)
    (t0 : ℝ) (ht0 : t0 ∈ Set.Icc (0 : ℝ) T) :
    IsPicardLindelof (trajectoryField p hT η) (tmin := (-1 : ℝ)) (tmax := T + 1)
      ⟨t0, ⟨by linarith [ht0.1], by linarith [ht0.2]⟩⟩
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
    have hmaxle : max ((T + 1 : ℝ) - t0) (t0 - (-1)) ≤ T + 1 := by
      apply max_le
      · linarith [ht0.1]
      · linarith [ht0.2]
    have h1 : (0 : ℝ) ≤ 5 * fieldBallBound p * (T + 1) := mul_nonneg h0 (by linarith)
    have h2 : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
    have harg : (0 : ℝ) ≤ 5 * fieldBallBound p * (T + 1) + r := by linarith
    have hacoe : ((5 * fieldBallBound p * (T + 1) + r).toNNReal : ℝ)
        = 5 * fieldBallBound p * (T + 1) + r := Real.coe_toNNReal _ harg
    rw [hLcoe, hacoe]
    have : (5 * fieldBallBound p : ℝ) * max ((T + 1 : ℝ) - t0) (t0 - (-1)) ≤
        5 * fieldBallBound p * (T + 1) := mul_le_mul_of_nonneg_left hmaxle h0
    linarith [this]

/-- **The flow based at an arbitrary time `t0`**, defined for every `x` in the closed unit ball. -/
noncomputable def trajectoryFlowPaddedAt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (t0 : ℝ) (ht0 : t0 ∈ Set.Icc (0 : ℝ) T) :
    Eucl d → ℝ → Eucl d :=
  Classical.choose
    (IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
      (trajectoryField_isPicardLindelof_padded_at p hT η (0 : Eucl d) 1 t0 ht0))

theorem trajectoryFlowPaddedAt_spec (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (t0 : ℝ) (ht0 : t0 ∈ Set.Icc (0 : ℝ) T) :
    (∀ x ∈ Metric.closedBall (0 : Eucl d) (1 : ℝ≥0), trajectoryFlowPaddedAt p hT η t0 ht0 x t0 = x ∧
        ∀ t ∈ Set.Icc (-1 : ℝ) (T + 1), HasDerivWithinAt (trajectoryFlowPaddedAt p hT η t0 ht0 x)
          (trajectoryField p hT η t (trajectoryFlowPaddedAt p hT η t0 ht0 x t))
          (Set.Icc (-1 : ℝ) (T + 1)) t) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Set.Icc (-1 : ℝ) (T + 1),
        LipschitzOnWith L' (trajectoryFlowPaddedAt p hT η t0 ht0 · t)
          (Metric.closedBall (0 : Eucl d) (1 : ℝ≥0)) :=
  Classical.choose_spec
    (IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
      (trajectoryField_isPicardLindelof_padded_at p hT η (0 : Eucl d) 1 t0 ht0))

@[simp] theorem trajectoryFlowPaddedAt_self (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) T)
    {x : Eucl d} (hx : x ∈ sphere d) :
    trajectoryFlowPaddedAt p hT η t0 ht0 x t0 = x :=
  ((trajectoryFlowPaddedAt_spec p hT η t0 ht0).1 x (mem_closedBall_of_mem_sphere hx)).1

theorem hasDerivWithinAt_trajectoryFlowPaddedAt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) T)
    {x : Eucl d} (hx : x ∈ sphere d) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (trajectoryFlowPaddedAt p hT η t0 ht0 x)
      (trajectoryField p hT η s (trajectoryFlowPaddedAt p hT η t0 ht0 x s)) (Icc (0 : ℝ) T) s := by
  have hmem : s ∈ Set.Icc (-1 : ℝ) (T + 1) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  exact (((trajectoryFlowPaddedAt_spec p hT η t0 ht0).1 x
    (mem_closedBall_of_mem_sphere hx)).2 s hmem).mono
    (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩)

theorem continuousOn_trajectoryFlowPaddedAt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) T)
    {x : Eucl d} (hx : x ∈ sphere d) :
    ContinuousOn (trajectoryFlowPaddedAt p hT η t0 ht0 x) (Set.Icc (0 : ℝ) T) :=
  fun _ ht => (hasDerivWithinAt_trajectoryFlowPaddedAt p hT η ht0 hx ht).continuousWithinAt

/-- **Sphere invariance for the arbitrary-base-point flow**, in BOTH time directions from `t0`. -/
theorem trajectoryFlowPaddedAt_mem_sphere (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) T)
    {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    trajectoryFlowPaddedAt p hT η t0 ht0 x t ∈ sphere d := by
  have hnorm := norm_sq_eq_one_of_radial_tangent_withinIcc_at (T := T)
    (x := fun s => trajectoryFlowPaddedAt p hT η t0 ht0 x s)
    (v := fun s => trajectoryField p hT η s (trajectoryFlowPaddedAt p hT η t0 ht0 x s))
    (c := fun s =>
      attnGate p (η (Set.projIcc 0 T hT s)).val (trajectoryFlowPaddedAt p hT η t0 ht0 x s))
    (K := 4 * fieldBallBound p) ht0
    (fun s hs => hasDerivWithinAt_trajectoryFlowPaddedAt p hT η ht0 hx hs)
    (fun s _ => attnFieldExt_radial p (η (Set.projIcc 0 T hT s)).val
      (trajectoryFlowPaddedAt p hT η t0 ht0 x s))
    (fun s _ => by
      haveI := (η (Set.projIcc 0 T hT s)).property.1
      exact abs_two_attnGate_le p (η (Set.projIcc 0 T hT s)).val
        (η (Set.projIcc 0 T hT s)).property.2 (trajectoryFlowPaddedAt p hT η t0 ht0 x s))
    (by rw [trajectoryFlowPaddedAt_self p hT η ht0 hx]; exact norm_eq_one_of_mem_sphere hx)
  have h1 := hnorm t ht
  simpa [sphere, Metric.mem_sphere, dist_eq_norm] using h1

/-- **Surjectivity on the sphere.** For every sphere target `y` and time `t`, the candidate preimage
`x' := trajectoryFlowPaddedAt p hT η t ht y 0` (the backward-based flow evaluated at time `0`) is
sphere-supported, and the forward flow `trajectoryFlowPadded` from `x'` reaches `y` at time `t`, by
ODE uniqueness against `trajectoryFlowPaddedAt p hT η t ht y` (same field, agree at `0`). Together
with `MapsTo` (leaf E3o) and `InjOn` (leaf E3p), this completes `IsMeanFieldFlow.sphere_bijOn`. -/
theorem trajectoryFlowPadded_surjOn (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Set.SurjOn (fun x => trajectoryFlowPadded p hT η x t) (sphere d) (sphere d) := by
  intro y hy
  set x' := trajectoryFlowPaddedAt p hT η t ht y 0 with hx'
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  have hx'sphere : x' ∈ sphere d := by
    rw [hx']
    exact trajectoryFlowPaddedAt_mem_sphere p hT η ht hy h0mem
  refine ⟨x', hx'sphere, ?_⟩
  have hEq : Set.EqOn (trajectoryFlowPadded p hT η x')
      (trajectoryFlowPaddedAt p hT η t ht y) (Set.Icc (0 : ℝ) T) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := trajectoryField p hT η) (s := fun _ => Set.univ)
      (K := (Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
        + Real.toNNReal (5 * fieldBallBound p)))
    · intro s hs
      haveI := (η (Set.projIcc 0 T hT s)).property.1
      exact (attnFieldExt_lipschitz p (η (Set.projIcc 0 T hT s)).val
        (η (Set.projIcc 0 T hT s)).property.2).lipschitzOnWith
    · exact (continuousOn_trajectoryFlowPadded p hT η hx'sphere).mono
        (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    · intro s hs
      exact (hasDerivAt_trajectoryFlowPadded p hT η hx'sphere
        (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    · intro s _; trivial
    · exact continuousOn_trajectoryFlowPaddedAt p hT η ht hy
    · intro s hs
      exact (hasDerivWithinAt_trajectoryFlowPaddedAt p hT η ht hy
        (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (icc_mem_nhdsWithin_ici hs)
    · intro s _; trivial
    · show trajectoryFlowPadded p hT η x' 0 = trajectoryFlowPaddedAt p hT η t ht y 0
      rw [trajectoryFlowPadded_zero p hT η hx'sphere]
  show trajectoryFlowPadded p hT η x' t = y
  rw [hEq ht, trajectoryFlowPaddedAt_self p hT η ht hy]

end MeasureToMeasure.Foundations
