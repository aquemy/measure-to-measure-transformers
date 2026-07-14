import MeasureToMeasure.Foundations.TrajectoryFlowSurjective
import MeasureToMeasure.Foundations.TrajectoryFlowInjective
import MeasureToMeasure.Foundations.SelfConsistencyFixedPoint

/-!
# `exists_meanFieldFlow` discharged: the McKean-Vlasov mean-field flow exists (M3b existence,
leaf E3r — campaign close)

This file **discharges the `exists_meanFieldFlow` axiom** of `Foundations/Attention.lean`,
replacing it with a genuine theorem, and re-hosts everything built on top of it (`attnStep`,
`attnMeasureFlow`, and their consequences) that used to live in `Attention.lean` and
`MeanFieldWellPosed.lean`. The relocation is structural, not mathematical: `Attention.lean` sits
*upstream* of the whole M3b existence campaign (`TrajectoryFieldPicardLindelof.lean` through
`TrajectoryFlowSurjective.lean`, which all need `AttnParams`/`attnFieldExt`/`IsMeanFieldFlow` from
it), so the existence proof — which consumes that entire campaign — cannot live inside
`Attention.lean` itself without a circular import. It lives here instead, downstream of the whole
chain, and everything that used to consume the axiom (`attnStep` etc.) moves here with it so that
those definitions can use the genuine theorem instead of the axiom.

## The construction

Fix `p : AttnParams d`, `T := p.duration`, and a sphere-supported probability datum `μ₀`. Leaf E3n
(`exists_selfConsistent_trajectory`) gives a fixed point `η` of the self-consistency map
`selfConsistencyStepCM`. The candidate flow is

  `Φ t x := trajectoryFlowPaddedExt p hT η t x - trajectoryFlowPaddedExt p hT η 0 x + x`,

where `trajectoryFlowPaddedExt` is `trajectoryFlowPadded` (leaf E3o, genuine `HasDerivAt` at every
`t ∈ [0,T]`) extended off the closed unit ball via `ballProj` (the same trick leaf E3h used for
`trajectoryFlowExt`). The identity-correction term `- trajectoryFlowPaddedExt 0 x + x` is what makes
`IsMeanFieldFlow.init : Φ 0 = id` hold as a GLOBAL function equality on all of `Eucl d`, not just the
sphere: a bare `ballProj`-extension gives `Φ 0 x = ballProj x`, which is only `x` inside the closed
unit ball, so the correction term is needed to cancel that discrepancy everywhere while vanishing
identically on the sphere (where `ballProj` is already the identity), so `Φ` reduces exactly to
`trajectoryFlowPadded p hT η x t` there.

The five `IsMeanFieldFlow` fields:
* `init`: the identity-correction term vanishes at `t = 0` by construction.
* `measurable`/`lipschitz`: `trajectoryFlowPaddedExt` is globally Lipschitz (composing the
  ball-Lipschitz `trajectoryFlowPadded` with the globally-1-Lipschitz `ballProj`, whose image always
  lands in the ball), and Mathlib's underlying Picard-Lindelöf existence theorem already supplies a
  UNIFORM-in-`t` Lipschitz witness (not per-`t`), matching `IsMeanFieldFlow.lipschitz`'s `∃ L, ∀ t,
  ...` shape directly.
* `sphere_bijOn`: transfers `MapsTo`/`InjOn`/`SurjOn` (leaves E3o/E3p/E3q) through the sphere-restricted
  equality `Φ t = trajectoryFlowPadded p hT η · t` there.
* `deriv`: `hasDerivAt_trajectoryFlowPadded` (E3o) gives the raw ODE derivative w.r.t.
  `trajectoryField`; the fixed-point self-consistency identity `eta_eq_pushforward` (E3p) identifies
  `η t` with the ACTUAL current pushforward `(Φ_t)_#μ₀`, and `attnFieldExt_eq_field_of_mem_sphere`
  identifies `attnFieldExt` with `p.field` on the sphere — composing these turns the raw ODE
  derivative into exactly the mean-field characteristic equation `IsMeanFieldFlow.deriv` demands.

M3b staging note (now obsolete): `exists_meanFieldFlow` was the sole remaining axiom in
`Foundations/Attention.lean`; after this file, it is a theorem. Axiom inventory 10 → 9.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal Classical

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-! ### The candidate flow: `trajectoryFlowPadded` extended off the ball, identity-corrected -/

/-- `trajectoryFlowPadded`, extended off the closed unit ball via `ballProj` — globally continuous
and Lipschitz, exactly mirroring `trajectoryFlowExt` (leaf E3h) but for the padded (two-sided
`HasDerivAt`) flow of leaf E3o. -/
noncomputable def trajectoryFlowPaddedExt (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (t : ℝ) (x : Eucl d) : Eucl d :=
  trajectoryFlowPadded p hT η (ballProj x) t

theorem ballProj_mem_closedBall (x : Eucl d) :
    ballProj x ∈ Metric.closedBall (0 : Eucl d) (1 : ℝ≥0) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact_mod_cast norm_ballProj_le x

theorem trajectoryFlowPaddedExt_zero (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (x : Eucl d) :
    trajectoryFlowPaddedExt p hT η 0 x = ballProj x :=
  ((trajectoryFlowPadded_spec p hT η).1 (ballProj x) (ballProj_mem_closedBall x)).1

theorem trajectoryFlowPaddedExt_eq_of_mem_sphere (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} {x : Eucl d} (hx : x ∈ sphere d) :
    trajectoryFlowPaddedExt p hT η t x = trajectoryFlowPadded p hT η x t := by
  unfold trajectoryFlowPaddedExt
  rw [ballProj_eq_self (norm_eq_one_of_mem_sphere hx).le]

/-- **The candidate mean-field flow.** `trajectoryFlowPaddedExt`, corrected by its own value at
`t = 0` so that `Φ 0 = id` holds GLOBALLY (not just on the ball); the correction vanishes exactly
on the sphere, where `Φ` reduces to `trajectoryFlowPadded`. -/
noncomputable def meanFieldFlowCandidate (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (t : ℝ) (x : Eucl d) : Eucl d :=
  trajectoryFlowPaddedExt p hT η t x - trajectoryFlowPaddedExt p hT η 0 x + x

theorem meanFieldFlowCandidate_zero (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    meanFieldFlowCandidate p hT η 0 = id := by
  funext x; unfold meanFieldFlowCandidate; simp

theorem meanFieldFlowCandidate_eq_of_mem_sphere (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} {x : Eucl d} (hx : x ∈ sphere d) :
    meanFieldFlowCandidate p hT η t x = trajectoryFlowPadded p hT η x t := by
  unfold meanFieldFlowCandidate
  rw [trajectoryFlowPaddedExt_eq_of_mem_sphere p hT η hx,
    trajectoryFlowPaddedExt_eq_of_mem_sphere p hT η hx, trajectoryFlowPadded_zero p hT η hx]
  abel

/-! ### The five `IsMeanFieldFlow` fields -/

/-- Uniform-in-`t` Lipschitz bound for the candidate flow, matching `IsMeanFieldFlow.lipschitz`'s
`∃ L, ∀ t, ...` shape directly (Mathlib's Picard-Lindelöf existence theorem already supplies a
witness uniform in `t`, not per-`t`). -/
theorem lipschitzWith_meanFieldFlowCandidate_uniform (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    ∃ L : ℝ≥0, ∀ t ∈ Set.Icc (0 : ℝ) T, LipschitzWith L (meanFieldFlowCandidate p hT η t) := by
  obtain ⟨L', hL'⟩ := (trajectoryFlowPadded_spec p hT η).2
  refine ⟨L' + L' + 1, fun t ht => LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  have ht' : t ∈ Set.Icc (-1 : ℝ) (T + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0' : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) (T + 1) := ⟨by linarith, by linarith⟩
  have hLt : LipschitzOnWith L' (trajectoryFlowPadded p hT η · t)
      (Metric.closedBall (0 : Eucl d) (1 : ℝ≥0)) := hL' t ht'
  have hL0 : LipschitzOnWith L' (trajectoryFlowPadded p hT η · 0)
      (Metric.closedBall (0 : Eucl d) (1 : ℝ≥0)) := hL' 0 h0'
  have h1 : dist (trajectoryFlowPaddedExt p hT η t x) (trajectoryFlowPaddedExt p hT η t y)
      ≤ (L' : ℝ) * dist x y := by
    unfold trajectoryFlowPaddedExt
    calc dist (trajectoryFlowPadded p hT η (ballProj x) t) (trajectoryFlowPadded p hT η (ballProj y) t)
        ≤ (L' : ℝ) * dist (ballProj x) (ballProj y) :=
          hLt.dist_le_mul (ballProj x) (ballProj_mem_closedBall x) (ballProj y)
            (ballProj_mem_closedBall y)
      _ ≤ (L' : ℝ) * dist x y := by
          apply mul_le_mul_of_nonneg_left _ L'.coe_nonneg
          simpa using lipschitzWith_ballProj.dist_le_mul x y
  have h2 : dist (trajectoryFlowPaddedExt p hT η 0 x) (trajectoryFlowPaddedExt p hT η 0 y)
      ≤ (L' : ℝ) * dist x y := by
    unfold trajectoryFlowPaddedExt
    calc dist (trajectoryFlowPadded p hT η (ballProj x) 0) (trajectoryFlowPadded p hT η (ballProj y) 0)
        ≤ (L' : ℝ) * dist (ballProj x) (ballProj y) :=
          hL0.dist_le_mul (ballProj x) (ballProj_mem_closedBall x) (ballProj y)
            (ballProj_mem_closedBall y)
      _ ≤ (L' : ℝ) * dist x y := by
          apply mul_le_mul_of_nonneg_left _ L'.coe_nonneg
          simpa using lipschitzWith_ballProj.dist_le_mul x y
  unfold meanFieldFlowCandidate
  calc dist (trajectoryFlowPaddedExt p hT η t x - trajectoryFlowPaddedExt p hT η 0 x + x)
        (trajectoryFlowPaddedExt p hT η t y - trajectoryFlowPaddedExt p hT η 0 y + y)
      ≤ dist (trajectoryFlowPaddedExt p hT η t x - trajectoryFlowPaddedExt p hT η 0 x)
          (trajectoryFlowPaddedExt p hT η t y - trajectoryFlowPaddedExt p hT η 0 y) + dist x y :=
        dist_add_add_le _ _ _ _
    _ ≤ (dist (trajectoryFlowPaddedExt p hT η t x) (trajectoryFlowPaddedExt p hT η t y)
        + dist (trajectoryFlowPaddedExt p hT η 0 x) (trajectoryFlowPaddedExt p hT η 0 y)) + dist x y := by
        gcongr; exact dist_sub_sub_le _ _ _ _
    _ ≤ L' * dist x y + L' * dist x y + dist x y := by gcongr
    _ = (L' + L' + 1) * dist x y := by ring

theorem measurable_meanFieldFlowCandidate (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Measurable (meanFieldFlowCandidate p hT η t) := by
  obtain ⟨L, hL⟩ := lipschitzWith_meanFieldFlowCandidate_uniform p hT η
  exact (hL t ht).continuous.measurable

/-- The self-consistency identity (`eta_eq_pushforward`, leaf E3p) plus `attnFieldExt_eq_field_
of_mem_sphere` identify the raw ODE derivative (`hasDerivAt_trajectoryFlowPadded`, leaf E3o) with
exactly the mean-field characteristic equation `IsMeanFieldFlow.deriv` needs. -/
theorem meanFieldFlow_deriv (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T) (μ₀ : Measure (Eucl d))
    [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0) (η : C(Set.Icc (0 : ℝ) T, SphereProb d))
    (hfix : selfConsistencyStepCM p hT η μ₀ hμ₀ = η)
    (x : Eucl d) (hx : x ∈ sphere d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (fun s => trajectoryFlowPadded p hT η x s)
      (p.field (μ₀.map (fun y => trajectoryFlowPadded p hT η y t))
        (trajectoryFlowPadded p hT η x t)) t := by
  have hd := hasDerivAt_trajectoryFlowPadded p hT η hx ht
  have hmapeq : μ₀.map (fun y => trajectoryFlowPadded p hT η y t)
      = μ₀.map (fun y => trajectoryFlow p hT η y t) := by
    apply Measure.map_congr
    apply ae_of_sphere_supported hμ₀
    intro y hy
    exact trajectoryFlowPadded_eq_trajectoryFlow p hT η hy ht
  have heq : trajectoryField p hT η t (trajectoryFlowPadded p hT η x t) =
      p.field (μ₀.map (fun y => trajectoryFlowPadded p hT η y t))
        (trajectoryFlowPadded p hT η x t) := by
    unfold trajectoryField
    have hproj_eq : Set.projIcc 0 T hT t = ⟨t, ht⟩ := Set.projIcc_of_mem hT ht
    rw [hproj_eq]
    have hxt_sphere : trajectoryFlowPadded p hT η x t ∈ sphere d :=
      trajectoryFlowPadded_mem_sphere p hT η hx ht
    rw [attnFieldExt_eq_field_of_mem_sphere p (η ⟨t, ht⟩).val hxt_sphere, hmapeq]
    congr 1
    exact eta_eq_pushforward p hT μ₀ hμ₀ η hfix ht
  rwa [heq] at hd

/-- `sphere_bijOn`: transfers `MapsTo`/`InjOn`/`SurjOn` (leaves E3o/E3p/E3q) through the
sphere-restricted equality `Φ t = trajectoryFlowPadded p hT η · t`. -/
theorem sphere_bijOn_meanFieldFlowCandidate (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Set.BijOn (meanFieldFlowCandidate p hT η t) (sphere d) (sphere d) := by
  have hfunEq : Set.EqOn (meanFieldFlowCandidate p hT η t) (fun x => trajectoryFlowPadded p hT η x t)
      (sphere d) :=
    fun x hx => meanFieldFlowCandidate_eq_of_mem_sphere p hT η hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hfunEq hx]
    exact trajectoryFlowPadded_mem_sphere p hT η hx ht
  · intro x hx y hy heq
    rw [hfunEq hx, hfunEq hy] at heq
    exact trajectoryFlowPadded_injOn p hT η ht hx hy heq
  · intro y hy
    obtain ⟨x, hx, hxeq⟩ := trajectoryFlowPadded_surjOn p hT η ht hy
    exact ⟨x, hx, by rw [hfunEq hx]; exact hxeq⟩

/-- Generic `IsMeanFieldFlow` constructor from its five fields — used to keep the anonymous
constructor away from the large concrete proof terms at the call site. -/
theorem mkIsMeanFieldFlow (p : AttnParams d) (μ₀ : Measure (Eucl d)) (Φ : ℝ → Eucl d → Eucl d)
    (hinit : Φ 0 = id)
    (hmeas : ∀ t ∈ Set.Icc 0 p.duration, Measurable (Φ t))
    (hlip : ∃ L, ∀ t ∈ Set.Icc 0 p.duration, LipschitzWith L (Φ t))
    (hbij : ∀ t ∈ Set.Icc 0 p.duration, Set.BijOn (Φ t) (sphere d) (sphere d))
    (hderiv : ∀ x ∈ sphere d, ∀ t ∈ Set.Icc 0 p.duration,
      HasDerivAt (fun s => Φ s x) (p.field (μ₀.map (Φ t)) (Φ t x)) t) :
    IsMeanFieldFlow p μ₀ Φ :=
  ⟨hinit, hmeas, hlip, hbij, hderiv⟩

set_option maxHeartbeats 1000000 in
/-- `meanFieldFlow_deriv` restated for `meanFieldFlowCandidate` itself (rather than the underlying
`trajectoryFlowPadded`), via the sphere-restricted equalities. The mixed occurrences of `Φ t` (bare,
as the argument to `Measure.map`, and applied at `x`) make a direct `rw`/`convert` on the goal
catastrophically slow; instead the three needed equalities are proved separately and combined into
one type-level rewrite before discharging with `▸`. -/
theorem meanFieldFlowCandidate_deriv (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T) (μ₀ : Measure (Eucl d))
    [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0) (η : C(Set.Icc (0 : ℝ) T, SphereProb d))
    (hfix : selfConsistencyStepCM p hT η μ₀ hμ₀ = η)
    (x : Eucl d) (hx : x ∈ sphere d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (fun s => meanFieldFlowCandidate p hT η s x)
      (p.field (μ₀.map (meanFieldFlowCandidate p hT η t)) (meanFieldFlowCandidate p hT η t x)) t := by
  have hsrc := meanFieldFlow_deriv p hT μ₀ hμ₀ η hfix x hx ht
  have hfun_eq : (fun s => meanFieldFlowCandidate p hT η s x)
      = (fun s => trajectoryFlowPadded p hT η x s) :=
    funext (fun s => meanFieldFlowCandidate_eq_of_mem_sphere p hT η hx)
  have hmap_eq : μ₀.map (meanFieldFlowCandidate p hT η t)
      = μ₀.map (fun y => trajectoryFlowPadded p hT η y t) := by
    apply Measure.map_congr
    apply ae_of_sphere_supported hμ₀
    intro y hy
    exact meanFieldFlowCandidate_eq_of_mem_sphere p hT η hy
  have hpt_eq : meanFieldFlowCandidate p hT η t x = trajectoryFlowPadded p hT η x t :=
    meanFieldFlowCandidate_eq_of_mem_sphere p hT η hx
  have htype_eq :
      (HasDerivAt (fun s => meanFieldFlowCandidate p hT η s x)
        (p.field (μ₀.map (meanFieldFlowCandidate p hT η t)) (meanFieldFlowCandidate p hT η t x)) t) =
      (HasDerivAt (fun s => trajectoryFlowPadded p hT η x s)
        (p.field (μ₀.map (fun y => trajectoryFlowPadded p hT η y t))
          (trajectoryFlowPadded p hT η x t)) t) := by
    rw [hfun_eq, hmap_eq, hpt_eq]
  exact htype_eq ▸ hsrc

theorem isMeanFieldFlow_meanFieldFlowCandidate (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) (hfix : selfConsistencyStepCM p hT η μ₀ hμ₀ = η)
    (hTeq : T = p.duration) :
    IsMeanFieldFlow p μ₀ (meanFieldFlowCandidate p hT η) := by
  have hinit : meanFieldFlowCandidate p hT η 0 = id := meanFieldFlowCandidate_zero p hT η
  have hmeas : ∀ t ∈ Set.Icc 0 p.duration, Measurable (meanFieldFlowCandidate p hT η t) := by
    intro t ht; rw [← hTeq] at ht; exact measurable_meanFieldFlowCandidate p hT η ht
  have hlip : ∃ L, ∀ t ∈ Set.Icc 0 p.duration, LipschitzWith L (meanFieldFlowCandidate p hT η t) := by
    obtain ⟨L, hL⟩ := lipschitzWith_meanFieldFlowCandidate_uniform p hT η
    exact ⟨L, fun t ht => hL t (hTeq ▸ ht)⟩
  have hbij : ∀ t ∈ Set.Icc 0 p.duration,
      Set.BijOn (meanFieldFlowCandidate p hT η t) (sphere d) (sphere d) := by
    intro t ht; rw [← hTeq] at ht; exact sphere_bijOn_meanFieldFlowCandidate p hT η ht
  have hderiv : ∀ x ∈ sphere d, ∀ t ∈ Set.Icc 0 p.duration,
      HasDerivAt (fun s => meanFieldFlowCandidate p hT η s x)
        (p.field (μ₀.map (meanFieldFlowCandidate p hT η t)) (meanFieldFlowCandidate p hT η t x)) t := by
    intro x hx t ht
    rw [← hTeq] at ht
    exact meanFieldFlowCandidate_deriv p hT μ₀ hμ₀ η hfix x hx ht
  exact mkIsMeanFieldFlow p μ₀ (meanFieldFlowCandidate p hT η) hinit hmeas hlip hbij hderiv

/-- **Well-posedness of the self-attention mean-field flow (existence).** For every Transformer
block and every sphere-supported probability datum there is a mean-field flow: the fixed point of
the self-consistency map (leaf E3n), transported through the padded point flow. Formerly the axiom
`exists_meanFieldFlow`; `Attention.lean`'s copy is deleted, this is the discharge. -/
theorem exists_meanFieldFlow (p : AttnParams d) (μ₀ : Measure (Eucl d))
    [IsProbabilityMeasure μ₀] (hs : μ₀ (sphere d)ᶜ = 0) :
    ∃ Φ : ℝ → Eucl d → Eucl d, IsMeanFieldFlow p μ₀ Φ := by
  obtain ⟨η, hfix⟩ := exists_selfConsistent_trajectory p p.duration_nonneg μ₀ hs
  exact ⟨meanFieldFlowCandidate p p.duration_nonneg η,
    isMeanFieldFlow_meanFieldFlowCandidate p p.duration_nonneg μ₀ hs η hfix rfl⟩

/-! ### `attnStep`/`attnMeasureFlow` and their consequences, relocated from `Attention.lean`

These definitions and theorems used to live in `Attention.lean`, consuming the axiom directly; they
move here verbatim (only the `axiom` → `theorem` reference changes, which is transparent since the
name and type are identical) because their bodies now need the genuine `exists_meanFieldFlow`
theorem above. -/

/-- One block step of the measure-level solution operator: push `μ` forward along the block's
mean-field flow at its duration. Junk branch: off sphere-supported probability data the step is
the identity (every downstream statement carries the sphere-probability hypotheses). -/
noncomputable def attnStep (p : AttnParams d) (μ : Measure (Eucl d)) : Measure (Eucl d) :=
  if h : IsProbabilityMeasure μ ∧ μ (sphere d)ᶜ = 0 then
    μ.map ((@exists_meanFieldFlow d p μ h.1 h.2).choose p.duration)
  else μ

/-- The solution operator of a schedule: fold the per-block steps left-to-right (run the first
block first). -/
noncomputable def attnMeasureFlow (θ : AttnSchedule d) (μ : Measure (Eucl d)) :
    Measure (Eucl d) :=
  θ.foldl (fun ν p => attnStep p ν) μ

@[simp] theorem attnMeasureFlow_nil (μ : Measure (Eucl d)) :
    attnMeasureFlow ([] : AttnSchedule d) μ = μ := rfl

/-- Composition of schedules is concatenation: running `θ ++ ψ` is running `θ`, then `ψ`. -/
theorem attnMeasureFlow_append (θ ψ : AttnSchedule d) (μ : Measure (Eucl d)) :
    attnMeasureFlow (θ ++ ψ) μ = attnMeasureFlow ψ (attnMeasureFlow θ μ) :=
  List.foldl_append ..

/-- One step preserves probability (on sphere-supported probability data). -/
theorem isProbabilityMeasure_attnStep (p : AttnParams d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    IsProbabilityMeasure (attnStep p μ) := by
  rw [attnStep, dif_pos ⟨‹IsProbabilityMeasure μ›, hs⟩]
  have hspec := (@exists_meanFieldFlow d p μ ‹_› hs).choose_spec
  have hm := hspec.measurable p.duration ⟨p.duration_nonneg, le_rfl⟩
  exact ⟨by rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩

/-- One step preserves sphere support: the flow maps the sphere into itself. -/
theorem attnStep_supportedIn_sphere (p : AttnParams d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    (attnStep p μ) (sphere d)ᶜ = 0 := by
  rw [attnStep, dif_pos ⟨‹IsProbabilityMeasure μ›, hs⟩]
  have hspec := (@exists_meanFieldFlow d p μ ‹_› hs).choose_spec
  have hdur : p.duration ∈ Set.Icc 0 p.duration := ⟨p.duration_nonneg, le_rfl⟩
  have hms : MeasurableSet (sphere d)ᶜ := Metric.isClosed_sphere.measurableSet.compl
  rw [Measure.map_apply (hspec.measurable p.duration hdur) hms]
  refine measure_mono_null (fun x hx => ?_) hs
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
  exact fun hxs => hx ((hspec.sphere_bijOn p.duration hdur).mapsTo hxs)

/-- The solution operator preserves probability and sphere support along the whole schedule. -/
theorem attnMeasureFlow_prob_supportedIn_sphere (θ : AttnSchedule d) :
    ∀ (μ : Measure (Eucl d)), IsProbabilityMeasure μ → μ (sphere d)ᶜ = 0 →
      IsProbabilityMeasure (attnMeasureFlow θ μ) ∧ (attnMeasureFlow θ μ) (sphere d)ᶜ = 0 := by
  induction θ with
  | nil => exact fun μ hμ hs => ⟨hμ, hs⟩
  | cons p rest ih =>
    intro μ hμ hs
    haveI := hμ
    have h1 := isProbabilityMeasure_attnStep p μ hs
    have h2 := attnStep_supportedIn_sphere p μ hs
    simpa [attnMeasureFlow] using ih (attnStep p μ) h1 h2

/-- The solution operator preserves probability (on sphere-supported probability data). -/
theorem isProbabilityMeasure_attnMeasureFlow (θ : AttnSchedule d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    IsProbabilityMeasure (attnMeasureFlow θ μ) :=
  (attnMeasureFlow_prob_supportedIn_sphere θ μ ‹_› hs).1

/-- The solution operator preserves sphere support (on sphere-supported probability data). -/
theorem attnMeasureFlow_supportedIn_sphere (θ : AttnSchedule d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    (attnMeasureFlow θ μ) (sphere d)ᶜ = 0 :=
  (attnMeasureFlow_prob_supportedIn_sphere θ μ ‹_› hs).2

/-! ### Transport-map extraction: every solution operator is a pushforward

Each block step pushes the measure along its mean-field flow at the block's duration; composing
the steps exhibits the whole schedule's action as one measurable pushforward, invertible on the
sphere. This is the paper's flow-map convention (the Lipschitz invertible `φ^T : 𝕊^{d-1} → 𝕊^{d-1}`
of eq. (B.2)), derived from the well-posedness interface, so downstream statements need not carry
per-member transport-map clauses as axiom content. -/

/-- **One step is a pushforward.** The block step of a sphere-supported probability measure is the
pushforward along a measurable, CONTINUOUS map that carries the sphere into itself and has a
measurable left inverse there (the mean-field flow slice at the block's duration; its sphere
restriction is a continuous bijection of a compact space, hence a homeomorphism). Continuity of the
forward map is threaded through explicitly (not just its sphere-inverse's continuity, already used
internally to build the homeomorphism) because a later leaf (`support_map_eq_image_of_continuous`,
towards `lemma_3_4_part2`) needs the forward map's own continuity to identify `support (μ.map Φ)`
with `Φ '' (support μ)`. -/
theorem attnStep_exists_map (p : AttnParams d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    ∃ Φ Φinv : Eucl d → Eucl d, Measurable Φ ∧ Continuous Φ ∧ Measurable Φinv ∧
      attnStep p μ = μ.map Φ ∧ Set.MapsTo Φ (sphere d) (sphere d) ∧
      ∀ x ∈ sphere d, Φinv (Φ x) = x := by
  classical
  have hspec := (@exists_meanFieldFlow d p μ ‹_› hs).choose_spec
  set Φd := (@exists_meanFieldFlow d p μ ‹_› hs).choose p.duration with hΦd
  have hdur : p.duration ∈ Set.Icc 0 p.duration := ⟨p.duration_nonneg, le_rfl⟩
  have hmeas : Measurable Φd := hspec.measurable p.duration hdur
  have hbij : Set.BijOn Φd (sphere d) (sphere d) := hspec.sphere_bijOn p.duration hdur
  obtain ⟨L, hlip⟩ := hspec.lipschitz
  have hcont : Continuous Φd := (hlip p.duration hdur).continuous
  -- The sphere restriction is a continuous bijection of a compact T2 space: a homeomorphism.
  haveI : CompactSpace (sphere d) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let e : sphere d ≃ sphere d := hbij.equiv Φd
  have hecont : Continuous (e : sphere d → sphere d) := by
    have : Continuous fun x : sphere d => Φd (x : Eucl d) := hcont.comp continuous_subtype_val
    exact Continuous.subtype_mk this _
  let homeo : sphere d ≃ₜ sphere d := Continuous.homeoOfEquivCompactToT2 (f := e) hecont
  -- Re-embed the sphere inverse as a global measurable map via a measurable retraction.
  obtain ⟨z₀, hz₀⟩ := sphere_nonempty_of_supported μ hs
  set πval : Eucl d → Eucl d := (sphere d).piecewise id fun _ => z₀ with hπval
  have hπmeas : Measurable πval :=
    Measurable.piecewise Metric.isClosed_sphere.measurableSet measurable_id measurable_const
  have hπmem : ∀ y, πval y ∈ sphere d := by
    intro y
    by_cases hy : y ∈ sphere d <;> simp [hπval, hy, hz₀]
  refine ⟨Φd, fun y => (homeo.symm ⟨πval y, hπmem y⟩ : Eucl d), hmeas, hcont,
    (continuous_subtype_val.comp homeo.symm.continuous).measurable.comp
      (hπmeas.subtype_mk (p := fun z => z ∈ sphere d)), ?_, hbij.mapsTo, ?_⟩
  · rw [attnStep, dif_pos ⟨‹IsProbabilityMeasure μ›, hs⟩]
  · intro x hx
    have hΦx : Φd x ∈ sphere d := hbij.mapsTo hx
    have hπ : πval (Φd x) = Φd x := by simp [hπval, hΦx]
    have hval : (⟨πval (Φd x), hπmem (Φd x)⟩ : sphere d) = e ⟨x, hx⟩ :=
      Subtype.ext (by show πval (Φd x) = ((e ⟨x, hx⟩ : sphere d) : Eucl d); rw [hπ]; rfl)
    calc (homeo.symm ⟨πval (Φd x), hπmem (Φd x)⟩ : Eucl d)
        = (homeo.symm (e ⟨x, hx⟩) : Eucl d) := by rw [hval]
      _ = ((⟨x, hx⟩ : sphere d) : Eucl d) := by
          have h2 : homeo.symm (e ⟨x, hx⟩) = ⟨x, hx⟩ := homeo.symm_apply_apply ⟨x, hx⟩
          exact congrArg Subtype.val h2
      _ = x := rfl

/-- **The solution operator is a pushforward.** Along any schedule, a sphere-supported probability
measure is pushed forward by one measurable, CONTINUOUS map, sphere-to-sphere, with a measurable
left inverse on the sphere: the composition of the per-block flow slices. This derives the
transport-map clause the paper attaches to its flow maps (eq. (B.2)) once and for all. Continuity
composes trivially through the induction (`hΦrc.comp hΦpc`) once `attnStep_exists_map` supplies it
per block. -/
theorem attnMeasureFlow_exists_map (θ : AttnSchedule d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    ∃ Φ Φinv : Eucl d → Eucl d, Measurable Φ ∧ Continuous Φ ∧ Measurable Φinv ∧
      attnMeasureFlow θ μ = μ.map Φ ∧ Set.MapsTo Φ (sphere d) (sphere d) ∧
      ∀ x ∈ sphere d, Φinv (Φ x) = x := by
  induction θ generalizing μ with
  | nil =>
    exact ⟨id, id, measurable_id, continuous_id, measurable_id, (Measure.map_id).symm,
      Set.mapsTo_id _, fun x _ => rfl⟩
  | cons p rest ih =>
    obtain ⟨Φp, Φpinv, hΦpm, hΦpc, hΦpim, hΦpeq, hΦpto, hΦpinv⟩ := attnStep_exists_map p μ hs
    haveI := isProbabilityMeasure_attnStep p μ hs
    have hs' : (attnStep p μ) (sphere d)ᶜ = 0 := attnStep_supportedIn_sphere p μ hs
    obtain ⟨Φr, Φrinv, hΦrm, hΦrc, hΦrim, hΦreq, hΦrto, hΦrinv⟩ := ih (attnStep p μ) hs'
    refine ⟨Φr ∘ Φp, Φpinv ∘ Φrinv, hΦrm.comp hΦpm, hΦrc.comp hΦpc, hΦpim.comp hΦrim, ?_,
      hΦrto.comp hΦpto, fun x hx => ?_⟩
    · have hcons : attnMeasureFlow (p :: rest) μ = attnMeasureFlow rest (attnStep p μ) := rfl
      rw [hcons, hΦreq, hΦpeq, Measure.map_map hΦrm hΦpm]
    · have hpx : Φp x ∈ sphere d := hΦpto hx
      simp only [Function.comp_apply]
      rw [hΦrinv (Φp x) hpx, hΦpinv x hx]

/-! ### The linear bridge, relocated from `MeanFieldWellPosed.lean`

These two theorems used to live in `MeanFieldWellPosed.lean`'s `MeanFieldBridge` section, consuming
the axiom directly; they move here for the same reason as `attnStep` above. -/

/-- **The linear bridge.** The attention step of a `V = 0` block coincides with the linear
pushforward along any `Block` whose field matches on the sphere: the block flow is a mean-field
flow (`isMeanFieldFlow_blockFlow`), uniqueness pins the chosen flow to it on the sphere, and sphere
support upgrades the pointwise agreement to equality of pushforwards. -/
theorem attnStep_eq_map_blockFlow (p : AttnParams d) (hV : p.V = 0) (b : Block d)
    (hagree : ∀ y ∈ sphere d, b.field y = tangentialProjector y (p.W (reluVec (p.U y + p.b))))
    (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀] (hs : μ₀ (sphere d)ᶜ = 0) :
    attnStep p μ₀ = μ₀.map (b.blockFlow p.duration) := by
  rw [attnStep, dif_pos ⟨‹IsProbabilityMeasure μ₀›, hs⟩]
  have hΦ := (@exists_meanFieldFlow d p μ₀ ‹_› hs).choose_spec
  have heq := meanFieldFlow_unique hs hΦ (isMeanFieldFlow_blockFlow b p hV hagree μ₀)
    p.duration ⟨p.duration_nonneg, le_rfl⟩
  refine Measure.map_congr ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hs
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
  exact fun hxs => hx (heq x hxs)

/-- The singleton-schedule form of the bridge: one `V = 0` piece is the linear block flow. -/
theorem attnMeasureFlow_singleton_eq_map_blockFlow (p : AttnParams d) (hV : p.V = 0)
    (b : Block d)
    (hagree : ∀ y ∈ sphere d, b.field y = tangentialProjector y (p.W (reluVec (p.U y + p.b))))
    (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀] (hs : μ₀ (sphere d)ᶜ = 0) :
    attnMeasureFlow [p] μ₀ = μ₀.map (b.blockFlow p.duration) :=
  attnStep_eq_map_blockFlow p hV b hagree μ₀ hs

end MeasureToMeasure.Foundations
