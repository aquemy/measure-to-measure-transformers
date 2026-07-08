import MeasureToMeasure.Foundations.TrajectoryFlowFTC
import Mathlib.Analysis.ODE.Gronwall

/-!
# A Grönwall bound comparing the self-consistency map at two trial trajectories (M3b existence,
leaf E3k)

The genuine McKean-Vlasov contraction estimate for the outer self-consistency map `Ξ` (E3+) needs a
Grönwall bound comparing `Ξ η₁` and `Ξ η₂` for two *arbitrary* trial trajectories `η₁, η₂` -- not
two solutions of the same self-consistent system, so the mean-field UNIQUENESS Grönwall
(`MeanFieldWellPosed.meanFlowDist_le_integral`, which drives the distance to `0` because both sides
solve the SAME equation) does not directly transfer.

This leaf builds the pointwise (fixed sphere point `x`) comparison via Mathlib's
`dist_le_of_approx_trajectories_ODE_of_mem`: `trajectoryFlow p hT η₁ x` is an *exact* solution of
the reference field `v t y := attnFieldExt p (η₁ t).val y`, while `trajectoryFlow p hT η₂ x` is an
*approximate* solution of that same reference field, with a CONSTANT approximation error `εg = 2M ·
dist η₁ η₂` (the field's measure-modulus `M`, applied to the WORST-CASE deviation between `η₁` and
`η₂` over the whole interval, via `norm_attnFieldExt_sub_measure_le` from leaf E3c). This gives
`dist (trajectoryFlow p hT η₁ x t) (trajectoryFlow p hT η₂ x t) ≤ gronwallBound 0 K εg t`, then
`dist_pushforwardAt_sub_le_of_pointwise` transfers this pointwise bound to the pushforward level via
the same `W₁`-coupling argument leaf E3i uses.

**This is a genuine bound, but NOT yet the contraction.** Using the GLOBAL sup-distance `dist η₁ η₂`
as the forcing term (rather than the pointwise `dist (η₁ s) (η₂ s)` kept inside the integral) is
lossy: it gives `dist (Ξ η₁ t) (Ξ η₂ t) ≤ (2M/K)(e^{Kt}-1)·dist η₁ η₂` in the AMBIENT sup metric,
which is not a contraction for general `T` and does not involve `bieleckiDist` at all. The genuine
McKean-Vlasov contraction needs a Grönwall variant with a TIME-VARYING forcing bound `dist (η₁ s)
(η₂ s) ≤ e^{λs}·bieleckiDist η₁ η₂` kept inside the integral against the kernel `e^{K(t-s)}`, giving
`dist (Ξ η₁ t) (Ξ η₂ t) ≤ (2M/(λ-K))·(e^{λt}-e^{Kt})·bieleckiDist η₁ η₂ ≤ (2M/(λ-K))·e^{λt}·
bieleckiDist η₁ η₂`, i.e. `bieleckiDist (Ξ η₁) (Ξ η₂) ≤ (2M/(λ-K))·bieleckiDist η₁ η₂` -- a genuine
contraction once `λ > K + 2M`. Mathlib's `dist_le_of_approx_trajectories_ODE_of_mem` only accepts a
CONSTANT approximation error, so this variable-forcing Grönwall needs to be built by hand, mirroring
`MeanFieldWellPosed.gronwall_integral_zero`'s antiderivative trick but with a nonzero, genuinely
time-dependent forcing term (that lemma drives its functional to exactly `0`; here the target is a
nonzero exponential bound).

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **Pointwise Grönwall bound comparing the trajectory-composed flow at two trial trajectories.**
`trajectoryFlow p hT η₁ x` solves the reference field exactly; `trajectoryFlow p hT η₂ x`
approximately, with constant error `2M·dist η₁ η₂` (E3c's measure-Lipschitz modulus applied to the
worst-case trajectory deviation). Via Mathlib's `dist_le_of_approx_trajectories_ODE_of_mem`. -/
theorem dist_trajectoryFlow_sub_le_gronwallBound (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      dist (trajectoryFlow p hT η₁ x t) (trajectoryFlow p hT η₂ x t) ≤
        gronwallBound 0
          ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
            + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ)
          (2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
            dist η₁ η₂) t := by
  set K : ℝ≥0 := Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
    + Real.toNNReal (5 * fieldBallBound p) with hK
  set M : ℝ := ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) with hM
  set εg : ℝ := 2 * M * dist η₁ η₂ with hεg
  have hv : ∀ t : ℝ,
      LipschitzWith K (fun y => attnFieldExt p (η₁ (Set.projIcc 0 T hT t)).val y) := by
    intro t
    haveI := (η₁ (Set.projIcc 0 T hT t)).property.1
    exact attnFieldExt_lipschitz p (η₁ (Set.projIcc 0 T hT t)).val
      (η₁ (Set.projIcc 0 T hT t)).property.2
  have hf : ContinuousOn (trajectoryFlow p hT η₁ x) (Set.Icc (0 : ℝ) T) :=
    continuousOn_trajectoryFlow p hT η₁ hx
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (trajectoryFlow p hT η₁ x)
        (trajectoryField p hT η₁ t (trajectoryFlow p hT η₁ x t)) (Set.Ici t) t := by
    intro t ht
    exact (hasDerivWithinAt_trajectoryFlow p hT η₁ hx
      (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (icc_mem_nhdsWithin_ici ht)
  have hg : ContinuousOn (trajectoryFlow p hT η₂ x) (Set.Icc (0 : ℝ) T) :=
    continuousOn_trajectoryFlow p hT η₂ hx
  have hg' : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (trajectoryFlow p hT η₂ x)
        (trajectoryField p hT η₂ t (trajectoryFlow p hT η₂ x t)) (Set.Ici t) t := by
    intro t ht
    exact (hasDerivWithinAt_trajectoryFlow p hT η₂ hx
      (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (icc_mem_nhdsWithin_ici ht)
  have hf_bound : ∀ t ∈ Set.Ico (0 : ℝ) T,
      dist (trajectoryField p hT η₁ t (trajectoryFlow p hT η₁ x t))
        ((fun y => attnFieldExt p (η₁ (Set.projIcc 0 T hT t)).val y) (trajectoryFlow p hT η₁ x t))
        ≤ (0 : ℝ) := by
    intro t _
    unfold trajectoryField
    rw [dist_self]
  have hg_bound : ∀ t ∈ Set.Ico (0 : ℝ) T,
      dist (trajectoryField p hT η₂ t (trajectoryFlow p hT η₂ x t))
        ((fun y => attnFieldExt p (η₁ (Set.projIcc 0 T hT t)).val y) (trajectoryFlow p hT η₂ x t))
        ≤ εg := by
    intro t ht
    unfold trajectoryField
    haveI := (η₁ (Set.projIcc 0 T hT t)).property.1
    haveI := (η₂ (Set.projIcc 0 T hT t)).property.1
    rw [dist_eq_norm]
    have hW1ne : W1 (η₂ (Set.projIcc 0 T hT t)).val (η₁ (Set.projIcc 0 T hT t)).val ≠ ⊤ :=
      SphereProb.w1dist_ne_top _ _
    have hle := norm_attnFieldExt_sub_measure_le p (η₂ (Set.projIcc 0 T hT t)).property.2
      (η₁ (Set.projIcc 0 T hT t)).property.2 hW1ne (trajectoryFlow p hT η₂ x t)
    have hWeq : (W1 (η₂ (Set.projIcc 0 T hT t)).val (η₁ (Set.projIcc 0 T hT t)).val).toReal
        = dist (η₂ (Set.projIcc 0 T hT t)) (η₁ (Set.projIcc 0 T hT t)) :=
      (SphereProb.dist_eq _ _).symm
    rw [hWeq] at hle
    have hdistcomm : dist (η₂ (Set.projIcc 0 T hT t)) (η₁ (Set.projIcc 0 T hT t))
        ≤ dist η₁ η₂ := by rw [dist_comm]; exact ContinuousMap.dist_apply_le_dist _
    have hxsphere : trajectoryFlow p hT η₂ x t ∈ sphere d := trajectoryFlow_mem_sphere p hT η₂ hx
      (Set.Ico_subset_Icc_self ht)
    have hxnorm : ‖trajectoryFlow p hT η₂ x t‖ = 1 := norm_eq_one_of_mem_sphere hxsphere
    have hMnn : (0 : ℝ) ≤ M := by rw [hM]; positivity
    calc ‖attnFieldExt p (η₂ (Set.projIcc 0 T hT t)).val (trajectoryFlow p hT η₂ x t)
          - attnFieldExt p (η₁ (Set.projIcc 0 T hT t)).val (trajectoryFlow p hT η₂ x t)‖
        ≤ (1 + ‖trajectoryFlow p hT η₂ x t‖ ^ 2) *
          (M * dist (η₂ (Set.projIcc 0 T hT t)) (η₁ (Set.projIcc 0 T hT t))) := hle
      _ = 2 * (M * dist (η₂ (Set.projIcc 0 T hT t)) (η₁ (Set.projIcc 0 T hT t))) := by
          rw [hxnorm]; norm_num
      _ ≤ 2 * (M * dist η₁ η₂) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdistcomm hMnn) (by norm_num)
      _ = εg := by rw [hεg]; ring
  have hstart : dist (trajectoryFlow p hT η₁ x 0) (trajectoryFlow p hT η₂ x 0) ≤ (0 : ℝ) := by
    rw [trajectoryFlow_zero p hT η₁ hx, trajectoryFlow_zero p hT η₂ hx, dist_self]
  intro t ht
  have := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun t y => attnFieldExt p (η₁ (Set.projIcc 0 T hT t)).val y) (s := fun _ => Set.univ)
    (a := (0 : ℝ)) (b := T) (K := K) (fun t _ => (hv t).lipschitzOnWith)
    hf hf' hf_bound (fun _ _ => Set.mem_univ _)
    hg hg' hg_bound (fun _ _ => Set.mem_univ _) hstart t ht
  rwa [zero_add, sub_zero] at this

theorem norm_trajectoryFlowExt_sub_le_two' (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {x : Eucl d} (hx : x ∈ sphere d) :
    ‖trajectoryFlowExt p hT η₁ t x - trajectoryFlowExt p hT η₂ t x‖ ≤ 2 := by
  rw [trajectoryFlowExt_eq_of_mem_sphere p hT η₁ hx, trajectoryFlowExt_eq_of_mem_sphere p hT η₂ hx]
  have h1 : trajectoryFlow p hT η₁ x t ∈ sphere d := trajectoryFlow_mem_sphere p hT η₁ hx ht
  have h2 : trajectoryFlow p hT η₂ x t ∈ sphere d := trajectoryFlow_mem_sphere p hT η₂ hx ht
  calc ‖trajectoryFlow p hT η₁ x t - trajectoryFlow p hT η₂ x t‖
      ≤ ‖trajectoryFlow p hT η₁ x t‖ + ‖trajectoryFlow p hT η₂ x t‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_eq_one_of_mem_sphere h1, norm_eq_one_of_mem_sphere h2]; norm_num

theorem integrable_norm_trajectoryFlowExt_sub' (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun x => ‖trajectoryFlowExt p hT η₁ t x - trajectoryFlowExt p hT η₂ t x‖) μ₀ := by
  refine Integrable.mono' (integrable_const (2 : ℝ))
    (((measurable_trajectoryFlowExt p hT η₁ ht).sub
      (measurable_trajectoryFlowExt p hT η₂ ht)).norm.aestronglyMeasurable) ?_
  refine ae_of_sphere_supported hμ₀ (fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_trajectoryFlowExt_sub_le_two' p hT η₁ η₂ ht hy

/-- **Transfer of a pointwise (`μ₀`-a.e. sphere) bound to the pushforward level**, via the same
`W₁`-coupling argument leaf E3i uses. -/
theorem dist_pushforwardAt_sub_le_of_pointwise (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (B : ℝ)
    (hpt : ∀ x ∈ sphere d, dist (trajectoryFlow p hT η₁ x t) (trajectoryFlow p hT η₂ x t) ≤ B) :
    dist (pushforwardAt p hT η₁ μ₀ hμ₀ ht) (pushforwardAt p hT η₂ μ₀ hμ₀ ht) ≤ B := by
  have hint := integrable_norm_trajectoryFlowExt_sub' p hT η₁ η₂ μ₀ hμ₀ ht
  have hbound_int : dist (pushforwardAt p hT η₁ μ₀ hμ₀ ht) (pushforwardAt p hT η₂ μ₀ hμ₀ ht)
      ≤ ∫ x, ‖trajectoryFlowExt p hT η₁ t x - trajectoryFlowExt p hT η₂ t x‖ ∂μ₀ := by
    unfold pushforwardAt
    rw [SphereProb.dist_eq]
    exact W1_toReal_map_le_integral_norm (measurable_trajectoryFlowExt p hT η₁ ht)
      (measurable_trajectoryFlowExt p hT η₂ ht) hint
  have hae : (fun x => ‖trajectoryFlowExt p hT η₁ t x - trajectoryFlowExt p hT η₂ t x‖)
      ≤ᵐ[μ₀] (fun _ => B) := by
    apply ae_of_sphere_supported hμ₀
    intro y hy
    show ‖trajectoryFlowExt p hT η₁ t y - trajectoryFlowExt p hT η₂ t y‖ ≤ B
    rw [trajectoryFlowExt_eq_of_mem_sphere p hT η₁ hy,
      trajectoryFlowExt_eq_of_mem_sphere p hT η₂ hy, ← dist_eq_norm]
    exact hpt y hy
  have hintle := integral_mono_ae hint (integrable_const B) hae
  rw [integral_const] at hintle
  simp only [Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul] at hintle
  exact hbound_int.trans hintle

/-- **The composed Grönwall bound at the pushforward level.** Not yet a contraction (see module
docstring): the constant forcing term `dist η₁ η₂` (ambient sup metric) is too lossy for the
Bielecki argument, which needs the pointwise `dist (η₁ s) (η₂ s)` kept inside the Grönwall integral. -/
theorem dist_pushforwardAt_le_gronwallBound (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ (sphere d)ᶜ = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    dist (pushforwardAt p hT η₁ μ₀ hμ₀ ht) (pushforwardAt p hT η₂ μ₀ hμ₀ ht) ≤
      gronwallBound 0
        ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
          + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ)
        (2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
          dist η₁ η₂) t :=
  dist_pushforwardAt_sub_le_of_pointwise p hT η₁ η₂ μ₀ hμ₀ ht _
    (fun _ hx => dist_trajectoryFlow_sub_le_gronwallBound p hT η₁ η₂ hx t ht)

end MeasureToMeasure.Foundations
