import MeasureToMeasure.Foundations.SelfConsistencyStep

/-!
# The FTC representation of the trajectory-composed flow (M3b existence, leaf E3j)

The upcoming contraction estimate for the outer self-consistency map `Ξ` needs to compare, for two
*different* trial trajectories `η₁, η₂`, the difference of their trajectory-composed flows
`trajectoryFlow p hT η₁ x t - trajectoryFlow p hT η₂ x t`. The standard route (mirroring
`MeanFieldWellPosed.flow_sub_eq_integral_field`, the analogous FTC step for the mean-field
UNIQUENESS Grönwall) is to write each flow as `x + ∫₀ᵗ (field along the way)`, subtract, and bound
the resulting integral. This leaf supplies that representation for `trajectoryFlow`.

Two new facts feed it:

* `norm_attnFieldExt_sub_le` -- the JOINT modulus of `attnFieldExt` in `(measure, point)` together,
  a triangle-inequality combination of the already-banked point-Lipschitz
  (`attnFieldExt_lipschitz`) and measure-Lipschitz (E3c's `norm_attnFieldExt_sub_measure_le`)
  moduli. Not previously assembled because leaf E3c only needed the measure side at a *fixed*
  point, and leaf E2a only needed the point side at a *fixed* measure.
* `continuousOn_trajectoryField_comp` -- for ANY continuous point-trajectory `φ`, the composite
  `s ↦ trajectoryField p hT η s (φ s)` is continuous, from the same triangle-inequality split (the
  measure leg via leaf E3d's `continuous_attnFieldExt_comp_trajectory`, the point leg via
  `attnFieldExt_lipschitz`). This is what feeds `intervalIntegral.integral_eq_sub_of_hasDeriv_right`
  in `trajectoryFlow_sub_eq_integral_field`, exactly as `velocity_continuousOn` feeds
  `flow_sub_eq_integral_field` on the mean-field-uniqueness side.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **The joint `(measure, point)` modulus of `attnFieldExt`.** A triangle-inequality combination
of the point-Lipschitz modulus (`attnFieldExt_lipschitz`, uniform over any sphere-supported
measure) and the measure-Lipschitz modulus (E3c's `norm_attnFieldExt_sub_measure_le`, uniform over
any point). -/
theorem norm_attnFieldExt_sub_le (p : AttnParams d) {ν ν' : Measure (Eucl d)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (hνS : ν (sphere d)ᶜ = 0)
    (hν'S : ν' (sphere d)ᶜ = 0) (hW1 : W1 ν ν' ≠ ⊤) (x x' : Eucl d) :
    ‖attnFieldExt p ν x - attnFieldExt p ν' x'‖ ≤
      ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
        + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) * ‖x - x'‖ +
      (1 + ‖x'‖ ^ 2) *
        (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
        (W1 ν ν').toReal := by
  calc ‖attnFieldExt p ν x - attnFieldExt p ν' x'‖
      ≤ ‖attnFieldExt p ν x - attnFieldExt p ν x'‖ + ‖attnFieldExt p ν x' - attnFieldExt p ν' x'‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
          + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) * ‖x - x'‖ +
        (1 + ‖x'‖ ^ 2) *
          ((‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
          (W1 ν ν').toReal) := by
        gcongr
        · rw [← dist_eq_norm, ← dist_eq_norm]
          exact (attnFieldExt_lipschitz p ν hνS).dist_le_mul x x'
        · exact norm_attnFieldExt_sub_measure_le p hνS hν'S hW1 x'
    _ = _ := by ring

/-- **Continuity of the field composed with any continuous point-trajectory.** For a continuous
`φ : ℝ → Eucl d`, the composite `s ↦ trajectoryField p hT η s (φ s)` is continuous on `[0,T]` -- the
measure leg from leaf E3d, the point leg from `attnFieldExt_lipschitz`, combined by a triangle
inequality exactly as in `norm_attnFieldExt_sub_le`. -/
theorem continuousOn_trajectoryField_comp (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {φ : ℝ → Eucl d}
    (hφ : ContinuousOn φ (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (fun s => trajectoryField p hT η s (φ s)) (Set.Icc (0 : ℝ) T) := by
  intro s₀ hs₀
  set L : ℝ := ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
    + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) with hLdef
  have h1 : ContinuousWithinAt (fun s => attnFieldExt p (η (Set.projIcc 0 T hT s)).val (φ s₀))
      (Set.Icc (0 : ℝ) T) s₀ :=
    ((continuous_attnFieldExt_comp_trajectory p η (φ s₀)).comp
      continuous_projIcc).continuousAt.continuousWithinAt
  have h2 : ContinuousWithinAt (fun s => L * ‖φ s - φ s₀‖) (Set.Icc (0 : ℝ) T) s₀ := by
    have := (hφ.continuousWithinAt (x := s₀) hs₀).sub (continuousWithinAt_const (b := φ s₀))
    exact continuousWithinAt_const.mul this.norm
  rw [Metric.continuousWithinAt_iff] at h1 h2 ⊢
  intro ε hε
  obtain ⟨δ1, hδ1, hcond1⟩ := h1 (ε / 2) (by linarith)
  obtain ⟨δ2, hδ2, hcond2⟩ := h2 (ε / 2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs hdist => ?_⟩
  have hs1 := hcond1 hs (lt_of_lt_of_le hdist (min_le_left _ _))
  have hs2 := hcond2 hs (lt_of_lt_of_le hdist (min_le_right _ _))
  unfold trajectoryField
  haveI := (η (Set.projIcc 0 T hT s)).property.1
  have hbound : dist (attnFieldExt p (η (Set.projIcc 0 T hT s)).val (φ s))
      (attnFieldExt p (η (Set.projIcc 0 T hT s)).val (φ s₀)) ≤ L * ‖φ s - φ s₀‖ := by
    rw [dist_eq_norm]
    exact (attnFieldExt_lipschitz p (η (Set.projIcc 0 T hT s)).val
      (η (Set.projIcc 0 T hT s)).property.2).dist_le_mul (φ s) (φ s₀)
  have hdist_real : |L * ‖φ s - φ s₀‖ - 0| < ε / 2 := by simpa [Real.dist_eq] using hs2
  rw [sub_zero] at hdist_real
  have habs : L * ‖φ s - φ s₀‖ < ε / 2 := lt_of_abs_lt hdist_real
  calc dist (attnFieldExt p (η (Set.projIcc 0 T hT s)).val (φ s))
        (attnFieldExt p (η (Set.projIcc 0 T hT s₀)).val (φ s₀))
      ≤ dist (attnFieldExt p (η (Set.projIcc 0 T hT s)).val (φ s))
          (attnFieldExt p (η (Set.projIcc 0 T hT s)).val (φ s₀))
        + dist (attnFieldExt p (η (Set.projIcc 0 T hT s)).val (φ s₀))
          (attnFieldExt p (η (Set.projIcc 0 T hT s₀)).val (φ s₀)) := dist_triangle _ _ _
    _ ≤ L * ‖φ s - φ s₀‖
        + dist (attnFieldExt p (η (Set.projIcc 0 T hT s)).val (φ s₀))
          (attnFieldExt p (η (Set.projIcc 0 T hT s₀)).val (φ s₀)) := add_le_add hbound le_rfl
    _ < ε / 2 + ε / 2 := by linarith [habs, hs1]
    _ = ε := by ring

/-- **FTC representation of the trajectory-composed flow.** `trajectoryFlow p hT η x t - x` equals
the time-integral of the field along the way -- the identity a Grönwall-style contraction estimate
for two different trial trajectories will subtract and bound. Mirrors `MeanFieldWellPosed.
flow_sub_eq_integral_field` for the mean-field-uniqueness side. -/
theorem trajectoryFlow_sub_eq_integral_field (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    trajectoryFlow p hT η x t - x
      = ∫ s in (0 : ℝ)..t, trajectoryField p hT η s (trajectoryFlow p hT η x s) := by
  have hderiv : ∀ s ∈ Set.Ioo (min (0 : ℝ) t) (max (0 : ℝ) t),
      HasDerivWithinAt (trajectoryFlow p hT η x)
        (trajectoryField p hT η s (trajectoryFlow p hT η x s)) (Set.Ioi s) s := by
    intro s hs
    rw [min_eq_left ht.1, max_eq_right ht.1] at hs
    have hsIco : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1.le, hs.2.trans_le ht.2⟩
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self hsIco
    exact (hasDerivWithinAt_trajectoryFlow p hT η hx hsIcc).mono_of_mem_nhdsWithin
      (nhdsWithin_mono s Set.Ioi_subset_Ici_self (icc_mem_nhdsWithin_ici hsIco))
  have hcont : ContinuousOn (trajectoryFlow p hT η x) (Set.uIcc (0 : ℝ) t) := by
    rw [Set.uIcc_of_le ht.1]
    exact (continuousOn_trajectoryFlow p hT η hx).mono (Set.Icc_subset_Icc le_rfl ht.2)
  have hintble : IntervalIntegrable
      (fun s => trajectoryField p hT η s (trajectoryFlow p hT η x s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht.1]
    exact (continuousOn_trajectoryField_comp p hT η (continuousOn_trajectoryFlow p hT η hx)).mono
      (Set.Icc_subset_Icc le_rfl ht.2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hintble
  rw [trajectoryFlow_zero p hT η hx] at hftc
  exact hftc.symm

end MeasureToMeasure.Foundations
