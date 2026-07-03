import Regression.OldStatements

/-!
# F12: `cluster_to_point` with an unrestricted target is false

The pre-F12 statement let the target `z` range over all of `Eucl d`, but the flow keeps sphere
mass on the sphere. Instantiate `μ = δ_e` (unit `e`) and `z = 3 • e`: every coupling of a
sphere-supported probability measure with `δ_z` transports each unit-norm point to `z`, at
distance at least `‖z‖ - 1 = 2`, so `W₂ ≥ 2 > 1 = ε`. Repaired in PR #66 (finding F12); the
statement moved to the mean-field layer in PR #69, and this disproof targets that layer
(`OldAttnClusterSig`), where the flow output is still a sphere-supported probability measure.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace ENNReal

/-- `(x ^ 2) ^ (1/2) = x` in `ℝ≥0∞`. -/
theorem ennreal_rpow_two_inv_two (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
  norm_num

/-- Any coupling of a sphere-supported measure with a far Dirac has squared transport cost at
least `(ofReal 2)²` per unit mass: a.e. the source point has norm `1` and the target is `z` with
`‖z‖ = 3`. -/
theorem sqTransportCost_ge_of_sphere_far {d : ℕ} {ν : Measure (Eucl d)}
    [IsProbabilityMeasure ν] (hνs : ν (MeasureToMeasure.sphere d)ᶜ = 0)
    {z : Eucl d} (hz : ‖z‖ = 3) {π : Measure (Eucl d × Eucl d)}
    (hπ : MeasureToMeasure.IsCoupling π ν (Measure.dirac z)) :
    ENNReal.ofReal 2 ^ 2 ≤ MeasureToMeasure.sqTransportCost π := by
  -- the first marginal keeps the first coordinate on the sphere a.e.
  have hms : MeasurableSet (MeasureToMeasure.sphere d)ᶜ :=
    Metric.isClosed_sphere.measurableSet.compl
  have h1 : π {xy : Eucl d × Eucl d | xy.1 ∉ MeasureToMeasure.sphere d} = 0 := by
    have hset : {xy : Eucl d × Eucl d | xy.1 ∉ MeasureToMeasure.sphere d}
        = Prod.fst ⁻¹' (MeasureToMeasure.sphere d)ᶜ := rfl
    rw [hset, ← Measure.fst_apply hms, hπ.1]
    exact hνs
  -- the second marginal pins the second coordinate to `z` a.e.
  have h2 : π {xy : Eucl d × Eucl d | ¬xy.2 = z} = 0 := by
    have hs : MeasurableSet ({z}ᶜ : Set (Eucl d)) :=
      (isClosed_singleton : IsClosed ({z} : Set (Eucl d))).measurableSet.compl
    have hset : {xy : Eucl d × Eucl d | ¬xy.2 = z} = Prod.snd ⁻¹' ({z}ᶜ : Set (Eucl d)) := by
      ext xy; simp
    rw [hset, ← Measure.snd_apply hs, hπ.2, Measure.dirac_apply' z hs,
      Set.indicator_of_notMem (by simp)]
  have hae : ∀ᵐ xy ∂π, xy.1 ∈ MeasureToMeasure.sphere d ∧ xy.2 = z := by
    have hae1 : ∀ᵐ xy ∂π, xy.1 ∈ MeasureToMeasure.sphere d := by rw [ae_iff]; exact h1
    have hae2 : ∀ᵐ xy ∂π, xy.2 = z := by rw [ae_iff]; exact h2
    exact hae1.and hae2
  have huniv : π Set.univ = 1 := by
    rw [← Measure.fst_univ, hπ.1]
    simp
  calc ENNReal.ofReal 2 ^ 2
      = ENNReal.ofReal 2 ^ 2 * π Set.univ := by rw [huniv, mul_one]
    _ = ∫⁻ _, ENNReal.ofReal 2 ^ 2 ∂π := (lintegral_const _).symm
    _ ≤ ∫⁻ xy, edist xy.1 xy.2 ^ 2 ∂π := by
        refine lintegral_mono_ae (hae.mono fun xy hxy => ?_)
        have hx1 : ‖xy.1‖ = 1 := by
          have := hxy.1
          simpa [MeasureToMeasure.sphere, mem_sphere_zero_iff_norm] using this
        have hdist : (2 : ℝ) ≤ dist xy.1 xy.2 := by
          rw [hxy.2, dist_eq_norm]
          have h := norm_sub_norm_le xy.1 z
          have h' : ‖z‖ - ‖xy.1‖ ≤ ‖xy.1 - z‖ := by
            have := norm_sub_norm_le z xy.1
            rw [norm_sub_rev] at this
            linarith
          rw [hz, hx1] at h'
          linarith
        have hedist : ENNReal.ofReal 2 ≤ edist xy.1 xy.2 := by
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal hdist
        exact pow_le_pow_left' hedist 2
    _ = MeasureToMeasure.sqTransportCost π := rfl

/-- The `ℝ≥0∞`-valued `W₂` from a sphere-supported probability measure to a Dirac at norm `3`
is at least `2`. -/
theorem W2_ge_two_of_sphere_far {d : ℕ} {ν : Measure (Eucl d)} [IsProbabilityMeasure ν]
    (hνs : ν (MeasureToMeasure.sphere d)ᶜ = 0) {z : Eucl d} (hz : ‖z‖ = 3) :
    ENNReal.ofReal 2 ≤ MeasureToMeasure.W2 ν (Measure.dirac z) := by
  unfold MeasureToMeasure.W2
  refine le_iInf fun π => le_iInf fun hπ => ?_
  calc ENNReal.ofReal 2
      = (ENNReal.ofReal 2 ^ 2) ^ (2⁻¹ : ℝ) := (ennreal_rpow_two_inv_two _).symm
    _ ≤ MeasureToMeasure.sqTransportCost π ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow (sqTransportCost_ge_of_sphere_far hνs hz hπ) (by norm_num)

/-- F12 (mean-field layer): `cluster_to_point` with the on-sphere restriction on `z` removed is
false -- the flowed measure stays a sphere-supported probability measure, and its `W₂` distance
to `δ_{3•e}` is at least `2 > 1 = ε`. -/
theorem oldAttnCluster_false (ax : Regression.OldAttnClusterSig) : False := by
  classical
  set e : Eucl 3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by simp [he_def]
  have hesph : e ∈ MeasureToMeasure.sphere 3 := by
    show e ∈ Metric.sphere (0 : Eucl 3) 1
    exact mem_sphere_zero_iff_norm.mpr he
  have hne : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at he
    exact zero_ne_one he
  -- δ_e is sphere-supported and lives in the open hemisphere around `e`
  have hμs : supportedIn (Measure.dirac e) (MeasureToMeasure.sphere 3) := by
    show Measure.dirac e (MeasureToMeasure.sphere 3)ᶜ = 0
    have hms : MeasurableSet (MeasureToMeasure.sphere 3)ᶜ :=
      (Metric.isClosed_sphere (x := (0 : Eucl 3)) (ε := 1)).measurableSet.compl
    rw [Measure.dirac_apply' _ hms,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hesph)]
  have hhemi : supportedIn (Measure.dirac e) {x : Eucl 3 | 0 < ⟪e, x⟫} := by
    have hSopen : IsOpen {x : Eucl 3 | 0 < ⟪e, x⟫} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_id)
    show Measure.dirac e {x : Eucl 3 | 0 < ⟪e, x⟫}ᶜ = 0
    have hee : (0 : ℝ) < ⟪e, e⟫ := by
      rw [real_inner_self_eq_norm_sq, he]; norm_num
    rw [Measure.dirac_apply' e hSopen.measurableSet.compl,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr
        (show e ∈ {x : Eucl 3 | 0 < ⟪e, x⟫} from hee))]
  obtain ⟨θ, hθ⟩ := ax (Measure.dirac e) (by infer_instance) (le_refl 3) 1 1 one_pos one_pos
    ((3 : ℝ) • e) e he hμs hhemi
  -- the flowed measure is a sphere-supported probability measure
  set ν : Measure (Eucl 3) := attnMeasureFlow θ (Measure.dirac e) with hν_def
  obtain ⟨hνprob, hνs⟩ :=
    MeasureToMeasure.Foundations.attnMeasureFlow_prob_supportedIn_sphere θ
      (Measure.dirac e) (by infer_instance) hμs
  haveI : IsProbabilityMeasure ν := hνprob
  -- `W₂(ν, δ_{3e})` is finite and at least 2, so the ℝ-valued interface is at least 2
  have hznorm : ‖(3 : ℝ) • e‖ = 3 := by
    rw [norm_smul, he, mul_one]; simp
  have hfin : MeasureToMeasure.W2 ν (Measure.dirac ((3 : ℝ) • e)) ≠ ⊤ := by
    refine MeasureToMeasure.W2_ne_top_of_ae_norm_le _ _ (R := 3) ?_ ?_
    · rw [ae_iff]
      refine measure_mono_null (fun y hy => ?_) hνs
      simp only [Set.mem_setOf_eq, not_le] at hy
      simp only [MeasureToMeasure.sphere, Set.mem_compl_iff, Metric.mem_sphere,
        dist_zero_right]
      intro hy1; rw [hy1] at hy; linarith
    · simp only [ae_dirac_eq, Filter.eventually_pure]
      rw [hznorm]
  have hge : ENNReal.ofReal 2 ≤ MeasureToMeasure.W2 ν (Measure.dirac ((3 : ℝ) • e)) :=
    W2_ge_two_of_sphere_far hνs hznorm
  have h2 : (2 : ℝ) ≤ Axioms.W2 ν (Measure.dirac ((3 : ℝ) • e)) := by
    show (2 : ℝ) ≤ (MeasureToMeasure.W2 ν (Measure.dirac ((3 : ℝ) • e))).toReal
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
    exact hge
  linarith

end Regression.Refuted
