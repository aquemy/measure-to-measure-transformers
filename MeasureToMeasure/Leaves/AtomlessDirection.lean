import MeasureToMeasure.Foundations.Sphere
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# A generic direction whose scalar projection is atomless (Proposition 2.2, Step A)

`prop_2_2` (Appendix, "Clustering to discrete measures with connected preimages") needs a
connected-prescribed-mass partition of the sphere. The construction slices along a single
direction `u`: sweep a threshold `t` and cut `{x | ⟪u,x⟫ ≤ t}` where the running mass first hits
each target. This only works if the *pushforward* `⟨u,·⟩_*μ0` has no atoms -- otherwise a single
threshold could carry positive mass and no cut lands exactly on a prescribed target.

**The genericity argument.** For an arbitrary atomless `μ0`, a single fixed `u` need not work (e.g.
`μ0` could itself concentrate mass on a level set of `⟪u,·⟩`), but *almost every* `u` does. The
proof is Fubini/Tonelli on pairs: `⟪u,x-y⟫=0` for a `μ0×μ0`-positive-mass set of pairs would force
`(μ0.prod μ0){p | ⟪u,p.1-p.2⟫=0} > 0`; integrating this quantity over `u` and swapping the order of
integration collapses it to an inner integral that is exactly the `toSphere`-measure of a *proper
subspace's* trace on the sphere (a "great subsphere"), which is Haar-null (`toSphere_ker_null`).
So the double integral is `0`, hence (nonneg integrand) the per-`u` quantity vanishes for
`σ`-a.e. `u`. A vanishing `(μ0.prod μ0){p|⟪u,p.1-p.2⟫=0}` rules out *every* level set of
`⟪u,·⟩` having positive `μ0`-mass simultaneously (a positive-mass level set for level `c` would
witness `{x|⟪u,x⟫=c}×{x|⟪u,x⟫=c} ⊆ {p|⟪u,p.1-p.2⟫=0}`, forcing the containing set's measure to be
`≥ m² > 0`) -- so the "good" `u`'s pushforward is atomless in the strongest sense: no level set at
all, for any `c`, carries positive mass. Since the "good" set has full (nonzero) `σ`-measure, it is
nonempty.

M3b/mid-level staging: Step A of the `prop_2_2` partition construction; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace Pointwise
open MeasureToMeasure

variable {d : ℕ}

/-- **The "long pole": a great subsphere is `toSphere`-null.** For `v ≠ 0`, the subsphere
`{u | ⟪u,v⟫=0}` (the trace of a proper hyperplane) has zero `toSphere`-measure -- its radial cone
sits inside the proper submodule `ker(⟪·,v⟫)`, which is Haar-null. -/
theorem toSphere_ker_null (v : Eucl d) (hv : v ≠ 0) :
    (volume : Measure (Eucl d)).toSphere {u : Metric.sphere (0:Eucl d) 1 | (⟪(u:Eucl d), v⟫ : ℝ) = 0} = 0 := by
  have hmeas : MeasurableSet {u : Metric.sphere (0:Eucl d) 1 | (⟪(u:Eucl d), v⟫ : ℝ) = 0} := by
    apply measurableSet_eq_fun (by fun_prop) measurable_const
  rw [(volume : Measure (Eucl d)).toSphere_apply' hmeas]
  set K : Submodule ℝ (Eucl d) :=
    ((innerSL ℝ v : Eucl d →L[ℝ] ℝ) : Eucl d →ₗ[ℝ] ℝ).ker with hKdef
  have hsub : Set.Ioo (0:ℝ) 1 • ((↑) '' {u : Metric.sphere (0:Eucl d) 1 | (⟪(u:Eucl d), v⟫ : ℝ) = 0})
      ⊆ (K : Set (Eucl d)) := by
    rintro x ⟨t, u, ht, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hu
    simp only [Set.mem_setOf_eq] at hw
    simp only [hKdef, SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply]
    rw [real_inner_smul_right, real_inner_comm v (w : Eucl d)] at *
    rw [hw, mul_zero]
  have hK_ne_top : K ≠ ⊤ := by
    intro hcon
    have hvmem : v ∈ K := by rw [hcon]; trivial
    rw [hKdef, LinearMap.mem_ker] at hvmem
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hvmem
    rw [real_inner_self_eq_norm_sq] at hvmem
    exact hv (by simpa using hvmem)
  have hnull : (volume : Measure (Eucl d)) (K : Set (Eucl d)) = 0 :=
    Measure.addHaar_submodule volume K hK_ne_top
  have hzero := measure_mono_null hsub hnull
  rw [hzero]
  simp

/-- **The Fubini/Tonelli collapse.** Integrating `u ↦ (μ0.prod μ0){p | ⟪u,p.1-p.2⟫=0}` over the
sphere gives `0`: swap the integration order, then the inner integral (over `u`, for fixed `p`)
is `σ univ` on the null diagonal `p.1=p.2` and `0` off it (via `toSphere_ker_null`), and the
diagonal is `(μ0.prod μ0)`-null since `μ0` is atomless. -/
theorem lintegral_prod_diag_eq_zero (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    [NoAtoms μ0] :
    ∫⁻ u : Metric.sphere (0:Eucl d) 1,
      (μ0.prod μ0) {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0}
      ∂(volume : Measure (Eucl d)).toSphere = 0 := by
  set σ := (volume : Measure (Eucl d)).toSphere with hσ
  have step1 : ∫⁻ u : Metric.sphere (0:Eucl d) 1,
        (μ0.prod μ0) {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0} ∂σ
      = ∫⁻ u : Metric.sphere (0:Eucl d) 1, ∫⁻ p : Eucl d × Eucl d,
          Set.indicator {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0}
            (1 : Eucl d × Eucl d → ENNReal) p ∂(μ0.prod μ0) ∂σ := by
    apply lintegral_congr
    intro u
    rw [lintegral_indicator_one (measurableSet_eq_fun (by fun_prop) measurable_const)]
  have step2 : ∫⁻ u : Metric.sphere (0:Eucl d) 1, ∫⁻ p : Eucl d × Eucl d,
        Set.indicator {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0}
          (1 : Eucl d × Eucl d → ENNReal) p ∂(μ0.prod μ0) ∂σ
      = ∫⁻ p : Eucl d × Eucl d, ∫⁻ u : Metric.sphere (0:Eucl d) 1,
          Set.indicator {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0}
            (1 : Eucl d × Eucl d → ENNReal) p ∂σ ∂(μ0.prod μ0) := by
    apply lintegral_lintegral_swap
    apply Measurable.aemeasurable
    have hmeasUP : MeasurableSet {q : (Metric.sphere (0:Eucl d) 1) × (Eucl d × Eucl d) |
        (⟪(q.1:Eucl d), q.2.1 - q.2.2⟫ : ℝ) = 0} := by
      apply measurableSet_eq_fun
      · exact (Continuous.inner (by fun_prop) (by fun_prop)).measurable
      · fun_prop
    have huncurry : (Function.uncurry fun (u : Metric.sphere (0:Eucl d) 1) (p : Eucl d × Eucl d) =>
        Set.indicator {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0}
          (1 : Eucl d × Eucl d → ENNReal) p)
        = Set.indicator {q : (Metric.sphere (0:Eucl d) 1) × (Eucl d × Eucl d) |
            (⟪(q.1:Eucl d), q.2.1 - q.2.2⟫ : ℝ) = 0}
            (1 : (Metric.sphere (0:Eucl d) 1) × (Eucl d × Eucl d) → ENNReal) := by
      ext q
      simp only [Function.uncurry, Set.indicator]
      by_cases h : (⟪(q.1:Eucl d), q.2.1 - q.2.2⟫ : ℝ) = 0 <;> simp [h]
    rw [huncurry]
    exact Measurable.indicator measurable_const hmeasUP
  have step3 : ∀ p : Eucl d × Eucl d, ∫⁻ u : Metric.sphere (0:Eucl d) 1,
        Set.indicator {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0}
          (1 : Eucl d × Eucl d → ENNReal) p ∂σ
      = if p.1 = p.2 then σ Set.univ else 0 := by
    intro p
    by_cases hpq : p.1 = p.2
    · rw [if_pos hpq]
      have hind1 : ∀ u : Metric.sphere (0:Eucl d) 1,
          Set.indicator {q : Eucl d × Eucl d | (⟪(u:Eucl d), q.1 - q.2⟫ : ℝ) = 0}
            (1 : Eucl d × Eucl d → ENNReal) p = 1 := by
        intro u
        simp only [Set.indicator_apply, Set.mem_setOf_eq, hpq, sub_self, inner_zero_right,
          if_true, Pi.one_apply]
      rw [lintegral_congr (μ := σ) hind1, lintegral_const, one_mul]
    · rw [if_neg hpq]
      have heq2 : ∀ u : Metric.sphere (0:Eucl d) 1,
          Set.indicator {q : Eucl d × Eucl d | (⟪(u:Eucl d), q.1 - q.2⟫ : ℝ) = 0}
            (1 : Eucl d × Eucl d → ENNReal) p
          = Set.indicator {w : Metric.sphere (0:Eucl d) 1 | (⟪(w:Eucl d), p.1 - p.2⟫ : ℝ) = 0}
              (1 : Metric.sphere (0:Eucl d) 1 → ENNReal) u := by
        intro u
        simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      rw [lintegral_congr (μ := σ) heq2,
        lintegral_indicator_one (measurableSet_eq_fun (by fun_prop) measurable_const),
        toSphere_ker_null (p.1 - p.2) (sub_ne_zero.mpr hpq)]
  rw [step1, step2]
  have step4 : ∫⁻ p : Eucl d × Eucl d, (if p.1 = p.2 then σ Set.univ else (0:ENNReal)) ∂(μ0.prod μ0)
      = 0 := by
    have hdiag : MeasurableSet {p : Eucl d × Eucl d | p.1 = p.2} := isClosed_diagonal.measurableSet
    have hdiagnull : (μ0.prod μ0) {p : Eucl d × Eucl d | p.1 = p.2} = 0 := by
      rw [Measure.prod_apply hdiag]; simp
    have hae : ∀ᵐ p ∂(μ0.prod μ0), (if p.1 = p.2 then σ Set.univ else (0:ENNReal)) = 0 := by
      rw [ae_iff]
      have hsub : {p : Eucl d × Eucl d | ¬ (if p.1 = p.2 then σ Set.univ else (0:ENNReal)) = 0}
          ⊆ {p : Eucl d × Eucl d | p.1 = p.2} := by
        intro p hp
        by_contra hcon
        exact hp (if_neg hcon)
      exact measure_mono_null hsub hdiagnull
    rw [lintegral_congr_ae hae]
    simp
  rw [lintegral_congr (μ := μ0.prod μ0) step3, step4]

/-- Measurability of the integrand of `lintegral_prod_diag_eq_zero`, needed to turn "the integral
vanishes" into "the integrand vanishes a.e." -/
theorem measurable_prod_diag_measure (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    [NoAtoms μ0] :
    Measurable (fun u : Metric.sphere (0:Eucl d) 1 =>
      (μ0.prod μ0) {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0}) := by
  have hmeasUP : MeasurableSet {q : (Metric.sphere (0:Eucl d) 1) × (Eucl d × Eucl d) |
      (⟪(q.1:Eucl d), q.2.1 - q.2.2⟫ : ℝ) = 0} := by
    apply measurableSet_eq_fun
    · exact (Continuous.inner (by fun_prop) (by fun_prop)).measurable
    · fun_prop
  have hf : Measurable (Set.indicator {q : (Metric.sphere (0:Eucl d) 1) × (Eucl d × Eucl d) |
      (⟪(q.1:Eucl d), q.2.1 - q.2.2⟫ : ℝ) = 0} (1 : (Metric.sphere (0:Eucl d) 1) × (Eucl d × Eucl d) → ENNReal)) :=
    Measurable.indicator measurable_const hmeasUP
  have hlint := hf.lintegral_prod_right' (ν := μ0.prod μ0)
  have heq : (fun u : Metric.sphere (0:Eucl d) 1 => ∫⁻ p : Eucl d × Eucl d,
        Set.indicator {q : (Metric.sphere (0:Eucl d) 1) × (Eucl d × Eucl d) |
          (⟪(q.1:Eucl d), q.2.1 - q.2.2⟫ : ℝ) = 0}
          (1 : (Metric.sphere (0:Eucl d) 1) × (Eucl d × Eucl d) → ENNReal) (u, p) ∂(μ0.prod μ0))
      = (fun u : Metric.sphere (0:Eucl d) 1 =>
          (μ0.prod μ0) {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0}) := by
    funext u
    rw [← lintegral_indicator_one (measurableSet_eq_fun (α := Eucl d × Eucl d)
      (f := fun p => (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ)) (by fun_prop) measurable_const)]
    apply lintegral_congr
    intro p
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [heq] at hlint
  exact hlint

/-- **A generic direction whose scalar projection is atomless.** For any atomless probability
measure `μ0` on `Eucl d` (`d ≥ 1`), some unit direction `u` has NO level set of `⟪u,·⟩` carrying
positive `μ0`-mass -- i.e. `⟨u,·⟩_*μ0` is atomless. This is Step A of `prop_2_2`'s
connected-prescribed-mass partition: slicing along such a `u` by threshold never has to cut through
a mass-carrying level set. -/
theorem exists_atomless_direction (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0] [NoAtoms μ0]
    [NeZero d] :
    ∃ u : Metric.sphere (0:Eucl d) 1, ∀ c : ℝ, μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) = c} = 0 := by
  set σ := (volume : Measure (Eucl d)).toSphere with hσ
  have hσpos_univ : σ Set.univ ≠ 0 := by
    rw [hσ, MeasureTheory.Measure.toSphere_apply_univ]
    have h1 : (Module.finrank ℝ (Eucl d) : ENNReal) ≠ 0 := by
      have : Module.finrank ℝ (Eucl d) ≠ 0 := by
        rw [finrank_euclideanSpace_fin]; exact NeZero.ne d
      exact_mod_cast this
    have h2 : (volume : Measure (Eucl d)) (Metric.ball 0 1) ≠ 0 :=
      (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
    exact mul_ne_zero h1 h2
  have hσpos : σ ≠ 0 := fun h => hσpos_univ (by rw [h]; simp)
  have hae : ∀ᵐ (u : Metric.sphere (0:Eucl d) 1) ∂σ,
      (μ0.prod μ0) {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0} = 0 :=
    (lintegral_eq_zero_iff (measurable_prod_diag_measure μ0)).mp (lintegral_prod_diag_eq_zero μ0)
  haveI : (ae σ).NeBot := ae_neBot.mpr hσpos
  obtain ⟨u, hu⟩ := hae.exists
  refine ⟨u, fun c => ?_⟩
  by_contra hcne
  set S : Set (Eucl d) := {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) = c} with hSdef
  set m := μ0 S with hmdef
  have hmpos : 0 < m := zero_lt_iff.mpr hcne
  have hsq : S ×ˢ S ⊆ {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [hSdef, Set.mem_setOf_eq] at hx hy
    simp only [Set.mem_setOf_eq, inner_sub_right, hx, hy, sub_self]
  have hle : m * m ≤ 0 := by
    calc m * m = (μ0.prod μ0) (S ×ˢ S) := (Measure.prod_prod S S).symm
      _ ≤ (μ0.prod μ0) {p : Eucl d × Eucl d | (⟪(u:Eucl d), p.1 - p.2⟫ : ℝ) = 0} := measure_mono hsq
      _ = 0 := hu
  have hne : m * m ≠ 0 := mul_ne_zero hmpos.ne' hmpos.ne'
  exact hne (nonpos_iff_eq_zero.mp hle)

end MeasureToMeasure.Leaves
