import Regression.OldStatements
import Mathlib.Analysis.Calculus.MeanValue

/-!
# F31: `lemma_5_4` is false without a dimension hypothesis (dimension one)

`lemma_5_4` (`L²` approximation of a transport map by a mean-field flow map) was stated for
arbitrary `d`. Instantiating at `d = 1` refutes that form, by the same freezing mechanism as F18
but one layer up, on the MEAN-FIELD dynamics: in `Eucl 1` the tangential projector at a unit
point annihilates every vector (`tangentialProjector_eq_zero_dim_one`), so `AttnParams.field`
vanishes at every sphere point for every parameter block and every current measure
(`attnField_eq_zero_dim_one`). Any `IsMeanFieldFlow` therefore has zero characteristic
derivative along `[0, duration]` and freezes sphere points
(`meanFieldFlow_frozen_dim_one`, via `constant_of_has_deriv_right_zero`); hence every
`attnStep` fixes the sphere Dirac `δ_e` exactly (`attnStep_dirac_dim_one`) and, by induction,
so does `attnMeasureFlow θ` for every schedule (`attnMeasureFlow_dirac_dim_one`). Against
`μ = δ_e`, `ψ = const (-e)`, `T = ε = 1` -- data satisfying every hypothesis -- every
approximant `ψε` must satisfy `δ_e = δ_{ψε e}`, forcing `ψε e = e` and `L²` error
`‖-e - e‖ = 2 ≰ 1`.

Repaired by adding `hd : 3 ≤ d` to `lemma_5_4` (finding F31), the paper's standing scope
(Theorem 1.2, p.5: "Suppose `d ⩾ 3`") and the hypothesis its sole consumer `theorem_1_2`
already carries. This file kernel-checks `Regression.OldLemma54NoDimSig → False`; the repaired
axiom carries `3 ≤ d`, so it cannot reproduce this signature (must-fail adapter:
`Refutations/F31_lemma_5_4_dim_free.lean`).
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements MeasureToMeasure.Foundations
open scoped RealInnerProductSpace

/-- In `Eucl 1` the tangential projector at a unit point annihilates every vector: with
`x₀² = 1`, the coordinate identity gives `v₀ - (x₀ v₀) x₀ = 0`. -/
theorem tangentialProjector_eq_zero_dim_one {x : Eucl 1} (hx : ‖x‖ = 1) (v : Eucl 1) :
    tangentialProjector x v = 0 := by
  have hxabs : |x 0| = 1 := by
    rw [← hx, EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]
  have hxx : x 0 * x 0 = 1 := by
    rw [← abs_mul_abs_self, hxabs]; norm_num
  have hinner : (⟪x, v⟫ : ℝ) = x 0 * v 0 := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  rw [tangentialProjector_apply]
  ext i
  rw [Subsingleton.elim i (0 : Fin 1)]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
  rw [hinner]
  linear_combination (-(v 0)) * hxx

/-- In dimension one the attention field vanishes at every sphere point, for every parameter
block and every current measure: the field is a tangential projection at a unit point. -/
theorem attnField_eq_zero_dim_one (p : AttnParams 1) (ν : Measure (Eucl 1)) {y : Eucl 1}
    (hy : ‖y‖ = 1) : p.field ν y = 0 :=
  tangentialProjector_eq_zero_dim_one hy _

/-- Any mean-field flow in dimension one freezes sphere points: the characteristic derivative is
the (vanishing) field along the sphere-confined trajectory, so the trajectory is constant on
`[0, duration]`. -/
theorem meanFieldFlow_frozen_dim_one (p : AttnParams 1) (μ₀ : Measure (Eucl 1))
    {Φ : ℝ → Eucl 1 → Eucl 1} (h : IsMeanFieldFlow p μ₀ Φ)
    {x : Eucl 1} (hx : x ∈ MeasureToMeasure.sphere 1) :
    Φ p.duration x = x := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) p.duration, HasDerivAt (fun s => Φ s x) 0 t := by
    intro t ht
    have hmem : Φ t x ∈ MeasureToMeasure.sphere 1 := (h.sphere_bijOn t ht).mapsTo hx
    have hnorm : ‖Φ t x‖ = 1 := by
      rw [MeasureToMeasure.sphere, Metric.mem_sphere, dist_zero_right] at hmem
      exact hmem
    have hd := h.deriv x hx t ht
    rwa [attnField_eq_zero_dim_one p _ hnorm] at hd
  have hcont : ContinuousOn (fun s => Φ s x) (Set.Icc 0 p.duration) :=
    fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hderiv t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt)
  have hval := hconst p.duration ⟨p.duration_nonneg, le_rfl⟩
  rw [hval, h.init]
  rfl

/-- In dimension one a single attention step fixes any sphere Dirac exactly: the step is the
pushforward along the chosen mean-field flow at the block duration, and that flow freezes the
atom. -/
theorem attnStep_dirac_dim_one (p : AttnParams 1) {e : Eucl 1}
    (he : e ∈ MeasureToMeasure.sphere 1) :
    attnStep p (Measure.dirac e) = Measure.dirac e := by
  have hs : Measure.dirac e (MeasureToMeasure.sphere 1)ᶜ = 0 := by
    have hms : MeasurableSet (MeasureToMeasure.sphere 1) := Metric.isClosed_sphere.measurableSet
    rw [Measure.dirac_apply' _ hms.compl, Set.indicator_of_notMem (not_not_intro he)]
  rw [attnStep, dif_pos ⟨(inferInstance : IsProbabilityMeasure (Measure.dirac e)), hs⟩]
  have hspec := (exists_meanFieldFlow p (Measure.dirac e) hs).choose_spec
  show (Measure.dirac e).map ((exists_meanFieldFlow p (Measure.dirac e) hs).choose p.duration)
      = Measure.dirac e
  rw [Measure.map_dirac e, meanFieldFlow_frozen_dim_one p _ hspec he]

/-- In dimension one every schedule fixes any sphere Dirac (fold `attnStep_dirac_dim_one` along
the list). -/
theorem attnMeasureFlow_dirac_dim_one (θ : AttnSchedule 1) {e : Eucl 1}
    (he : e ∈ MeasureToMeasure.sphere 1) :
    attnMeasureFlow θ (Measure.dirac e) = Measure.dirac e := by
  induction θ with
  | nil => simp
  | cons p rest ih =>
    have hcons : attnMeasureFlow (p :: rest) (Measure.dirac e)
        = attnMeasureFlow rest (attnStep p (Measure.dirac e)) := rfl
    rw [hcons, attnStep_dirac_dim_one p he, ih]

/-- **F31.** The dimension-free `lemma_5_4` schema is false: at `d = 1` the pair
`μ = δ_{e₀}`, `ψ = const (-e₀)` satisfies every hypothesis (probability, sphere-supported,
measurable, a.e. sphere-valued), yet every schedule's flow fixes `δ_{e₀}`, so every admissible
approximant `ψε` has `ψε e₀ = e₀` and `L²` error `‖-e₀ - e₀‖ = 2 > 1 = ε`. -/
theorem oldLemma54NoDim_false : ¬ Regression.OldLemma54NoDimSig := by
  intro h
  set e : Eucl 1 := EuclideanSpace.single (0 : Fin 1) (1 : ℝ) with he
  have hnorm : ‖e‖ = 1 := by rw [he]; simp
  have hmem : e ∈ MeasureToMeasure.sphere 1 := by
    rw [MeasureToMeasure.sphere, Metric.mem_sphere, dist_zero_right]; exact hnorm
  have hmemneg : (-e) ∈ MeasureToMeasure.sphere 1 := by
    rw [MeasureToMeasure.sphere, Metric.mem_sphere, dist_zero_right, norm_neg]; exact hnorm
  have hμs : supportedIn (Measure.dirac e) (MeasureToMeasure.sphere 1) := by
    have hms : MeasurableSet (MeasureToMeasure.sphere 1) := Metric.isClosed_sphere.measurableSet
    show Measure.dirac e (MeasureToMeasure.sphere 1)ᶜ = 0
    rw [Measure.dirac_apply' _ hms.compl, Set.indicator_of_notMem (not_not_intro hmem)]
  obtain ⟨θ, ψε, hflow, hψεm, hL2⟩ :=
    h (Measure.dirac e) inferInstance (fun _ => -e) 1 1 one_pos one_pos hμs measurable_const
      (Filter.Eventually.of_forall fun _ => hmemneg)
  rw [attnMeasureFlow_dirac_dim_one θ hmem, Measure.map_dirac e] at hflow
  -- `δ_e = δ_{ψε e}` forces `ψε e = e`.
  have hfix : ψε e = e := by
    by_contra hne
    have h1 : Measure.dirac e ({e} : Set (Eucl 1)) = 1 := by
      rw [Measure.dirac_apply' _ (measurableSet_singleton e),
        Set.indicator_of_mem (Set.mem_singleton e)]
      rfl
    have h2 : Measure.dirac (ψε e) ({e} : Set (Eucl 1)) = 0 := by
      rw [Measure.dirac_apply' _ (measurableSet_singleton e),
        Set.indicator_of_notMem (by simpa using hne)]
    rw [hflow, h2] at h1
    exact one_ne_zero h1.symm
  have hint : ∫ x, ‖(-e) - ψε x‖ ^ 2 ∂(Measure.dirac e) = ‖(-e) - ψε e‖ ^ 2 :=
    integral_dirac _ e
  have hval : ‖(-e) - ψε e‖ ^ 2 = 4 := by
    rw [hfix]
    have hcalc : (-e) - e = (-2 : ℝ) • e := by module
    rw [hcalc, norm_smul, hnorm]
    norm_num
  rw [hint, hval] at hL2
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h4] at hL2
  linarith

end Regression.Refuted
