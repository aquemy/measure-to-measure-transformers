import Regression.OldStatements

/-!
# F14: disentanglement without pairwise distinctness is false (identical inputs)

One schedule produces ONE flowed measure per input; a family of two IDENTICAL inputs yields the
same output twice, which cannot be a probability measure supported in each of two disjoint
balls. This is the F14 linearity-of-the-family failure mode in its sharpest form: no hypothesis
short of distinguishing the inputs can make family-level disentanglement true, which is why
`exists_disentangling_balls` carries the paper's standing assumption `μ₀^i ≢ μ₀^j` (p.5) and the
gap-form `SharedMissingDirection` since PR #69. The historical dense-atoms disproof of the
pre-F14 linear statement (scratch file `BoomDisentangle.lean`, ~200 lines) is superseded by this
sharper and far shorter witness; its narrative lives in `RESEARCH.md` (F14).
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace

/-- F14: the current-layer disentangling statement without the pairwise-distinctness hypothesis
(and with the pre-F14 point-form missing direction) is false: two identical Dirac inputs cannot
be steered into two disjoint balls by one schedule. -/
theorem oldAttnDisentangle_false (ax : Regression.OldAttnDisentangleSig) : False := by
  classical
  set ω : Eucl 3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hω_def
  have hω : ‖ω‖ = 1 := by simp [hω_def]
  have hnegsph : -ω ∈ MeasureToMeasure.sphere 3 := by
    show -ω ∈ Metric.sphere (0 : Eucl 3) 1
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact hω
  -- the family: two identical Diracs at `-ω`
  set μ₀ : Fin 2 → Measure (Eucl 3) := fun _ => Measure.dirac (-ω) with hμ₀_def
  have hμ : ∀ i, IsProbabilityMeasure (μ₀ i) := fun _ => by infer_instance
  have hμs : ∀ i, supportedIn (μ₀ i) (MeasureToMeasure.sphere 3) := by
    intro i
    show Measure.dirac (-ω) (MeasureToMeasure.sphere 3)ᶜ = 0
    have hms : MeasurableSet (MeasureToMeasure.sphere 3)ᶜ :=
      (Metric.isClosed_sphere (x := (0 : Eucl 3)) (ε := 1)).measurableSet.compl
    rw [Measure.dirac_apply' _ hms,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hnegsph)]
  -- the point-form missing direction holds: `⟪ω, -ω⟫ = -1 < 1`
  have hmiss : ∃ ω' : Eucl 3, ‖ω'‖ = 1 ∧
      ∀ i, supportedIn (μ₀ i) {x | ⟪ω', x⟫ < 1} := by
    refine ⟨ω, hω, fun i => ?_⟩
    show Measure.dirac (-ω) {x : Eucl 3 | ⟪ω, x⟫ < 1}ᶜ = 0
    have hopen : IsOpen {x : Eucl 3 | ⟪ω, x⟫ < 1} :=
      isOpen_lt (continuous_const.inner continuous_id) continuous_const
    have hmem : -ω ∈ {x : Eucl 3 | ⟪ω, x⟫ < 1} := by
      show ⟪ω, -ω⟫ < 1
      rw [inner_neg_right, real_inner_self_eq_norm_sq, hω]
      norm_num
    rw [Measure.dirac_apply' _ hopen.measurableSet.compl,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]
  obtain ⟨θ, α, r, hr0, hr1, hsep, hball⟩ := ax (le_refl 3) μ₀ 1 one_pos hμ hμs hmiss
  -- one schedule, one output: both ball constraints apply to the SAME measure
  set ν : Measure (Eucl 3) := attnMeasureFlow θ (Measure.dirac (-ω)) with hν_def
  obtain ⟨hνprob, -⟩ :=
    MeasureToMeasure.Foundations.attnMeasureFlow_prob_supportedIn_sphere θ
      (Measure.dirac (-ω)) (by infer_instance) (hμs 0)
  have hb0 : ν (Metric.ball (α 0) r)ᶜ = 0 := hball 0
  have hb1 : ν (Metric.ball (α 1) r)ᶜ = 0 := hball 1
  -- the balls are disjoint, so together the complements cover everything
  have hdisj : Metric.ball (α 0) r ∩ Metric.ball (α 1) r = ∅ := by
    by_contra hne
    obtain ⟨x, hx0, hx1⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hd01 : 2 * r ≤ dist (α 0) (α 1) := hsep 0 1 (by decide)
    have htri : dist (α 0) (α 1) ≤ dist (α 0) x + dist x (α 1) := dist_triangle _ _ _
    rw [Metric.mem_ball, dist_comm] at hx0
    rw [Metric.mem_ball] at hx1
    linarith
  have hcover : (Set.univ : Set (Eucl 3))
      ⊆ (Metric.ball (α 0) r)ᶜ ∪ (Metric.ball (α 1) r)ᶜ := by
    intro x _
    by_cases hx0 : x ∈ Metric.ball (α 0) r
    · refine Set.mem_union_right _ fun hx1 => ?_
      have hmem : x ∈ Metric.ball (α 0) r ∩ Metric.ball (α 1) r := ⟨hx0, hx1⟩
      rw [hdisj] at hmem
      exact hmem
    · exact Set.mem_union_left _ hx0
  have huniv : ν Set.univ = 0 := by
    refine le_antisymm ?_ zero_le
    calc ν Set.univ ≤ ν ((Metric.ball (α 0) r)ᶜ ∪ (Metric.ball (α 1) r)ᶜ) :=
          measure_mono hcover
      _ ≤ ν (Metric.ball (α 0) r)ᶜ + ν (Metric.ball (α 1) r)ᶜ := measure_union_le _ _
      _ = 0 := by rw [hb0, hb1, add_zero]
  haveI := hνprob
  rw [measure_univ] at huniv
  exact one_ne_zero huniv

end Regression.Refuted
