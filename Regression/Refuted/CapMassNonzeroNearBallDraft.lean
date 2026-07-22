import Regression.OldStatements
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# `DraftCapMassNonzeroNearBallSig` is false (`disentangle_insert_colinear_phase4_gap`, G3)

`massGapCollapse_capMass_nonzero` (`MeasureToMeasure/Leaves/GenRestNearBall.lean`) needed to
determine whether the mass-gap-cap-collapse construction's cap mass `Sμ`/`Sν`
(`Lemma34Part1MeanField.lean`) is forced nonzero by the hypotheses already in scope at the actual
Phase-3/4 call site. It is not (`hne`/`hcc` only force `Sμ ≠ Sν`, never that either is nonzero on
its own), so the natural next step -- mirroring `GenRestNearBall`'s own "universal over every
witnessing cap" shape -- would be to introduce a blanket hypothesis: for every `z`, `cosR` witnessing a
mass gap between `μ` and `ν` (restricted to the Phase-3/4 ball-confined regime), BOTH sides' cap
mass is nonzero.

**That draft is false**, refuted here BEFORE admission (the degenerate-instantiation-attack step of
the axiom protocol caught it): a `z` chosen to literally BE one atom of a two-atom measure always
isolates it with a `cosR` close enough to `1`, giving the OTHER measure's cap mass `0` at a genuine
mass gap. This is not a contrived degeneracy -- it defeats the EXACT two-atom rational-chord family
(`Regression/NonVacuity/MidLevel.lean`'s own `lemma_3_4_part2` witness, points on Pythagorean
chords `(5/13,12/13)-(12/13,5/13)` and `(3/5,4/5)-(4/5,3/5)`) this project already uses as its
canonical non-vacuity witness for the SAME colinear-barycenter (`γ ∈ (0,1)`) regime -- so this
"works for every cap" shape is incompatible with atomic measures in general, not just some
adversarial corner case.

Unlike `GenRestNearBall`/`hgenRest` (believed but not *proven* false in the near-Dirac regime, per
`mean-field-axioms-retractability`), this draft has a genuine kernel-checked refutation: it must
NOT be re-introduced verbatim. A workable non-degeneracy hypothesis for the cap mass would need to
be tied to the SPECIFIC cap the construction's internal Besicovitch existential
(`exists_cap_measure_ne_subset`) selects, not a blanket universal over all witnessing caps -- e.g.
via `Classical.choose`-pinning (logically sound, but then unverifiable/uncheckable by any concrete
non-vacuity witness, since the pinned value is an opaque classical choice) or by restructuring the
mass-gap-cap-collapse construction to take a CALLER-SUPPLIED cap. Both are substantial, unbuilt
work, out of scope for this investigative leaf; see the leaf's own report for the full trace.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements MeasureToMeasure.Leaves
open scoped RealInnerProductSpace ENNReal

/-- A point of the plane `Eucl 2` from two coordinates (local copy of
`Regression.NonVacuity.pt`, duplicated to avoid a `Refuted → NonVacuity` import, since
`NonVacuity` already imports `Refuted`). -/
noncomputable def capMassPt (x y : ℝ) : Eucl 2 := WithLp.toLp 2 ![x, y]

theorem capMassPt_apply_zero (x y : ℝ) : capMassPt x y 0 = x := rfl
theorem capMassPt_apply_one (x y : ℝ) : capMassPt x y 1 = y := rfl

theorem capMassPt_inner (x y x' y' : ℝ) :
    (⟪capMassPt x y, capMassPt x' y'⟫ : ℝ) = x * x' + y * y' := by
  unfold capMassPt
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two, RCLike.inner_apply]
  ring

theorem capMassPt_mem_sphere {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) :
    capMassPt x y ∈ MeasureToMeasure.sphere 2 := by
  have hnorm : ‖capMassPt x y‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, capMassPt_apply_zero, capMassPt_apply_one, Real.norm_eq_abs,
      sq_abs]
    rw [h, Real.sqrt_one]
  exact mem_sphere_zero_iff_norm.mpr hnorm

theorem capMassPt_mem_orthant {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    capMassPt x y ∈ orthant 2 := by
  intro i
  fin_cases i
  · exact hx
  · exact hy

theorem capMassPt_ne_of_fst {x y x' y' : ℝ} (h : x ≠ x') : capMassPt x y ≠ capMassPt x' y' :=
  fun hEq => h (by
    simpa [capMassPt_apply_zero] using congrFun (congrArg (fun (v : Eucl 2) i => v i) hEq) 0)

/-- The two-atom measure `w • δ_a + w' • δ_b` (local copy of `Regression.NonVacuity.twoAtom`). -/
noncomputable def capMassTwoAtom (w w' : ℝ≥0∞) (a b : Eucl 2) : Measure (Eucl 2) :=
  w • Measure.dirac a + w' • Measure.dirac b

theorem capMassTwoAtom_isProbabilityMeasure {w w' : ℝ≥0∞} (h : w + w' = 1) (a b : Eucl 2) :
    IsProbabilityMeasure (capMassTwoAtom w w' a b) := by
  constructor
  simp [capMassTwoAtom, h]

theorem capMassTwoAtom_supportedIn {w w' : ℝ≥0∞} {a b : Eucl 2} {S : Set (Eucl 2)}
    (hS : MeasurableSet S) (ha : a ∈ S) (hb : b ∈ S) :
    supportedIn (capMassTwoAtom w w' a b) S := by
  show capMassTwoAtom w w' a b Sᶜ = 0
  simp only [capMassTwoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ hS.compl, Measure.dirac_apply' _ hS.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ha),
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hb)]
  simp

theorem capMassTwoAtom_apply_fst {w w' : ℝ≥0∞} {a b : Eucl 2} (hab : a ≠ b) :
    capMassTwoAtom w w' a b {a} = w := by
  simp only [capMassTwoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_singleton a),
    Measure.dirac_apply' _ (measurableSet_singleton a),
    Set.indicator_of_mem (Set.mem_singleton a),
    Set.indicator_of_notMem (by simpa using hab.symm)]
  simp

theorem capMassTwoAtom_barycenter {w w' : ℝ≥0∞} (hw : w ≠ ⊤) (hw' : w' ≠ ⊤) (a b : Eucl 2) :
    barycenter (capMassTwoAtom w w' a b) = w.toReal • a + w'.toReal • b := by
  have hInt : ∀ (c : Eucl 2), Integrable (fun z : Eucl 2 => z) (Measure.dirac c) :=
    fun c => integrable_dirac (by simp [enorm_lt_top])
  rw [barycenter, capMassTwoAtom,
    integral_add_measure ((hInt a).smul_measure hw) ((hInt b).smul_measure hw'),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]

theorem orthant2_measurableSet : MeasurableSet (orthant 2) := by
  have : orthant 2 = ⋂ i : Fin 2, {v : Eucl 2 | 0 < v i} := by
    ext v; simp [orthant, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable

/-- **The refutation.** The rational-chord two-atom witness (identical to
`Regression.NonVacuity.MidLevel`'s own `lemma_3_4_part2` non-vacuity check, plus a trivially large
confining ball) satisfies EVERY hypothesis of `DraftCapMassNonzeroNearBallSig`, yet the cap
`z := a`, `cosR := 64/65` witnesses a genuine mass gap (`μ`'s cap mass `1/2`, `ν`'s cap mass `0`)
that the draft's conclusion says cannot happen. -/
theorem capMassNonzeroNearBallDraft_false (ax : Regression.DraftCapMassNonzeroNearBallSig) :
    False := by
  have hsum : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := ENNReal.add_halves 1
  have hne2 : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by finiteness
  set a := capMassPt (5 / 13) (12 / 13) with ha
  set b := capMassPt (12 / 13) (5 / 13) with hb
  set c := capMassPt (3 / 5) (4 / 5) with hc
  set e := capMassPt (4 / 5) (3 / 5) with he
  set μ := capMassTwoAtom (1 / 2) (1 / 2) a b with hμdef
  set ν := capMassTwoAtom (1 / 2) (1 / 2) c e with hνdef
  have hμprob : IsProbabilityMeasure μ := capMassTwoAtom_isProbabilityMeasure hsum a b
  have hνprob : IsProbabilityMeasure ν := capMassTwoAtom_isProbabilityMeasure hsum c e
  have hasph : a ∈ MeasureToMeasure.sphere 2 := capMassPt_mem_sphere (by norm_num)
  have hbsph : b ∈ MeasureToMeasure.sphere 2 := capMassPt_mem_sphere (by norm_num)
  have hcsph : c ∈ MeasureToMeasure.sphere 2 := capMassPt_mem_sphere (by norm_num)
  have hesph : e ∈ MeasureToMeasure.sphere 2 := capMassPt_mem_sphere (by norm_num)
  have hμs : supportedIn μ (MeasureToMeasure.sphere 2) :=
    capMassTwoAtom_supportedIn Metric.isClosed_sphere.measurableSet hasph hbsph
  have hνs : supportedIn ν (MeasureToMeasure.sphere 2) :=
    capMassTwoAtom_supportedIn Metric.isClosed_sphere.measurableSet hcsph hesph
  have hμo : supportedIn μ (orthant 2) :=
    capMassTwoAtom_supportedIn orthant2_measurableSet
      (capMassPt_mem_orthant (by norm_num) (by norm_num))
      (capMassPt_mem_orthant (by norm_num) (by norm_num))
  have hνo : supportedIn ν (orthant 2) :=
    capMassTwoAtom_supportedIn orthant2_measurableSet
      (capMassPt_mem_orthant (by norm_num) (by norm_num))
      (capMassPt_mem_orthant (by norm_num) (by norm_num))
  have hane : a ≠ b := capMassPt_ne_of_fst (by norm_num)
  have hacne : a ≠ c := capMassPt_ne_of_fst (by norm_num)
  have haene : a ≠ e := capMassPt_ne_of_fst (by norm_num)
  have hne : μ ≠ ν := by
    intro hEq
    have hμa : μ {a} = 1 / 2 := capMassTwoAtom_apply_fst hane
    have hνa : ν {a} = 0 := by
      show capMassTwoAtom (1 / 2) (1 / 2) c e {a} = 0
      simp only [capMassTwoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [Measure.dirac_apply' _ (measurableSet_singleton a),
        Measure.dirac_apply' _ (measurableSet_singleton a),
        Set.indicator_of_notMem (by simpa using hacne.symm),
        Set.indicator_of_notMem (by simpa using haene.symm)]
      simp
    rw [hEq, hνa] at hμa
    exact absurd hμa.symm (by norm_num)
  have htoReal : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by rw [ENNReal.toReal_div]; norm_num
  have hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ barycenter μ = γ • barycenter ν := by
    refine ⟨85 / 91, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [capMassTwoAtom_barycenter hne2 hne2, capMassTwoAtom_barycenter hne2 hne2, htoReal]
    refine WithLp.ofLp_injective 2 ?_
    funext i
    fin_cases i
    · simp only [ha, hb, hc, he, capMassPt, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      norm_num
    · simp only [ha, hb, hc, he, capMassPt, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      norm_num
  have hanorm : ‖a‖ = 1 := norm_eq_one_of_mem_sphere hasph
  have hbnorm : ‖b‖ = 1 := norm_eq_one_of_mem_sphere hbsph
  have hcnorm : ‖c‖ = 1 := norm_eq_one_of_mem_sphere hcsph
  have henorm : ‖e‖ = 1 := norm_eq_one_of_mem_sphere hesph
  have hballMeas : MeasurableSet (Metric.ball (0 : Eucl 2) 2) := Metric.isOpen_ball.measurableSet
  have haball : a ∈ Metric.ball (0 : Eucl 2) 2 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hanorm]; norm_num
  have hbball : b ∈ Metric.ball (0 : Eucl 2) 2 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hbnorm]; norm_num
  have hcball : c ∈ Metric.ball (0 : Eucl 2) 2 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hcnorm]; norm_num
  have heball : e ∈ Metric.ball (0 : Eucl 2) 2 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, henorm]; norm_num
  have hμball : supportedIn μ (Metric.ball (0 : Eucl 2) 2) :=
    capMassTwoAtom_supportedIn hballMeas haball hbball
  have hνball : supportedIn ν (Metric.ball (0 : Eucl 2) 2) :=
    capMassTwoAtom_supportedIn hballMeas hcball heball
  -- the isolating cap: `z := a`, `cosR := 64/65` -- `a` is in it, `b`, `c`, `e` are not.
  have hcapmeas : MeasurableSet {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} :=
    measurableSet_lt measurable_const (continuous_const.inner continuous_id).measurable
  have hbnotcap : b ∉ {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} := by
    simp only [Set.mem_setOf_eq, not_lt, ha, hb, capMassPt_inner]; norm_num
  have hcnotcap : c ∉ {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} := by
    simp only [Set.mem_setOf_eq, not_lt, ha, hc, capMassPt_inner]; norm_num
  have henotcap : e ∉ {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} := by
    simp only [Set.mem_setOf_eq, not_lt, ha, he, capMassPt_inner]; norm_num
  have hacap : a ∈ {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} := by
    simp only [Set.mem_setOf_eq, ha, capMassPt_inner]; norm_num
  have hμcap : μ {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} = 1 / 2 := by
    show capMassTwoAtom (1 / 2) (1 / 2) a b {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} = 1 / 2
    simp only [capMassTwoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ hcapmeas, Measure.dirac_apply' _ hcapmeas,
      Set.indicator_of_mem hacap, Set.indicator_of_notMem hbnotcap]
    simp
  have hνcap : ν {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} = 0 := by
    show capMassTwoAtom (1 / 2) (1 / 2) c e {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} = 0
    simp only [capMassTwoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ hcapmeas, Measure.dirac_apply' _ hcapmeas,
      Set.indicator_of_notMem hcnotcap, Set.indicator_of_notMem henotcap]
    simp
  have hgap : μ {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)}
      ≠ ν {x : Eucl 2 | (64 : ℝ) / 65 < (⟪a, x⟫ : ℝ)} := by
    rw [hμcap, hνcap]; norm_num
  obtain ⟨_, hνnz⟩ := ax (0 : Eucl 2) 2 (by norm_num) μ ν hμprob hνprob hne hμs hνs hμo hνo
    hμball hνball hcol a hanorm (64 / 65) ⟨by norm_num, by norm_num⟩ hgap
  exact hνnz hνcap

end Regression.Refuted
