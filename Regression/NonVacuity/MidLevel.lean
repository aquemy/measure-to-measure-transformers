import Regression.Refuted.F12_HeavyTails

/-!
# Non-vacuity witnesses for the `Statements/MidLevel.lean` axioms

Each `example` below constructs concrete data satisfying EVERY hypothesis of one axiom and
applies it. An over-strengthened (vacuous) axiom -- one whose hypotheses cannot be met -- would
make this file fail to build, which is the dual failure mode to the false-axiom class the
`Refutations/` gate guards against. The witnesses are Dirac masses at standard basis vectors.

The `lemma_3_4` witnesses use the rational chord construction: two-atom measures at Pythagorean
points of the positive-quadrant unit circle. For part 1, the chords `[(3/5,4/5), (12/13,5/13)]`
and `[(4/5,3/5), (5/13,12/13)]` interleave in circular order, so they cross; solving the 2x2
rational system puts the common barycenter at `(11/16, 11/16)` with weights `35/48, 13/48` on
both chords. For part 2, the diagonal-symmetric pairs have barycenters `(17/26, 17/26)` and
`(7/10, 7/10)` on the diagonal ray, colinear with ratio `γ = 85/91 ∈ (0, 1)`. The
`exists_parked_schedule` witness is the singleton family already at its target under the empty
schedule (horizon `0`).
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open scoped RealInnerProductSpace ENNReal

/-! ### Shared Dirac witness data -/

/-- The unit basis vector `e₀` of `Eucl d` (for `0 < d` via a `Fin d` index). -/
noncomputable def unitE (d : ℕ) (i : Fin d) : Eucl d := EuclideanSpace.single i (1 : ℝ)

/-- Basis vectors are unit vectors. -/
theorem unitE_norm (d : ℕ) (i : Fin d) : ‖unitE d i‖ = 1 := by simp [unitE]

/-- Basis vectors lie on the sphere. -/
theorem unitE_mem_sphere (d : ℕ) (i : Fin d) : unitE d i ∈ MeasureToMeasure.sphere d := by
  show unitE d i ∈ Metric.sphere (0 : Eucl d) 1
  exact mem_sphere_zero_iff_norm.mpr (unitE_norm d i)

/-- A Dirac at a sphere point is sphere-supported. -/
theorem dirac_supportedIn_sphere {d : ℕ} {x : Eucl d}
    (hx : x ∈ MeasureToMeasure.sphere d) :
    supportedIn (Measure.dirac x) (MeasureToMeasure.sphere d) := by
  show Measure.dirac x (MeasureToMeasure.sphere d)ᶜ = 0
  have hms : MeasurableSet (MeasureToMeasure.sphere d)ᶜ :=
    (Metric.isClosed_sphere (x := (0 : Eucl d)) (ε := 1)).measurableSet.compl
  rw [Measure.dirac_apply' _ hms, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx)]

/-- A Dirac at a unit vector lives in the open hemisphere around that vector. -/
theorem dirac_supportedIn_hemisphere {d : ℕ} {e : Eucl d} (he : ‖e‖ = 1) :
    supportedIn (Measure.dirac e) {x : Eucl d | 0 < ⟪e, x⟫} := by
  have hee : (0 : ℝ) < ⟪e, e⟫ := by
    rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hSopen : IsOpen {x : Eucl d | 0 < ⟪e, x⟫} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  show Measure.dirac e {x : Eucl d | 0 < ⟪e, x⟫}ᶜ = 0
  rw [Measure.dirac_apply' e hSopen.measurableSet.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr
      (show e ∈ {x : Eucl d | 0 < ⟪e, x⟫} from hee))]

/-- A Dirac at a unit vector misses the cap around the antipode (`ω := -e`, gap `δ := 1`). -/
theorem dirac_missingCap {d : ℕ} {e : Eucl d} (he : ‖e‖ = 1) :
    MissingCap (Measure.dirac e) := by
  refine ⟨-e, by rwa [norm_neg], 1, one_pos, ?_⟩
  have hmem : e ∈ {x : Eucl d | ⟪-e, x⟫ ≤ 1 - 1} := by
    show ⟪-e, e⟫ ≤ 1 - 1
    rw [inner_neg_left, real_inner_self_eq_norm_sq, he]
    norm_num
  have hclosed : IsClosed {x : Eucl d | ⟪-e, x⟫ ≤ 1 - 1} :=
    isClosed_le (continuous_const.inner continuous_id) continuous_const
  show Measure.dirac e {x : Eucl d | ⟪-e, x⟫ ≤ 1 - 1}ᶜ = 0
  rw [Measure.dirac_apply' _ hclosed.measurableSet.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]

/-! ### The witnesses -/

/-- Non-vacuity of `prop_2_1`: `δ_{e₀}` on `𝕊⁰ ⊂ ℝ¹`, in its own hemisphere. -/
example : True := by
  have _h := prop_2_1 (Measure.dirac (unitE 1 0)) 1 1 one_pos one_pos (unitE 1 0)
    (unitE_norm 1 0) (dirac_supportedIn_sphere (unitE_mem_sphere 1 0))
    (dirac_supportedIn_hemisphere (unitE_norm 1 0))
  trivial

/-- Non-vacuity of `lemma_3_2` (family form): the one-member family `![δ_{e₀}]` on `Eucl 2`
(`2 ≤ d` is now required, finding F18), probability, sphere-supported, with the shared antipodal
missing cap. -/
example : True := by
  have hmiss : SharedMissingDirection (fun _ : Fin 1 => Measure.dirac (unitE 2 0)) := by
    obtain ⟨ω, hω, δ, hδ, hsupp⟩ := dirac_missingCap (unitE_norm 2 0)
    exact ⟨ω, hω, δ, hδ, fun _ => hsupp⟩
  have _h := lemma_3_2 (fun _ : Fin 1 => Measure.dirac (unitE 2 0))
    (fun _ => inferInstance) (le_refl 2) 1 one_pos
    (fun _ => dirac_supportedIn_sphere (unitE_mem_sphere 2 0)) hmiss
  trivial

/-- Non-vacuity of `lemma_3_3` (family form): the one-member family `![δ_{e₀}]` acted at `j = 0`
with itself as the colinear companion (`c = 1`); the non-colinearity hypothesis is vacuous on one
member. -/
example : True := by
  have horth : supportedIn (Measure.dirac (unitE 1 0)) (orthant 1) := by
    have hmem : unitE 1 0 ∈ orthant 1 := by
      intro i
      rw [Subsingleton.elim i (0 : Fin 1)]
      show (0 : ℝ) < unitE 1 0 0
      simp [unitE]
    show Measure.dirac (unitE 1 0) (orthant 1)ᶜ = 0
    rw [Measure.dirac_apply' _ Regression.Refuted.measurableSet_orthant1.compl,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]
  have _h := lemma_3_3 (0 : Fin 1) (fun _ => Measure.dirac (unitE 1 0))
    (Measure.dirac (unitE 1 0)) (fun _ => inferInstance) 1 1 one_pos one_pos
    (fun _ => dirac_supportedIn_sphere (unitE_mem_sphere 1 0)) (fun _ => horth)
    (dirac_supportedIn_sphere (unitE_mem_sphere 1 0)) horth
    (by intro i k hik; exact absurd (Subsingleton.elim i k) hik)
    ⟨1, (one_smul ℝ _).symm⟩
  trivial

/-- Non-vacuity of `prop_4_2`: one active point, `e₀ ↦ e₁` on `𝕊² ⊂ ℝ³`. -/
example : True := by
  have _h := prop_4_2 (le_refl 3) 1 ![unitE 3 0] ![unitE 3 1] 1 one_pos
    (fun i => by fin_cases i; exact unitE_mem_sphere 3 0)
    (fun i => by fin_cases i; exact unitE_mem_sphere 3 1)
    (fun a b _ => Subsingleton.elim a b)
    (fun a b _ => Subsingleton.elim a b)
    (fun i hi => absurd hi (by omega))
  trivial

/-- Non-vacuity of `cluster_to_point`: `δ_{e₀}` steered to the on-sphere target `e₁` (`d = 3`). -/
example : True := by
  have _h := cluster_to_point (Measure.dirac (unitE 3 0)) (le_refl 3) 1 1 one_pos one_pos
    (unitE 3 1) (unitE 3 0) (unitE_mem_sphere 3 1) (unitE_norm 3 0)
    (dirac_supportedIn_sphere (unitE_mem_sphere 3 0))
    (dirac_supportedIn_hemisphere (unitE_norm 3 0))
  trivial

/-- Non-vacuity of `lemma_5_1`: the singleton family matched by the identity map. -/
example : True := by
  have hdisj : DisjointSupports (fun _ : Fin 1 => Measure.dirac (unitE 1 0)) := by
    refine ⟨fun _ => Set.univ, fun i => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
    show Measure.dirac (unitE 1 0) (Set.univ : Set (Eucl 1))ᶜ = 0
    simp
  have _h := lemma_5_1 (fun _ : Fin 1 => Measure.dirac (unitE 1 0))
    (fun _ : Fin 1 => Measure.dirac (unitE 1 0)) hdisj hdisj
    (fun i => ⟨id, Measure.map_id⟩)
  trivial

/-- Non-vacuity of `lemma_5_4`: `δ_{e₀}` with the identity transport map. -/
example : True := by
  have hψs : ∀ᵐ x ∂(Measure.dirac (unitE 1 0)), id x ∈ MeasureToMeasure.sphere 1 := by
    simp only [ae_dirac_eq, Filter.eventually_pure, id]
    exact unitE_mem_sphere 1 0
  have _h := lemma_5_4 (Measure.dirac (unitE 1 0)) id 1 1 one_pos one_pos
    (dirac_supportedIn_sphere (unitE_mem_sphere 1 0)) measurable_id hψs
  trivial


/-! ### lemma_B_2 (now a theorem; the witness doubles as a non-vacuity check of its statement) -/

/-- The centre lies in its own proper cap: `d_g(e₀, e₀) = arccos 1 = 0 < π/4`. -/
theorem unitE_mem_geodesicBall (d : ℕ) (i : Fin d) :
    unitE d i ∈ geodesicBall (unitE d i) (Real.pi / 4) := by
  refine ⟨unitE_mem_sphere d i, ?_⟩
  have h1 : (⟪unitE d i, unitE d i⟫ : ℝ) = 1 :=
    inner_self_eq_one_of_mem_sphere (unitE_mem_sphere d i)
  rw [geodesicDist, h1, Real.arccos_one]
  positivity

/-- Witness for `lemma_B_2` (statement satisfiable): the Dirac at `e₀` over the coincident
proper-cap pair `B(e₀, π/4)`, horizon `1`, tolerance `1/2`. -/
example : ∃ θ : Params 2, switches θ ≤ 1 ∧
    (1 - ENNReal.ofReal (1/2)) * (Measure.dirac (unitE 2 0)) (geodesicBall (unitE 2 0) (Real.pi/4))
      ≤ (measureFlow θ 1 (Measure.dirac (unitE 2 0)))
          (geodesicBall (unitE 2 0) (Real.pi/4) ∩ geodesicBall (unitE 2 0) (Real.pi/4)) :=
  lemma_B_2 (Measure.dirac (unitE 2 0)) (le_refl 2) 1 (1/2) one_pos (by norm_num)
    (unitE 2 0) (unitE 2 0) (unitE_mem_sphere 2 0) (unitE_mem_sphere 2 0)
    (Real.pi/4) (Real.pi/4)
    ⟨by positivity, by linarith [Real.pi_pos]⟩ ⟨by positivity, by linarith [Real.pi_pos]⟩
    ⟨unitE 2 0, unitE_mem_geodesicBall 2 0, unitE_mem_geodesicBall 2 0⟩

/-! ### Two-atom witnesses for `lemma_3_4` (the rational chord construction) -/

/-- A point of the plane `Eucl 2` from two coordinates. -/
noncomputable def pt (x y : ℝ) : Eucl 2 := WithLp.toLp 2 ![x, y]

theorem pt_apply_zero (x y : ℝ) : pt x y 0 = x := rfl

theorem pt_apply_one (x y : ℝ) : pt x y 1 = y := rfl

/-- Unit-circle membership from the Pythagorean identity. -/
theorem pt_mem_sphere {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) :
    pt x y ∈ MeasureToMeasure.sphere 2 := by
  have hnorm : ‖pt x y‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, pt_apply_zero, pt_apply_one, Real.norm_eq_abs, sq_abs]
    rw [h, Real.sqrt_one]
  exact mem_sphere_zero_iff_norm.mpr hnorm

/-- Open-quadrant membership. -/
theorem pt_mem_orthant {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : pt x y ∈ orthant 2 := by
  intro i
  fin_cases i
  · exact hx
  · exact hy

/-- Distinct first coordinates give distinct points. -/
theorem pt_ne_of_fst {x y x' y' : ℝ} (h : x ≠ x') : pt x y ≠ pt x' y' := fun hEq =>
  h (by simpa [pt_apply_zero] using congrFun (congrArg (fun (v : Eucl 2) i => v i) hEq) 0)

/-- The two-atom measure `w • δ_a + w' • δ_b`. -/
noncomputable def twoAtom (w w' : ℝ≥0∞) (a b : Eucl 2) : Measure (Eucl 2) :=
  w • Measure.dirac a + w' • Measure.dirac b

theorem isProbabilityMeasure_twoAtom {w w' : ℝ≥0∞} (h : w + w' = 1) (a b : Eucl 2) :
    IsProbabilityMeasure (twoAtom w w' a b) := by
  constructor
  simp [twoAtom, h]

/-- A two-atom measure is supported in any measurable set containing both atoms. -/
theorem twoAtom_supportedIn {w w' : ℝ≥0∞} {a b : Eucl 2} {S : Set (Eucl 2)}
    (hS : MeasurableSet S) (ha : a ∈ S) (hb : b ∈ S) : supportedIn (twoAtom w w' a b) S := by
  show twoAtom w w' a b Sᶜ = 0
  simp only [twoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ hS.compl, Measure.dirac_apply' _ hS.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ha),
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hb)]
  simp

/-- The atom mass of a two-atom measure at its first atom (when the atoms differ). -/
theorem twoAtom_apply_fst {w w' : ℝ≥0∞} {a b : Eucl 2} (hab : a ≠ b) :
    twoAtom w w' a b {a} = w := by
  simp only [twoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_singleton a),
    Measure.dirac_apply' _ (measurableSet_singleton a),
    Set.indicator_of_mem (Set.mem_singleton a),
    Set.indicator_of_notMem (by simpa using hab.symm)]
  simp

/-- The barycenter of a two-atom measure is the weighted atom average. -/
theorem twoAtom_barycenter {w w' : ℝ≥0∞} (hw : w ≠ ⊤) (hw' : w' ≠ ⊤) (a b : Eucl 2) :
    MeasureToMeasure.Leaves.barycenter (twoAtom w w' a b) =
      w.toReal • a + w'.toReal • b := by
  have hInt : ∀ (c : Eucl 2), Integrable (fun z : Eucl 2 => z) (Measure.dirac c) :=
    fun c => integrable_dirac (by simp [enorm_lt_top])
  rw [MeasureToMeasure.Leaves.barycenter, twoAtom,
    integral_add_measure ((hInt a).smul_measure hw) ((hInt b).smul_measure hw'),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]

/-- Non-vacuity of `lemma_3_4_part1`: the crossing rational chords
`(3/5,4/5)–(12/13,5/13)` and `(4/5,3/5)–(5/13,12/13)`, both weighted `35/48, 13/48`, are two
DISTINCT sphere-and-orthant-supported probability measures with the SAME barycenter
`(11/16, 11/16)`. -/
example : True := by
  have hsum : (35 / 48 : ℝ≥0∞) + 13 / 48 = 1 := by
    rw [ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by norm_num)
  have hne48 : (35 / 48 : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hne48' : (13 / 48 : ℝ≥0∞) ≠ ⊤ := by finiteness
  set a := pt (3/5) (4/5) with ha
  set b := pt (12/13) (5/13) with hb
  set c := pt (4/5) (3/5) with hc
  set e := pt (5/13) (12/13) with he
  set μ := twoAtom (35/48) (13/48) a b with hμdef
  set ν := twoAtom (35/48) (13/48) c e with hνdef
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_twoAtom hsum a b
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_twoAtom hsum c e
  have hμs : supportedIn μ (MeasureToMeasure.sphere 2) :=
    twoAtom_supportedIn Metric.isClosed_sphere.measurableSet
      (pt_mem_sphere (by norm_num)) (pt_mem_sphere (by norm_num))
  have hνs : supportedIn ν (MeasureToMeasure.sphere 2) :=
    twoAtom_supportedIn Metric.isClosed_sphere.measurableSet
      (pt_mem_sphere (by norm_num)) (pt_mem_sphere (by norm_num))
  have horthMeas : MeasurableSet (orthant 2) := by
    have : orthant 2 = ⋂ i : Fin 2, {v : Eucl 2 | 0 < v i} := by
      ext v; simp [orthant, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hμo : supportedIn μ (orthant 2) :=
    twoAtom_supportedIn horthMeas (pt_mem_orthant (by norm_num) (by norm_num))
      (pt_mem_orthant (by norm_num) (by norm_num))
  have hνo : supportedIn ν (orthant 2) :=
    twoAtom_supportedIn horthMeas (pt_mem_orthant (by norm_num) (by norm_num))
      (pt_mem_orthant (by norm_num) (by norm_num))
  -- distinctness: μ charges `a`, ν does not.
  have hne : μ ≠ ν := by
    intro hEq
    have hμa : μ {a} = 35 / 48 := twoAtom_apply_fst (pt_ne_of_fst (by norm_num))
    have hνa : ν {a} = 0 := by
      show twoAtom (35/48) (13/48) c e {a} = 0
      simp only [twoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [Measure.dirac_apply' _ (measurableSet_singleton a),
        Measure.dirac_apply' _ (measurableSet_singleton a),
        Set.indicator_of_notMem (by simpa using (pt_ne_of_fst (by norm_num) : c ≠ a)),
        Set.indicator_of_notMem (by simpa using (pt_ne_of_fst (by norm_num) : e ≠ a))]
      simp
    rw [hEq, hνa] at hμa
    exact absurd hμa.symm (by norm_num)
  -- equal barycenters: both chords cross at `(11/16, 11/16)`.
  have htoReal : (35 / 48 : ℝ≥0∞).toReal = 35 / 48 ∧ (13 / 48 : ℝ≥0∞).toReal = 13 / 48 := by
    constructor <;> · rw [ENNReal.toReal_div]; norm_num
  have hbar : MeasureToMeasure.Leaves.barycenter μ = MeasureToMeasure.Leaves.barycenter ν := by
    rw [twoAtom_barycenter hne48 hne48', twoAtom_barycenter hne48 hne48',
      htoReal.1, htoReal.2]
    refine WithLp.ofLp_injective 2 ?_
    funext i
    fin_cases i
    · simp only [ha, hb, hc, he, pt, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      norm_num
    · simp only [ha, hb, hc, he, pt, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      norm_num
  have hUuniv : supportedIn μ Set.univ := by
    show μ Set.univᶜ = 0
    simp
  have hUuniv' : supportedIn ν Set.univ := by
    show ν Set.univᶜ = 0
    simp
  have _h := lemma_3_4_part1 μ ν 1 one_pos hne hμs hνs hμo hνo hbar
    Set.univ isOpen_univ hUuniv hUuniv'
  trivial

/-- Non-vacuity of `lemma_3_4_part2`: the diagonal-symmetric halves have barycenters
`(17/26, 17/26)` and `(7/10, 7/10)` on the diagonal ray, colinear with `γ = 85/91 ∈ (0,1)`. -/
example : True := by
  have hsum : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := ENNReal.add_halves 1
  have hne2 : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by finiteness
  set a := pt (5/13) (12/13) with ha
  set b := pt (12/13) (5/13) with hb
  set c := pt (3/5) (4/5) with hc
  set e := pt (4/5) (3/5) with he
  set μ := twoAtom (1/2) (1/2) a b with hμdef
  set ν := twoAtom (1/2) (1/2) c e with hνdef
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_twoAtom hsum a b
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_twoAtom hsum c e
  have hμs : supportedIn μ (MeasureToMeasure.sphere 2) :=
    twoAtom_supportedIn Metric.isClosed_sphere.measurableSet
      (pt_mem_sphere (by norm_num)) (pt_mem_sphere (by norm_num))
  have hνs : supportedIn ν (MeasureToMeasure.sphere 2) :=
    twoAtom_supportedIn Metric.isClosed_sphere.measurableSet
      (pt_mem_sphere (by norm_num)) (pt_mem_sphere (by norm_num))
  have horthMeas : MeasurableSet (orthant 2) := by
    have : orthant 2 = ⋂ i : Fin 2, {v : Eucl 2 | 0 < v i} := by
      ext v; simp [orthant, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hμo : supportedIn μ (orthant 2) :=
    twoAtom_supportedIn horthMeas (pt_mem_orthant (by norm_num) (by norm_num))
      (pt_mem_orthant (by norm_num) (by norm_num))
  have hνo : supportedIn ν (orthant 2) :=
    twoAtom_supportedIn horthMeas (pt_mem_orthant (by norm_num) (by norm_num))
      (pt_mem_orthant (by norm_num) (by norm_num))
  have hne : μ ≠ ν := by
    intro hEq
    have hμa : μ {a} = 1 / 2 := twoAtom_apply_fst (pt_ne_of_fst (by norm_num))
    have hνa : ν {a} = 0 := by
      show twoAtom (1/2) (1/2) c e {a} = 0
      simp only [twoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [Measure.dirac_apply' _ (measurableSet_singleton a),
        Measure.dirac_apply' _ (measurableSet_singleton a),
        Set.indicator_of_notMem (by simpa using (pt_ne_of_fst (by norm_num) : c ≠ a)),
        Set.indicator_of_notMem (by simpa using (pt_ne_of_fst (by norm_num) : e ≠ a))]
      simp
    rw [hEq, hνa] at hμa
    exact absurd hμa.symm (by norm_num)
  have htoReal : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div]; norm_num
  have hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧
      MeasureToMeasure.Leaves.barycenter μ =
        γ • MeasureToMeasure.Leaves.barycenter ν := by
    refine ⟨85 / 91, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [twoAtom_barycenter hne2 hne2, twoAtom_barycenter hne2 hne2, htoReal]
    refine WithLp.ofLp_injective 2 ?_
    funext i
    fin_cases i
    · simp only [ha, hb, hc, he, pt, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      norm_num
    · simp only [ha, hb, hc, he, pt, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      norm_num
  have _h := lemma_3_4_part2 μ ν 1 one_pos hne hμs hνs hμo hνo hcol
  trivial

/-! ### exists_parked_schedule -/

/-- Non-vacuity of `exists_parked_schedule`: the singleton family `δ_{e₀}` on `𝕊² ⊂ ℝ³`, already
at its own target under the empty schedule (horizon `0`, zero switches). -/
example : True := by
  have hdisj : DisjointSupports (fun _ : Fin 1 => Measure.dirac (unitE 3 0)) := by
    refine ⟨fun _ => {unitE 3 0}, fun i => ?_,
      fun i j hij => absurd (Subsingleton.elim i j) hij⟩
    show Measure.dirac (unitE 3 0) ({unitE 3 0} : Set (Eucl 3))ᶜ = 0
    rw [Measure.dirac_apply' _ (measurableSet_singleton _).compl,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (Set.mem_singleton (unitE 3 0)))]
  have hper : ∀ i : Fin 1, ∃ θ : Foundations.AttnSchedule 3,
      Foundations.AttnSchedule.durationSum θ = 0 ∧
      Foundations.AttnSchedule.switches θ ≤ (fun _ : Fin 1 => 0) i ∧
      Axioms.W2 (Foundations.attnMeasureFlow θ (Measure.dirac (unitE 3 0)))
        (Measure.dirac (unitE 3 0)) ≤ 1 := by
    intro i
    refine ⟨[], rfl, le_refl 0, ?_⟩
    rw [Foundations.attnMeasureFlow_nil]
    show (MeasureToMeasure.W2 (Measure.dirac (unitE 3 0)) (Measure.dirac (unitE 3 0))).toReal ≤ 1
    rw [MeasureToMeasure.W2_self_eq_zero]
    norm_num
  have _h := exists_parked_schedule (le_refl 3)
    (fun _ : Fin 1 => Measure.dirac (unitE 3 0)) (fun _ => Measure.dirac (unitE 3 0))
    0 1 (fun _ => 0) hdisj hper
  trivial

end Regression.NonVacuity
