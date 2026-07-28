import Regression.Refuted.F12_HeavyTails
import MeasureToMeasure.Statements.Lemma34Part1
import MeasureToMeasure.Statements.Prop21
import MeasureToMeasure.Statements.ClusterToPoint

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
    (fun i => ⟨id, measurable_id, Measure.map_id⟩)
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

/-! #### Named part-2 witness pair

The diagonal-symmetric halves have barycenters `(17/26, 17/26)` and `(7/10, 7/10)` on the diagonal
ray, colinear with `γ = 85/91 ∈ (0,1)`. Named (rather than inline in an `example`) so that
`Regression/Refuted/HgenRestUnconditionallyFalse.lean` can reuse the same admissible pair to refute
`GenRestNearBall` (finding F22). -/

/-- Part-2 witness `μ`: equal-weight atoms at `(5/13, 12/13)` and `(12/13, 5/13)`. -/
noncomputable def partTwoMu : Measure (Eucl 2) :=
  twoAtom (1/2) (1/2) (pt (5/13) (12/13)) (pt (12/13) (5/13))

/-- Part-2 witness `ν`: equal-weight atoms at `(3/5, 4/5)` and `(4/5, 3/5)`. -/
noncomputable def partTwoNu : Measure (Eucl 2) :=
  twoAtom (1/2) (1/2) (pt (3/5) (4/5)) (pt (4/5) (3/5))

instance partTwoMu_isProbabilityMeasure : IsProbabilityMeasure partTwoMu :=
  isProbabilityMeasure_twoAtom (ENNReal.add_halves 1) _ _

instance partTwoNu_isProbabilityMeasure : IsProbabilityMeasure partTwoNu :=
  isProbabilityMeasure_twoAtom (ENNReal.add_halves 1) _ _

theorem partTwoMu_supportedIn_sphere : supportedIn partTwoMu (MeasureToMeasure.sphere 2) :=
  twoAtom_supportedIn Metric.isClosed_sphere.measurableSet
    (pt_mem_sphere (by norm_num)) (pt_mem_sphere (by norm_num))

theorem partTwoNu_supportedIn_sphere : supportedIn partTwoNu (MeasureToMeasure.sphere 2) :=
  twoAtom_supportedIn Metric.isClosed_sphere.measurableSet
    (pt_mem_sphere (by norm_num)) (pt_mem_sphere (by norm_num))

/-- The open orthant of `Eucl 2` is measurable (an intersection of open half-spaces). -/
theorem orthant_two_measurableSet : MeasurableSet (orthant 2) := by
  have : orthant 2 = ⋂ i : Fin 2, {v : Eucl 2 | 0 < v i} := by
    ext v; simp [orthant, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable

theorem partTwoMu_supportedIn_orthant : supportedIn partTwoMu (orthant 2) :=
  twoAtom_supportedIn orthant_two_measurableSet
    (pt_mem_orthant (by norm_num) (by norm_num)) (pt_mem_orthant (by norm_num) (by norm_num))

theorem partTwoNu_supportedIn_orthant : supportedIn partTwoNu (orthant 2) :=
  twoAtom_supportedIn orthant_two_measurableSet
    (pt_mem_orthant (by norm_num) (by norm_num)) (pt_mem_orthant (by norm_num) (by norm_num))

theorem partTwoMu_ne_partTwoNu : partTwoMu ≠ partTwoNu := by
  intro hEq
  have hμa : partTwoMu {pt (5/13) (12/13)} = 1 / 2 :=
    twoAtom_apply_fst (pt_ne_of_fst (by norm_num))
  have hνa : partTwoNu {pt (5/13) (12/13)} = 0 := by
    show twoAtom (1/2) (1/2) (pt (3/5) (4/5)) (pt (4/5) (3/5)) {pt (5/13) (12/13)} = 0
    simp only [twoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_notMem
        (by simpa using (pt_ne_of_fst (by norm_num) : pt (3/5) (4/5) ≠ pt (5/13) (12/13))),
      Set.indicator_of_notMem
        (by simpa using (pt_ne_of_fst (by norm_num) : pt (4/5) (3/5) ≠ pt (5/13) (12/13)))]
    simp
  rw [hEq, hνa] at hμa
  exact absurd hμa.symm (by norm_num)

theorem partTwo_colinear : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧
    MeasureToMeasure.Leaves.barycenter partTwoMu =
      γ • MeasureToMeasure.Leaves.barycenter partTwoNu := by
  have hne2 : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by finiteness
  have htoReal : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div]; norm_num
  refine ⟨85 / 91, ⟨by norm_num, by norm_num⟩, ?_⟩
  show MeasureToMeasure.Leaves.barycenter
      (twoAtom (1/2) (1/2) (pt (5/13) (12/13)) (pt (12/13) (5/13))) =
    (85 / 91 : ℝ) • MeasureToMeasure.Leaves.barycenter
      (twoAtom (1/2) (1/2) (pt (3/5) (4/5)) (pt (4/5) (3/5)))
  rw [twoAtom_barycenter hne2 hne2, twoAtom_barycenter hne2 hne2, htoReal]
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  · simp only [pt, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    norm_num
  · simp only [pt, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    norm_num

/-- Non-vacuity scope for `lemma_3_4_part2` (rescoped 2026-07-27, finding F22). The paper-level
hypothesis bundle -- distinctness, sphere and orthant supports, colinear-unequal barycenters
(`γ = 85/91`) -- IS jointly satisfiable, witnessed by `partTwoMu`/`partTwoNu` above. A FULL
application of the discharged theorem is impossible: the `hgenRest` hypothesis added at discharge
time (PR #260) is unsatisfiable for every measure pair and every `d ≥ 2`, kernel-checked as
`lemma_3_4_part2_hgenRest_unsatisfiable` in `Regression/Refuted/HgenRestUnconditionallyFalse.lean`,
so `lemma_3_4_part2` is currently VACUOUS pending re-discharge. An earlier version of this example
applied `lemma_3_4_part2` PARTIALLY (10 of its 13 explicit arguments), which silently stopped
guarding when PR #260 added hypotheses; per F22, non-vacuity witnesses must ascribe the full
conclusion type so a partial application cannot typecheck. -/
example : True := by
  have _hne := partTwoMu_ne_partTwoNu
  have _hcol := partTwo_colinear
  have _hs := partTwoMu_supportedIn_sphere
  have _ho := partTwoNu_supportedIn_orthant
  trivial

/-! ### prop_2_2 (`hxhull`, F21) -/

/-- A point on the great-circle arc `t ↦ (cos t, sin t, 0)` in `Eucl 3`. -/
noncomputable def arcPt (t : ℝ) : Eucl 3 := WithLp.toLp 2 ![Real.cos t, Real.sin t, 0]

theorem arcPt_apply_zero (t : ℝ) : arcPt t 0 = Real.cos t := rfl
theorem arcPt_apply_one (t : ℝ) : arcPt t 1 = Real.sin t := rfl
theorem arcPt_apply_two (t : ℝ) : arcPt t 2 = 0 := rfl

/-- The arc lies on the unit sphere: `cos²+ sin²+0² = 1`. -/
theorem arcPt_mem_sphere (t : ℝ) : arcPt t ∈ MeasureToMeasure.sphere 3 := by
  have hnorm : ‖arcPt t‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_three, arcPt_apply_zero, arcPt_apply_one, arcPt_apply_two,
      Real.norm_eq_abs, sq_abs]
    rw [show Real.cos t ^ 2 + Real.sin t ^ 2 + (0 : ℝ) ^ 2
        = Real.sin t ^ 2 + Real.cos t ^ 2 by ring, Real.sin_sq_add_cos_sq, Real.sqrt_one]
  exact mem_sphere_zero_iff_norm.mpr hnorm

theorem arcPt_continuous : Continuous arcPt := by
  unfold arcPt
  fun_prop

/-- The arc is injective on `[0, π/4]` (a fortiori on `[0, π]`, where `cos` already is). -/
theorem arcPt_injOn : Set.InjOn arcPt (Set.Icc (0 : ℝ) (Real.pi / 4)) := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 4) ⊆ Set.Icc (0 : ℝ) Real.pi :=
    fun x hx => ⟨hx.1, hx.2.trans (by linarith [Real.pi_pos])⟩
  intro t1 h1 t2 h2 heq
  have hcos : Real.cos t1 = Real.cos t2 := by
    have h := congrFun (congrArg (fun (v : Eucl 3) i => v i) heq) 0
    rwa [arcPt_apply_zero, arcPt_apply_zero] at h
  exact Real.injOn_cos (hsub h1) (hsub h2) hcos

/-- The uniform (Lebesgue-based) probability measure on the arc `t ∈ [0, π/4]`, pushed onto the
sphere: atomless (F21's `hxhull` witness needs a genuinely atomless `μ`, not a Dirac). -/
noncomputable def arcMeasure : Measure (Eucl 3) :=
  (ENNReal.ofReal (Real.pi / 4))⁻¹ • (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 4))).map arcPt

theorem arcMeasure_ofReal_ne : (ENNReal.ofReal (Real.pi / 4)) ≠ 0 ∧ (ENNReal.ofReal (Real.pi / 4)) ≠ ⊤ :=
  ⟨(ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])).ne', ENNReal.ofReal_ne_top⟩

theorem arcMeasure_apply (s : Set (Eucl 3)) (hs : MeasurableSet s) :
    arcMeasure s = (ENNReal.ofReal (Real.pi / 4))⁻¹ *
      volume (arcPt ⁻¹' s ∩ Set.Icc (0 : ℝ) (Real.pi / 4)) := by
  rw [arcMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply arcPt_continuous.measurable hs, Measure.restrict_apply' measurableSet_Icc]

instance arcMeasure_isProbabilityMeasure : IsProbabilityMeasure arcMeasure := by
  constructor
  rw [arcMeasure_apply Set.univ MeasurableSet.univ]
  simp only [Set.preimage_univ, Set.univ_inter]
  rw [Real.volume_Icc, sub_zero,
    ENNReal.inv_mul_cancel arcMeasure_ofReal_ne.1 arcMeasure_ofReal_ne.2]

/-- `arcMeasure` is atomless: any singleton pulls back, via injectivity on `[0, π/4]`, to at most
one point of `ℝ`, which is Lebesgue-null. -/
theorem arcMeasure_atomless (y : Eucl 3) : arcMeasure {y} = 0 := by
  rw [arcMeasure_apply {y} (measurableSet_singleton y)]
  have hsub : arcPt ⁻¹' {y} ∩ Set.Icc (0 : ℝ) (Real.pi / 4) ⊆
      {t ∈ Set.Icc (0:ℝ) (Real.pi/4) | arcPt t = y} := fun t ht => ⟨ht.2, ht.1⟩
  rcases Set.eq_empty_or_nonempty {t ∈ Set.Icc (0:ℝ) (Real.pi/4) | arcPt t = y} with he | ⟨t0, ht0⟩
  · have : arcPt ⁻¹' {y} ∩ Set.Icc (0 : ℝ) (Real.pi / 4) = ∅ :=
      Set.subset_eq_empty (he ▸ hsub) he
    rw [this]; simp
  · have hset : {t ∈ Set.Icc (0:ℝ) (Real.pi/4) | arcPt t = y} = {t0} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ht, hty⟩
        exact arcPt_injOn ht ht0.1 (hty.trans ht0.2.symm)
      · rintro rfl; exact ht0
    have hfinal : arcPt ⁻¹' {y} ∩ Set.Icc (0 : ℝ) (Real.pi / 4) = {t0} :=
      Set.Subset.antisymm (hset ▸ hsub) (by
        rw [Set.singleton_subset_iff]; exact ⟨ht0.2, ht0.1⟩)
    rw [hfinal, Real.volume_singleton, mul_zero]

/-- `arcMeasure` is supported on the sphere: `arcPt` never leaves it. -/
theorem arcMeasure_supportedIn_sphere : supportedIn arcMeasure (MeasureToMeasure.sphere 3) := by
  show arcMeasure (MeasureToMeasure.sphere 3)ᶜ = 0
  have hms : MeasurableSet (MeasureToMeasure.sphere 3)ᶜ :=
    (Metric.isClosed_sphere (x := (0 : Eucl 3)) (ε := 1)).measurableSet.compl
  rw [arcMeasure_apply _ hms]
  have hpre : arcPt ⁻¹' (MeasureToMeasure.sphere 3)ᶜ ∩ Set.Icc (0 : ℝ) (Real.pi / 4) = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hns _
    exact absurd (arcPt_mem_sphere t) hns
  rw [hpre]; simp

/-- **The `hxhull` witness (F21).** A closed set carrying `arcMeasure`'s full mass must contain
`arcPt 0`: if not, its (open, `arcPt` continuous) preimage-complement contains an open ball around
`0`, whose intersection with `[0, π/4]` is a one-sided interval of positive length -- forcing
`arcMeasure sᶜ > 0`, contradicting full support. -/
theorem arcPt_zero_mem_of_closed_convex_supportedIn {s : Set (Eucl 3)} (hsc : IsClosed s)
    (hsupp : supportedIn arcMeasure s) : arcPt 0 ∈ s := by
  by_contra hnot
  have hmeas : MeasurableSet s := hsc.measurableSet
  have hcompl : arcMeasure sᶜ = 0 := hsupp
  rw [arcMeasure_apply _ hmeas.compl] at hcompl
  have hvol0 : volume (arcPt ⁻¹' sᶜ ∩ Set.Icc (0 : ℝ) (Real.pi / 4)) = 0 := by
    rcases mul_eq_zero.mp hcompl with h | h
    · exact absurd h (ENNReal.inv_ne_zero.mpr arcMeasure_ofReal_ne.2)
    · exact h
  have h0mem : (0 : ℝ) ∈ arcPt ⁻¹' sᶜ := by
    simp only [Set.mem_preimage, Set.mem_compl_iff]; exact hnot
  have hopen : IsOpen (arcPt ⁻¹' sᶜ) := hsc.isOpen_compl.preimage arcPt_continuous
  obtain ⟨δ, hδpos, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0mem
  set δ' : ℝ := min δ (Real.pi / 8) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos (by linarith [Real.pi_pos])
  have hsubset : Set.Ico (0 : ℝ) δ' ⊆ arcPt ⁻¹' sᶜ ∩ Set.Icc (0 : ℝ) (Real.pi / 4) := by
    intro t ht
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact ht.2.trans_le (min_le_left _ _)
    refine ⟨hball htball, ht.1, ?_⟩
    exact (calc t < δ' := ht.2
      _ ≤ Real.pi / 8 := min_le_right _ _
      _ ≤ Real.pi / 4 := by linarith [Real.pi_pos]).le
  have hpos : 0 < volume (Set.Ico (0 : ℝ) δ') := by
    rw [Real.volume_Ico]; exact ENNReal.ofReal_pos.mpr (by linarith)
  have hle : volume (Set.Ico (0 : ℝ) δ') ≤ volume (arcPt ⁻¹' sᶜ ∩ Set.Icc (0 : ℝ) (Real.pi / 4)) :=
    measure_mono hsubset
  rw [hvol0] at hle
  exact absurd hle (not_le.mpr hpos)

/-- Non-vacuity of `prop_2_2`: the atomless arc measure `arcMeasure`, single target `arcPt 0`
(weight `1`), horizon `T = 1`, tolerance `ε = 1`. `hxhull` is discharged by
`arcPt_zero_mem_of_closed_convex_supportedIn` -- no geometric fact about the target beyond lying in
the support is needed, since `M = 1` puts the sole target exactly there. -/
example : True := by
  haveI := arcMeasure_isProbabilityMeasure
  have _h := prop_2_2 arcMeasure (le_refl 3) 1 1 one_pos one_pos
    arcMeasure_atomless arcMeasure_supportedIn_sphere
    1 (fun _ => arcPt 0) (fun _ => arcPt_mem_sphere 0)
    (fun _ s hsc _ hsupp => arcPt_zero_mem_of_closed_convex_supportedIn hsc hsupp)
    (fun _ => 1) (by simp) (fun _ => one_ne_zero)
    (Measure.dirac (arcPt 0)) (by simp)
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

/-! ### `lemma_3_4_part2` (non-vacuous re-statement, finding F26): FULL-application witness

The pair: `arc2Measure`, the uniform probability measure on the `𝕊¹`-arc `t ∈ [π/8, 3π/8]`
(atomless; sphere and OPEN-orthant supported, since the closed sub-arc avoids the axes), and
`arc2Nu := (1/2)•arc2Measure + (1/2)•δ_m` with `m := arc2Pt (π/4)` the arc midpoint (legal: the
re-statement adds `[NoAtoms μ]` ONLY, so `ν` may carry an atom). The supports coincide (`m` lies
in the arc's support), the measures differ (`ν{m} = 1/2 > 0 = μ{m}`), and the barycenters are
colinear-unequal: by the exact symmetric-arc integral, `barycenter μ = s • m` with
`s = sin(π/8)/(π/8) ∈ (0,1)` (`Real.sin_lt`), so `barycenter ν = ((1+s)/2) • m` and
`barycenter μ = γ • barycenter ν` with `γ = 2s/(1+s) ∈ (0,1)`. Per the F22 lesson (T1 rule), the
witness example applies the re-stated theorem FULLY, with the conclusion type ascribed. -/

theorem pt_eq_smul (x y : ℝ) : pt x y = x • unitE 2 0 + y • unitE 2 1 := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;> simp [pt, unitE, EuclideanSpace.single]

/-- A point of the open first-quadrant arc of `𝕊¹ ⊂ ℝ²`. -/
noncomputable def arc2Pt (t : ℝ) : Eucl 2 := pt (Real.cos t) (Real.sin t)

theorem arc2Pt_mem_sphere (t : ℝ) : arc2Pt t ∈ MeasureToMeasure.sphere 2 :=
  pt_mem_sphere (by rw [← Real.sin_sq_add_cos_sq t]; ring)

theorem arc2Pt_continuous : Continuous arc2Pt := by
  unfold arc2Pt pt
  fun_prop

theorem arc2Pt_injOn : Set.InjOn arc2Pt (Set.Icc (Real.pi/8) (3*Real.pi/8)) := by
  have hsub : Set.Icc (Real.pi/8) (3*Real.pi/8) ⊆ Set.Icc (0 : ℝ) Real.pi := fun x hx =>
    ⟨le_trans (by positivity) hx.1, hx.2.trans (by linarith [Real.pi_pos])⟩
  intro t1 h1 t2 h2 heq
  have hcos : Real.cos t1 = Real.cos t2 := by
    have h := congrFun (congrArg (fun (v : Eucl 2) i => v i) heq) 0
    simpa [arc2Pt, pt_apply_zero] using h
  exact Real.injOn_cos (hsub h1) (hsub h2) hcos

theorem arc2Pt_mem_orthant {t : ℝ} (ht : t ∈ Set.Icc (Real.pi/8) (3*Real.pi/8)) :
    arc2Pt t ∈ orthant 2 := by
  have hπ := Real.pi_pos
  refine pt_mem_orthant (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · linarith [ht.1]
  · linarith [ht.2]
  · linarith [ht.1]
  · linarith [ht.2]

/-- The uniform probability measure on the arc `t ∈ [π/8, 3π/8]`, pushed onto the sphere. -/
noncomputable def arc2Measure : Measure (Eucl 2) :=
  (ENNReal.ofReal (Real.pi / 4))⁻¹ •
    (volume.restrict (Set.Icc (Real.pi/8) (3*Real.pi/8))).map arc2Pt

theorem arc2_norm_ne : (ENNReal.ofReal (Real.pi / 4)) ≠ 0 ∧ (ENNReal.ofReal (Real.pi / 4)) ≠ ⊤ :=
  ⟨(ENNReal.ofReal_pos.mpr (by positivity)).ne', ENNReal.ofReal_ne_top⟩

theorem arc2Measure_apply (s : Set (Eucl 2)) (hs : MeasurableSet s) :
    arc2Measure s = (ENNReal.ofReal (Real.pi / 4))⁻¹ *
      volume (arc2Pt ⁻¹' s ∩ Set.Icc (Real.pi/8) (3*Real.pi/8)) := by
  rw [arc2Measure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply arc2Pt_continuous.measurable hs, Measure.restrict_apply' measurableSet_Icc]

instance arc2Measure_isProbabilityMeasure : IsProbabilityMeasure arc2Measure := by
  constructor
  rw [arc2Measure_apply Set.univ MeasurableSet.univ]
  simp only [Set.preimage_univ, Set.univ_inter]
  rw [Real.volume_Icc, show 3*Real.pi/8 - Real.pi/8 = Real.pi/4 by ring,
    ENNReal.inv_mul_cancel arc2_norm_ne.1 arc2_norm_ne.2]

theorem arc2Measure_atomless (y : Eucl 2) : arc2Measure {y} = 0 := by
  rw [arc2Measure_apply {y} (measurableSet_singleton y)]
  have hsub : arc2Pt ⁻¹' {y} ∩ Set.Icc (Real.pi/8) (3*Real.pi/8) ⊆
      {t ∈ Set.Icc (Real.pi/8) (3*Real.pi/8) | arc2Pt t = y} := fun t ht => ⟨ht.2, ht.1⟩
  rcases Set.eq_empty_or_nonempty {t ∈ Set.Icc (Real.pi/8) (3*Real.pi/8) | arc2Pt t = y} with
    he | ⟨t0, ht0⟩
  · have hempty : arc2Pt ⁻¹' {y} ∩ Set.Icc (Real.pi/8) (3*Real.pi/8) = ∅ :=
      Set.subset_eq_empty (he ▸ hsub) rfl
    rw [hempty]; simp
  · have hset : {t ∈ Set.Icc (Real.pi/8) (3*Real.pi/8) | arc2Pt t = y} = {t0} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ht, hty⟩
        exact arc2Pt_injOn ht ht0.1 (hty.trans ht0.2.symm)
      · rintro rfl; exact ht0
    have hfinal : arc2Pt ⁻¹' {y} ∩ Set.Icc (Real.pi/8) (3*Real.pi/8) = {t0} :=
      Set.Subset.antisymm (hset ▸ hsub) (by
        rw [Set.singleton_subset_iff]; exact ⟨ht0.2, ht0.1⟩)
    rw [hfinal, Real.volume_singleton, mul_zero]

instance arc2Measure_noAtoms : NoAtoms arc2Measure := ⟨arc2Measure_atomless⟩

theorem arc2Measure_supportedIn_sphere : supportedIn arc2Measure (MeasureToMeasure.sphere 2) := by
  show arc2Measure (MeasureToMeasure.sphere 2)ᶜ = 0
  have hms : MeasurableSet (MeasureToMeasure.sphere 2)ᶜ :=
    (Metric.isClosed_sphere (x := (0 : Eucl 2)) (ε := 1)).measurableSet.compl
  rw [arc2Measure_apply _ hms]
  have hpre : arc2Pt ⁻¹' (MeasureToMeasure.sphere 2)ᶜ ∩ Set.Icc (Real.pi/8) (3*Real.pi/8) = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hns _
    exact absurd (arc2Pt_mem_sphere t) hns
  rw [hpre]; simp

theorem arc2Measure_supportedIn_orthant : supportedIn arc2Measure (orthant 2) := by
  show arc2Measure (orthant 2)ᶜ = 0
  rw [arc2Measure_apply _ orthant_two_measurableSet.compl]
  have hpre : arc2Pt ⁻¹' (orthant 2)ᶜ ∩ Set.Icc (Real.pi/8) (3*Real.pi/8) = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hno ht
    exact absurd (arc2Pt_mem_orthant ht) hno
  rw [hpre]; simp

theorem arc2Measure_integrable : Integrable (fun x : Eucl 2 => x) arc2Measure :=
  MeasureToMeasure.Leaves.integrable_id_of_sphere_support arc2Measure_supportedIn_sphere

/-- The arc midpoint `m = (√2/2, √2/2)`. -/
noncomputable def arc2Mid : Eucl 2 := arc2Pt (Real.pi/4)

theorem arc2Mid_mem_support : arc2Mid ∈ arc2Measure.support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨V, hVU, hVopen, hmV⟩ := mem_nhds_iff.mp hU
  have hpre : IsOpen (arc2Pt ⁻¹' V) := hVopen.preimage arc2Pt_continuous
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hpre _ (hmV : (Real.pi/4:ℝ) ∈ arc2Pt ⁻¹' V)
  set δ : ℝ := min ε (Real.pi/8) with hδdef
  have hδpos : 0 < δ := lt_min hεpos (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδle : δ ≤ Real.pi/8 := min_le_right _ _
  have hsub : Set.Ioo (Real.pi/4 - δ) (Real.pi/4 + δ) ⊆
      arc2Pt ⁻¹' V ∩ Set.Icc (Real.pi/8) (3*Real.pi/8) := by
    intro t ht
    refine ⟨hball ?_, ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · linarith [ht.1]
      · linarith [ht.2]
    · linarith [ht.1, Real.pi_pos]
    · linarith [ht.2, Real.pi_pos]
  have hVpos : 0 < arc2Measure V := by
    rw [arc2Measure_apply V hVopen.measurableSet]
    apply ENNReal.mul_pos
    · exact (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top).ne'
    · refine (lt_of_lt_of_le ?_ (measure_mono hsub)).ne'
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
  exact hVpos.trans_le (measure_mono hVU)

/-! #### The exact barycenter: `barycenter arc2Measure = s • arc2Mid`, `s = sin(π/8)/(π/8)` -/

theorem arc2_sin_integral_aux :
    Real.sin (3*Real.pi/8) - Real.sin (Real.pi/8)
      = 2 * Real.cos (Real.pi/4) * Real.sin (Real.pi/8) := by
  have hb : Real.sin (3*Real.pi/8)
      = Real.sin (Real.pi/4) * Real.cos (Real.pi/8)
        + Real.cos (Real.pi/4) * Real.sin (Real.pi/8) := by
    rw [← Real.sin_add]; ring_nf
  have ha : Real.sin (Real.pi/8)
      = Real.sin (Real.pi/4) * Real.cos (Real.pi/8)
        - Real.cos (Real.pi/4) * Real.sin (Real.pi/8) := by
    rw [← Real.sin_sub]; ring_nf
  linarith

theorem arc2_cos_integral_aux :
    Real.cos (Real.pi/8) - Real.cos (3*Real.pi/8)
      = 2 * Real.sin (Real.pi/4) * Real.sin (Real.pi/8) := by
  have hb : Real.cos (3*Real.pi/8)
      = Real.cos (Real.pi/4) * Real.cos (Real.pi/8)
        - Real.sin (Real.pi/4) * Real.sin (Real.pi/8) := by
    rw [← Real.cos_add]; ring_nf
  have ha : Real.cos (Real.pi/8)
      = Real.cos (Real.pi/4) * Real.cos (Real.pi/8)
        + Real.sin (Real.pi/4) * Real.sin (Real.pi/8) := by
    rw [← Real.cos_sub]; ring_nf
  linarith

theorem arc2_int_cos :
    ∫ t in Set.Icc (Real.pi/8) (3*Real.pi/8), Real.cos t
      = Real.sqrt 2 * Real.sin (Real.pi/8) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (Real.pi/8:ℝ) ≤ 3*Real.pi/8)]
  rw [integral_cos, arc2_sin_integral_aux, Real.cos_pi_div_four]
  ring

theorem arc2_int_sin :
    ∫ t in Set.Icc (Real.pi/8) (3*Real.pi/8), Real.sin t
      = Real.sqrt 2 * Real.sin (Real.pi/8) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (Real.pi/8:ℝ) ≤ 3*Real.pi/8)]
  rw [integral_sin, arc2_cos_integral_aux, Real.sin_pi_div_four]
  ring

theorem arc2_int_vec :
    ∫ t in Set.Icc (Real.pi/8) (3*Real.pi/8), arc2Pt t
      = (Real.sqrt 2 * Real.sin (Real.pi/8)) • unitE 2 0
        + (Real.sqrt 2 * Real.sin (Real.pi/8)) • unitE 2 1 := by
  have hint1 : IntegrableOn (fun t => Real.cos t • unitE 2 0)
      (Set.Icc (Real.pi/8) (3*Real.pi/8)) volume :=
    (Continuous.smul Real.continuous_cos continuous_const).integrableOn_Icc
  have hint2 : IntegrableOn (fun t => Real.sin t • unitE 2 1)
      (Set.Icc (Real.pi/8) (3*Real.pi/8)) volume :=
    (Continuous.smul Real.continuous_sin continuous_const).integrableOn_Icc
  have heq : ∫ t in Set.Icc (Real.pi/8) (3*Real.pi/8), arc2Pt t
      = ∫ t in Set.Icc (Real.pi/8) (3*Real.pi/8),
          (Real.cos t • unitE 2 0 + Real.sin t • unitE 2 1) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => pt_eq_smul _ _)
  rw [heq, integral_add hint1 hint2, integral_smul_const, integral_smul_const,
    arc2_int_cos, arc2_int_sin]

/-- The exact symmetric-arc barycenter identity. -/
theorem arc2Measure_bary :
    MeasureToMeasure.Leaves.barycenter arc2Measure
      = (Real.sin (Real.pi/8) / (Real.pi/8)) • arc2Mid := by
  have hmap : (∫ x, x ∂((volume.restrict (Set.Icc (Real.pi/8) (3*Real.pi/8))).map arc2Pt))
      = ∫ t in Set.Icc (Real.pi/8) (3*Real.pi/8), arc2Pt t :=
    integral_map arc2Pt_continuous.measurable.aemeasurable aestronglyMeasurable_id
  show (∫ x, x ∂arc2Measure) = _
  rw [arc2Measure, integral_smul_measure, hmap, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity), arc2_int_vec]
  show _ = (Real.sin (Real.pi/8) / (Real.pi/8)) • arc2Pt (Real.pi/4)
  rw [show arc2Pt (Real.pi/4) = pt (Real.cos (Real.pi/4)) (Real.sin (Real.pi/4)) from rfl,
    pt_eq_smul, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1 <;> · congr 1; field_simp; ring

theorem arc2_s_mem : Real.sin (Real.pi/8) / (Real.pi/8) ∈ Set.Ioo (0:ℝ) 1 := by
  have h8 : (0:ℝ) < Real.pi/8 := by positivity
  constructor
  · have := Real.sin_pos_of_pos_of_lt_pi h8 (by linarith [Real.pi_pos])
    positivity
  · rw [div_lt_one h8]
    exact Real.sin_lt h8

/-! #### The companion `ν`: half arc, half Dirac at the midpoint -/

/-- `ν := (1/2)•arc2Measure + (1/2)•δ_m`: same support, colinear-unequal barycenter, one atom
(legal: only `μ` must be atomless). -/
noncomputable def arc2Nu : Measure (Eucl 2) :=
  (1/2 : ℝ≥0∞) • arc2Measure + (1/2 : ℝ≥0∞) • Measure.dirac arc2Mid

instance arc2Nu_isProbabilityMeasure : IsProbabilityMeasure arc2Nu := by
  constructor
  rw [arc2Nu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    measure_univ, measure_univ, mul_one]
  exact ENNReal.add_halves 1

theorem arc2Mid_mem_sphere : arc2Mid ∈ MeasureToMeasure.sphere 2 :=
  arc2Pt_mem_sphere (Real.pi/4)

theorem arc2Nu_supportedIn_sphere : supportedIn arc2Nu (MeasureToMeasure.sphere 2) := by
  show arc2Nu (MeasureToMeasure.sphere 2)ᶜ = 0
  have hms : MeasurableSet (MeasureToMeasure.sphere 2)ᶜ :=
    (Metric.isClosed_sphere (x := (0 : Eucl 2)) (ε := 1)).measurableSet.compl
  rw [arc2Nu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    show arc2Measure (MeasureToMeasure.sphere 2)ᶜ = 0 from arc2Measure_supportedIn_sphere,
    Measure.dirac_apply' _ hms,
    Set.indicator_of_notMem (by simpa using arc2Mid_mem_sphere)]
  simp

theorem arc2Mid_mem_orthant : arc2Mid ∈ orthant 2 :=
  arc2Pt_mem_orthant ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem arc2Nu_supportedIn_orthant : supportedIn arc2Nu (orthant 2) := by
  show arc2Nu (orthant 2)ᶜ = 0
  rw [arc2Nu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    show arc2Measure (orthant 2)ᶜ = 0 from arc2Measure_supportedIn_orthant,
    Measure.dirac_apply' _ orthant_two_measurableSet.compl,
    Set.indicator_of_notMem (by simpa using arc2Mid_mem_orthant)]
  simp

/-- The witnesses differ at the Dirac point. -/
theorem arc2Measure_ne_arc2Nu : arc2Measure ≠ arc2Nu := by
  intro hEq
  have hν : arc2Nu {arc2Mid} = 1/2 := by
    rw [arc2Nu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul, arc2Measure_atomless, Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_mem (Set.mem_singleton arc2Mid)]
    simp
  rw [← hEq, arc2Measure_atomless] at hν
  exact absurd hν.symm (by norm_num)

/-- Scalar multiples do not change the topological support. -/
theorem support_smul_eq_two {μ : Measure (Eucl 2)} {c : ℝ≥0∞} (hc0 : c ≠ 0) :
    (c • μ).support = μ.support := by
  ext x
  rw [Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
  constructor
  · intro h U hU
    have hpos := h U hU
    rw [Measure.smul_apply, smul_eq_mul] at hpos
    rw [pos_iff_ne_zero] at hpos ⊢
    intro hcontra
    exact hpos (by rw [hcontra, mul_zero])
  · intro h U hU
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hc0 (h U hU).ne'

/-- The support of a Dirac is the singleton. -/
theorem support_dirac_eq (m : Eucl 2) : (Measure.dirac m).support = {m} := by
  ext x
  rw [Measure.mem_support_iff_forall, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hU : {m}ᶜ ∈ nhds x := isOpen_compl_singleton.mem_nhds (by simpa using hne)
    have hpos := h _ hU
    rw [Measure.dirac_apply' _ (measurableSet_singleton m).compl] at hpos
    simp [Set.indicator_of_notMem, Set.mem_compl_iff] at hpos
  · intro hxm
    subst hxm
    intro U hU
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
    norm_num

theorem arc2_support_eq : arc2Measure.support = arc2Nu.support := by
  rw [arc2Nu, Measure.support_add, support_smul_eq_two (by norm_num),
    support_smul_eq_two (by norm_num), support_dirac_eq]
  exact (Set.union_eq_self_of_subset_right
    (Set.singleton_subset_iff.mpr arc2Mid_mem_support)).symm

theorem arc2Nu_bary :
    MeasureToMeasure.Leaves.barycenter arc2Nu
      = ((1 + Real.sin (Real.pi/8) / (Real.pi/8)) / 2) • arc2Mid := by
  have hdint : Integrable (fun x : Eucl 2 => x) (Measure.dirac arc2Mid) :=
    integrable_dirac enorm_lt_top
  show (∫ x, x ∂arc2Nu) = _
  rw [arc2Nu, integral_add_measure (arc2Measure_integrable.smul_measure (by norm_num))
      (hdint.smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure]
  have hd : (∫ x, x ∂(Measure.dirac arc2Mid)) = arc2Mid := by simp
  rw [hd, show (∫ x, x ∂arc2Measure)
      = MeasureToMeasure.Leaves.barycenter arc2Measure from rfl, arc2Measure_bary]
  have h12 : ((1/2 : ℝ≥0∞)).toReal = 1/2 := by
    rw [ENNReal.toReal_div]; norm_num
  rw [h12, smul_smul, ← add_smul]
  congr 1
  ring

/-- Colinearity with `γ = 2s/(1+s) ∈ (0,1)`. -/
theorem arc2_colinear : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧
    MeasureToMeasure.Leaves.barycenter arc2Measure
      = γ • MeasureToMeasure.Leaves.barycenter arc2Nu := by
  obtain ⟨hs0, hs1⟩ := arc2_s_mem
  set s : ℝ := Real.sin (Real.pi/8) / (Real.pi/8) with hsdef
  refine ⟨2*s/(1+s), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_lt_one (by linarith)]; linarith
  · rw [arc2Measure_bary, arc2Nu_bary, smul_smul]
    rw [show (Real.sin (Real.pi/8) / (Real.pi/8)) = s from rfl]
    congr 1
    field_simp

/-- **Non-vacuity of the re-stated `lemma_3_4_part2` (finding F26): FULL application with the
conclusion type ascribed** (the T1 rule from F22: partial applications are forbidden, they stop
guarding when hypotheses are added). Every hypothesis is discharged with the concrete
`arc2Measure`/`arc2Nu` pair at horizon `T = 1`. -/
example : ∃ θ : Foundations.AttnSchedule 2, Foundations.AttnSchedule.durationSum θ = 1 ∧
    Foundations.AttnSchedule.switches θ ≤ 2 ∧
    ∀ γ₂ : ℝ, MeasureToMeasure.Leaves.barycenter (Foundations.attnMeasureFlow θ arc2Measure)
      ≠ γ₂ • MeasureToMeasure.Leaves.barycenter (Foundations.attnMeasureFlow θ arc2Nu) :=
  lemma_3_4_part2 arc2Measure arc2Nu 1 one_pos arc2Measure_ne_arc2Nu
    arc2Measure_supportedIn_sphere arc2Nu_supportedIn_sphere
    arc2Measure_supportedIn_orthant arc2Nu_supportedIn_orthant
    arc2_colinear arc2_support_eq

end Regression.NonVacuity
