import Regression.Refuted.F12_HeavyTails

/-!
# Non-vacuity witnesses for the `Statements/MidLevel.lean` axioms

Each `example` below constructs concrete data satisfying EVERY hypothesis of one axiom and
applies it. An over-strengthened (vacuous) axiom -- one whose hypotheses cannot be met -- would
make this file fail to build, which is the dual failure mode to the false-axiom class the
`Refutations/` gate guards against. The witnesses are Dirac masses at standard basis vectors.

Remaining `WITNESS-TODO` markers (harder constructions, tracked for follow-up):
- WITNESS-TODO(lemma_3_4_part1): two distinct sphere-and-orthant-supported probability measures
  with EQUAL barycenters (rational-point chord-intersection construction).
- WITNESS-TODO(lemma_3_4_part2): same with `γ`-colinear unequal barycenters.
- WITNESS-TODO(exists_parked_schedule): a disjoint family with per-member schedules (needs a
  per-member `hper` witness, i.e. a cluster_to_point application per piece).
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open scoped RealInnerProductSpace

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

/-- Non-vacuity of `lemma_3_2`: `δ_{e₀}`, probability, sphere-supported, missing the antipodal
cap. -/
example : True := by
  have _h := lemma_3_2 (Measure.dirac (unitE 1 0)) 1 one_pos
    (dirac_supportedIn_sphere (unitE_mem_sphere 1 0)) (dirac_missingCap (unitE_norm 1 0))
  trivial

/-- Non-vacuity of `lemma_3_3`: `δ_{e₀}` is sphere- and orthant-supported in `ℝ¹`. -/
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
  have _h := lemma_3_3 (Measure.dirac (unitE 1 0)) 1 1 one_pos one_pos
    (dirac_supportedIn_sphere (unitE_mem_sphere 1 0)) horth
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

end Regression.NonVacuity
