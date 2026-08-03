import Regression.NonVacuity.DisentangleAssembly
import MeasureToMeasure.Statements.MainResultsExclusive

/-!
# Non-vacuity witnesses for the gated companion main results

The companions in `Statements/MainResultsExclusive.lean` guard the paper's headline conclusions
behind the `ExclusiveSupportFamily` gate, so their hypothesis bundles must be exhibited jointly
satisfiable, applied FULLY with an explicit conclusion-type ascription per the witness rule of
WORKFLOW.md (a partial application silently stops guarding, finding F22). The witness is the
standard family: two distinct Diracs at `e₀, e₁ ∈ 𝕊² ⊂ ℝ³`, `e₂` the shared missing direction
(gap `δ = 1`), each Dirac's own point its exclusive support witness.
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements MeasureToMeasure.Leaves
open MeasureToMeasure.Foundations (AttnSchedule)
open scoped RealInnerProductSpace

/-- Non-vacuity of `prop_3_1_of_exclusive_supports`: the standard Dirac family satisfies the FULL
bundle (probability, sphere support, pairwise distinctness, shared missing direction, exclusivity
gate), applied in full with an explicit conclusion-type ascription. -/
example : True := by
  set μ₀ : Fin 2 → Measure (Eucl 3) :=
    ![Measure.dirac (unitE 3 0), Measure.dirac (unitE 3 1)] with hμ₀_def
  have hμ : ∀ i, IsProbabilityMeasure (μ₀ i) := by
    intro i
    fin_cases i <;> · show IsProbabilityMeasure (Measure.dirac _); infer_instance
  have hμs : ∀ i, supportedIn (μ₀ i) (MeasureToMeasure.sphere 3) := by
    intro i
    fin_cases i
    · exact dirac_supportedIn_sphere (unitE_mem_sphere 3 0)
    · exact dirac_supportedIn_sphere (unitE_mem_sphere 3 1)
  have hne : Pairwise fun i j => μ₀ i ≠ μ₀ j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact dirac_ne_dirac unitE3_zero_ne_one
      | exact dirac_ne_dirac unitE3_zero_ne_one.symm
  have hcap : ∀ x ∈ ({unitE 3 0, unitE 3 1} : Set (Eucl 3)),
      x ∈ {y : Eucl 3 | ⟪unitE 3 2, y⟫ ≤ 1 - 1} := by
    intro x hx
    rcases hx with h | h <;> subst h <;>
      · show ⟪unitE 3 2, _⟫ ≤ 1 - 1
        simp [unitE, EuclideanSpace.inner_single_left]
  have hmiss : SharedMissingDirection μ₀ := by
    refine ⟨unitE 3 2, unitE_norm 3 2, 1, one_pos, fun i => ?_⟩
    have hclosed : IsClosed {y : Eucl 3 | ⟪unitE 3 2, y⟫ ≤ 1 - 1} :=
      isClosed_le (continuous_const.inner continuous_id) continuous_const
    fin_cases i <;>
      · show Measure.dirac _ {y : Eucl 3 | ⟪unitE 3 2, y⟫ ≤ 1 - 1}ᶜ = 0
        rw [Measure.dirac_apply' _ hclosed.measurableSet.compl,
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (hcap _ (by simp)))]
  have hgate : ExclusiveSupportFamily μ₀ := by
    intro i
    fin_cases i
    · exact ⟨unitE 3 0, mem_support_dirac _, fun j hj => by
        fin_cases j
        · exact absurd rfl hj
        · exact notMem_support_dirac unitE3_zero_ne_one⟩
    · exact ⟨unitE 3 1, mem_support_dirac _, fun j hj => by
        fin_cases j
        · exact notMem_support_dirac unitE3_zero_ne_one.symm
        · exact absurd rfl hj⟩
  have _h : ∃ θ : AttnSchedule 3, AttnSchedule.durationSum θ = 1 ∧
      DisjointSupports (fun i => Foundations.attnMeasureFlow θ (μ₀ i)) ∧
      ∀ i, ∃ e : Eucl 3, ‖e‖ = 1 ∧
        supportedIn (Foundations.attnMeasureFlow θ (μ₀ i)) {x | 0 < ⟪e, x⟫} :=
    prop_3_1_of_exclusive_supports (le_refl 3) μ₀ 1 one_pos hμ hμs hne hmiss hgate
  trivial

/-- Non-vacuity of `theorem_1_1_of_exclusive_supports`: the standard Dirac family with the two
on-sphere Dirac targets `x = (e₀, e₁)` satisfies the FULL bundle (probability, sphere support,
on-sphere targets, pairwise distinctness, shared missing direction, exclusivity gate), applied in
full with an explicit conclusion-type ascription. -/
example : True := by
  set μ₀ : Fin 2 → Measure (Eucl 3) :=
    ![Measure.dirac (unitE 3 0), Measure.dirac (unitE 3 1)] with hμ₀_def
  set x : Fin 2 → Eucl 3 := ![unitE 3 0, unitE 3 1] with hx_def
  have hμ : ∀ i, IsProbabilityMeasure (μ₀ i) := by
    intro i
    fin_cases i <;> · show IsProbabilityMeasure (Measure.dirac _); infer_instance
  have hμs : ∀ i, supportedIn (μ₀ i) (MeasureToMeasure.sphere 3) := by
    intro i
    fin_cases i
    · exact dirac_supportedIn_sphere (unitE_mem_sphere 3 0)
    · exact dirac_supportedIn_sphere (unitE_mem_sphere 3 1)
  have hx : ∀ i, x i ∈ MeasureToMeasure.sphere 3 := by
    intro i
    fin_cases i
    · exact unitE_mem_sphere 3 0
    · exact unitE_mem_sphere 3 1
  have hne : Pairwise fun i j => μ₀ i ≠ μ₀ j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact dirac_ne_dirac unitE3_zero_ne_one
      | exact dirac_ne_dirac unitE3_zero_ne_one.symm
  have hcap : ∀ y ∈ ({unitE 3 0, unitE 3 1} : Set (Eucl 3)),
      y ∈ {z : Eucl 3 | ⟪unitE 3 2, z⟫ ≤ 1 - 1} := by
    intro y hy
    rcases hy with h | h <;> subst h <;>
      · show ⟪unitE 3 2, _⟫ ≤ 1 - 1
        simp [unitE, EuclideanSpace.inner_single_left]
  have hmiss : SharedMissingDirection μ₀ := by
    refine ⟨unitE 3 2, unitE_norm 3 2, 1, one_pos, fun i => ?_⟩
    have hclosed : IsClosed {z : Eucl 3 | ⟪unitE 3 2, z⟫ ≤ 1 - 1} :=
      isClosed_le (continuous_const.inner continuous_id) continuous_const
    fin_cases i <;>
      · show Measure.dirac _ {z : Eucl 3 | ⟪unitE 3 2, z⟫ ≤ 1 - 1}ᶜ = 0
        rw [Measure.dirac_apply' _ hclosed.measurableSet.compl,
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (hcap _ (by simp)))]
  have hgate : ExclusiveSupportFamily μ₀ := by
    intro i
    fin_cases i
    · exact ⟨unitE 3 0, mem_support_dirac _, fun j hj => by
        fin_cases j
        · exact absurd rfl hj
        · exact notMem_support_dirac unitE3_zero_ne_one⟩
    · exact ⟨unitE 3 1, mem_support_dirac _, fun j hj => by
        fin_cases j
        · exact notMem_support_dirac unitE3_zero_ne_one.symm
        · exact absurd rfl hj⟩
  have _h : ∃ θ : AttnSchedule 3, AttnSchedule.durationSum θ = 1 ∧
      ∀ i, MeasureToMeasure.Axioms.W2 (Foundations.attnMeasureFlow θ (μ₀ i))
        (Measure.dirac (x i)) ≤ 1 :=
    theorem_1_1_of_exclusive_supports (le_refl 3) μ₀ x 1 1 one_pos one_pos hmiss hμ hμs hx
      hne hgate
  trivial

/-- Non-vacuity of `theorem_1_2_of_exclusive_supports`: the standard Dirac family with itself as
the target family, matched by the identity transport map, satisfies the FULL bundle (probability,
sphere support, both missing directions, pairwise distinctness, matchability, exclusivity gate),
applied in full with an explicit conclusion-type ascription. -/
example : True := by
  set μ₀ : Fin 2 → Measure (Eucl 3) :=
    ![Measure.dirac (unitE 3 0), Measure.dirac (unitE 3 1)] with hμ₀_def
  have hμ : ∀ i, IsProbabilityMeasure (μ₀ i) := by
    intro i
    fin_cases i <;> · show IsProbabilityMeasure (Measure.dirac _); infer_instance
  have hμs : ∀ i, supportedIn (μ₀ i) (MeasureToMeasure.sphere 3) := by
    intro i
    fin_cases i
    · exact dirac_supportedIn_sphere (unitE_mem_sphere 3 0)
    · exact dirac_supportedIn_sphere (unitE_mem_sphere 3 1)
  have hne : Pairwise fun i j => μ₀ i ≠ μ₀ j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact dirac_ne_dirac unitE3_zero_ne_one
      | exact dirac_ne_dirac unitE3_zero_ne_one.symm
  have hcap : ∀ y ∈ ({unitE 3 0, unitE 3 1} : Set (Eucl 3)),
      y ∈ {z : Eucl 3 | ⟪unitE 3 2, z⟫ ≤ 1 - 1} := by
    intro y hy
    rcases hy with h | h <;> subst h <;>
      · show ⟪unitE 3 2, _⟫ ≤ 1 - 1
        simp [unitE, EuclideanSpace.inner_single_left]
  have hmiss : SharedMissingDirection μ₀ := by
    refine ⟨unitE 3 2, unitE_norm 3 2, 1, one_pos, fun i => ?_⟩
    have hclosed : IsClosed {z : Eucl 3 | ⟪unitE 3 2, z⟫ ≤ 1 - 1} :=
      isClosed_le (continuous_const.inner continuous_id) continuous_const
    fin_cases i <;>
      · show Measure.dirac _ {z : Eucl 3 | ⟪unitE 3 2, z⟫ ≤ 1 - 1}ᶜ = 0
        rw [Measure.dirac_apply' _ hclosed.measurableSet.compl,
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (hcap _ (by simp)))]
  have hgate : ExclusiveSupportFamily μ₀ := by
    intro i
    fin_cases i
    · exact ⟨unitE 3 0, mem_support_dirac _, fun j hj => by
        fin_cases j
        · exact absurd rfl hj
        · exact notMem_support_dirac unitE3_zero_ne_one⟩
    · exact ⟨unitE 3 1, mem_support_dirac _, fun j hj => by
        fin_cases j
        · exact notMem_support_dirac unitE3_zero_ne_one.symm
        · exact absurd rfl hj⟩
  -- Each member is matched to itself by the identity transport map.
  have hmatch : Matchable μ₀ μ₀ := by
    intro i
    refine ⟨id, measurable_id, ?_, Measure.map_id⟩
    rw [MeasureTheory.ae_iff]
    exact hμs i
  have _h : ∃ θ : AttnSchedule 3, AttnSchedule.durationSum θ = 1 ∧
      ∀ i, MeasureToMeasure.Axioms.W2 (Foundations.attnMeasureFlow θ (μ₀ i)) (μ₀ i) ≤ 1 :=
    theorem_1_2_of_exclusive_supports (le_refl 3) μ₀ μ₀ 1 1 one_pos one_pos hmiss hmiss hμ hμs
      hne hmatch hgate
  trivial

end Regression.NonVacuity
