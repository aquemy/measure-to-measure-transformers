import Regression.NonVacuity.MidLevel

/-!
# Non-vacuity witnesses for the `Statements/MainResults.lean` axiom

`exists_disentangling_balls` gained probability, sphere-support, pairwise-distinctness, and the
gap-form `SharedMissingDirection` hypotheses in PR #69 (finding F14). The witness family below
(two distinct Dirac masses at orthogonal basis vectors, with the third basis vector as the shared
missing direction) confirms the hypotheses are jointly satisfiable.
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open scoped RealInnerProductSpace

/-- Diracs at distinct points are distinct measures (they disagree on a singleton). -/
theorem dirac_ne_dirac {d : ℕ} {x y : Eucl d} (hxy : x ≠ y) :
    (Measure.dirac x : Measure (Eucl d)) ≠ Measure.dirac y := by
  intro h
  have heval := congrArg (fun m : Measure (Eucl d) => m {x}) h
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Set.indicator_of_mem (Set.mem_singleton _),
    Set.indicator_of_notMem (by simpa using hxy.symm)] at heval
  simp at heval

/-- The first two basis vectors of `Eucl 3` are distinct. -/
theorem unitE3_zero_ne_one : unitE 3 0 ≠ unitE 3 1 := by
  intro h
  have h0 := congrFun (congrArg (fun x : Eucl 3 => (x : Fin 3 → ℝ)) h) 0
  simp [unitE] at h0

/-- Non-vacuity of `exists_disentangling_balls`: two distinct Diracs at `e₀, e₁ ∈ 𝕊² ⊂ ℝ³`,
with `e₂` the shared missing direction (gap `δ = 1`). -/
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
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact dirac_ne_dirac unitE3_zero_ne_one
    · exact dirac_ne_dirac unitE3_zero_ne_one.symm
    · exact absurd rfl hij
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
  have _h := exists_disentangling_balls (le_refl 3) μ₀ 1 one_pos hμ hμs hne hmiss
  trivial

end Regression.NonVacuity
