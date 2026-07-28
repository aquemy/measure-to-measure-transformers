import Regression.NonVacuity.MainResults
import MeasureToMeasure.Leaves.DisentangleInductionAssembly

/-!
# Non-vacuity witness for `disentangled_prefix_of_exclusive_supports`

The strong induction over `N` (`Leaves/DisentangleInductionAssembly.lean`) guards the
`exists_disentangling_balls` re-base: its hypothesis bundle (probability members, sphere support,
`SharedMissingDirection`, `ExclusiveSupportFamily`) must be jointly satisfiable or the whole
placement chain is kernel-clean but inapplicable (the `kernel-clean-not-applicable` pattern,
finding F22's lesson). The witness reuses `MainResults.lean`'s family (two Diracs at the first
two basis vectors of `ℝ³`, third basis vector as the shared missing direction) and adds the
exclusivity data: a Dirac's support is its singleton, so each member's own point is its exclusive
witness. Applied FULLY, with an explicit conclusion-type ascription, per the witness rule of
WORKFLOW.md.
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements MeasureToMeasure.Leaves
open MeasureToMeasure.Foundations (AttnSchedule)
open scoped RealInnerProductSpace

/-- The base point belongs to its own Dirac's support (every neighborhood carries mass `1`). -/
theorem mem_support_dirac {d : ℕ} (x : Eucl d) :
    x ∈ (Measure.dirac x : Measure (Eucl d)).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  have h1 : (Measure.dirac x : Measure (Eucl d)) V = 1 := by
    rw [Measure.dirac_apply' _ hVopen.measurableSet, Set.indicator_of_mem hxV]
    rfl
  exact lt_of_lt_of_le (by norm_num) (h1 ▸ measure_mono hVU)

/-- Any other point misses a Dirac's support (a small enough ball around it is null). -/
theorem notMem_support_dirac {d : ℕ} {x y : Eucl d} (hxy : y ≠ x) :
    y ∉ (Measure.dirac x : Measure (Eucl d)).support := by
  refine Measure.notMem_support_iff_exists.mpr
    ⟨Metric.ball y (dist y x), Metric.ball_mem_nhds _ (dist_pos.mpr hxy), ?_⟩
  rw [Measure.dirac_apply' _ Metric.isOpen_ball.measurableSet,
    Set.indicator_of_notMem
      (fun h => lt_irrefl _ (by rwa [Metric.mem_ball, dist_comm] at h))]

/-- Non-vacuity of `disentangled_prefix_of_exclusive_supports`: the `MainResults.lean` family
(distinct Diracs at `e₀, e₁ ∈ 𝕊² ⊂ ℝ³`, `e₂` the shared missing direction) also satisfies the
`ExclusiveSupportFamily` gate, and the strong induction applies to it in full. -/
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
  have _h : ∃ (θ : AttnSchedule 3) (α : Fin 2 → Eucl 3) (r : Fin 2 → ℝ),
      (∀ i, 0 < r i) ∧ AttnSchedule.durationSum θ = 1 ∧
      DisentangledPrefix 3 2 2 μ₀ θ α r ∧
      Pairwise fun i j : Fin 2 => ∀ c : ℝ,
        barycenter (Foundations.attnMeasureFlow θ (μ₀ i)) ≠
          c • barycenter (Foundations.attnMeasureFlow θ (μ₀ j)) :=
    disentangled_prefix_of_exclusive_supports (le_refl 3) μ₀ hμ hμs hmiss hgate 1 one_pos
  trivial

end Regression.NonVacuity
