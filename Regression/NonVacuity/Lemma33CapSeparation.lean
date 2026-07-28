import Regression.NonVacuity.DisentangleAvoidingInsert
import MeasureToMeasure.Leaves.Lemma33CapSeparation

/-!
# Non-vacuity witness for `lemma_3_3_of_cap_separation`

The FULL application demanded by the witness rule: every hypothesis of the cap-separation gated
companion of `lemma_3_3` (`MeasureToMeasure/Leaves/Lemma33CapSeparation.lean`) is instantiated
concretely and the theorem is applied to completion with its conclusion type ascribed. The
companion's gate hypotheses guard a public conclusion (the axiom's own conclusion shape), so a
partial application would not do: it would silently stop guarding if a later PR added an
unsatisfiable hypothesis (the exact hole that hid finding F22, `GenRestNearBall`).

**The data.** `d = 2`, `N = 2`, acted index `j = 0`. Reuses the two-Dirac `resFam` toolkit of
`Regression.NonVacuity.DisentangleResolvingAsym`: index `0` (the acted member) at
`resQ = (4/5, 3/5)`, index `1` (the bystander) at `resP = (3/5, 4/5)`, both on
`sphere 2 ∩ orthant 2` with exact rationals. The colinear companion is `ν₀ := dirac resQ` itself
(`c = 1`). The collapse direction is `ω̂ = ‖resQ‖⁻¹ • resQ = resQ` (unit norm), and the gate is
instantiated at `cosR = 24/25`, `m = 49/50`:

* acted/companion sub-cap: `⟪resQ, resQ⟫ = 1 ≥ 49/50`, so both Diracs sit in `{m ≤ ⟪ω̂, ·⟫}`;
* bystander nullity: `⟪resQ, resP⟫ = 24/25`, NOT strictly above `cosR = 24/25`, so the Dirac at
  `resP` puts zero mass on the open cap `{24/25 < ⟪ω̂, ·⟫}`.

The probe constraint `cosR ≥ 0` (recorded in the companion's module docstring) is respected
non-degenerately: for `N ≥ 2` any gate with `cosR < 0` is vacuous, because orthant-supported
bystanders always carry mass in the closed positive hemisphere of the orthant direction `ω̂`;
here `cosR = 24/25` is the exact bystander level, the tightest satisfiable choice for this pair.
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Leaves MeasureToMeasure.Foundations
open MeasureToMeasure.Statements
open scoped RealInnerProductSpace

/-- The normalized barycenter direction of the acted member is `resQ` itself (unit norm). -/
theorem capOmega_eq :
    ‖MeasureToMeasure.Leaves.barycenter (resFam 0)‖⁻¹ •
      MeasureToMeasure.Leaves.barycenter (resFam 0) = resQ := by
  rw [show resFam 0 = Measure.dirac resQ from rfl, barycenter_dirac, resQ_norm]
  norm_num

/-- The bystander level: `⟪resQ, resP⟫ = 24/25`, the gate's `cosR`. -/
theorem inner_resQ_resP : (⟪resQ, resP⟫ : ℝ) = 24 / 25 := by
  rw [resQ, resP]
  simp [pt, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]
  norm_num

/-- A Dirac at a point of a measurable set is supported in it. -/
theorem dirac_supportedIn_of_mem {d : ℕ} {x : Eucl d} {S : Set (Eucl d)}
    (hS : MeasurableSet S) (hx : x ∈ S) : supportedIn (Measure.dirac x) S := by
  show Measure.dirac x Sᶜ = 0
  rw [Measure.dirac_apply' _ hS.compl, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx)]

/-- The closed sub-cap `{m ≤ ⟪ω, ·⟫}` is measurable (it is closed). -/
theorem closedCap_measurable {d : ℕ} (ω : Eucl d) (m : ℝ) :
    MeasurableSet {x : Eucl d | m ≤ (⟪ω, x⟫ : ℝ)} :=
  (isClosed_le continuous_const (continuous_const.inner continuous_id)).measurableSet

/-- The open cap `{c < ⟪ω, ·⟫}` is measurable (it is open). -/
theorem openCap_measurable {d : ℕ} (ω : Eucl d) (c : ℝ) :
    MeasurableSet {x : Eucl d | c < (⟪ω, x⟫ : ℝ)} :=
  (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet

/-- The bystander Dirac at `resP` is null on the open cap `{24/25 < ⟪resQ, ·⟫}`: its level is
EXACTLY `24/25`, not strictly above. -/
theorem dirac_resP_null_cap :
    Measure.dirac resP {x : Eucl 2 | (24 / 25 : ℝ) < (⟪resQ, x⟫ : ℝ)} = 0 := by
  rw [Measure.dirac_apply' _ (openCap_measurable resQ (24 / 25))]
  refine Set.indicator_of_notMem ?_ _
  simp only [Set.mem_setOf_eq, not_lt, inner_resQ_resP, le_refl]

/-- The acted point sits in its own closed sub-cap: `⟪resQ, resQ⟫ = 1 ≥ 49/50`. -/
theorem resQ_mem_closedCap : resQ ∈ {x : Eucl 2 | (49 / 50 : ℝ) ≤ (⟪resQ, x⟫ : ℝ)} := by
  simp only [Set.mem_setOf_eq, real_inner_self_eq_norm_sq, resQ_norm]
  norm_num

/-- Pairwise FULL non-colinearity of the initial family (no flow prefix, unlike the sibling
`resFam_noncolinear`): `resQ = c • resP` forces `c = 4/3` and `c = 3/4` at once. -/
theorem resFam_noncolinear_init : Pairwise fun i k : Fin 2 => ∀ c : ℝ,
    MeasureToMeasure.Leaves.barycenter (resFam i)
      ≠ c • MeasureToMeasure.Leaves.barycenter (resFam k) := by
  have h01 : ∀ c : ℝ, MeasureToMeasure.Leaves.barycenter (resFam 0)
      ≠ c • MeasureToMeasure.Leaves.barycenter (resFam 1) := by
    intro c
    rw [show resFam 0 = Measure.dirac resQ from rfl, show resFam 1 = Measure.dirac resP from rfl,
      barycenter_dirac, barycenter_dirac]
    exact resQ_ne_smul_resP c
  have h10 : ∀ c : ℝ, MeasureToMeasure.Leaves.barycenter (resFam 1)
      ≠ c • MeasureToMeasure.Leaves.barycenter (resFam 0) := by
    intro c
    rw [show resFam 0 = Measure.dirac resQ from rfl, show resFam 1 = Measure.dirac resP from rfl,
      barycenter_dirac, barycenter_dirac]
    exact resP_ne_smul_resQ c
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact h01
  · exact h10
  · exact absurd rfl hab

/-- **Non-vacuity of `lemma_3_3_of_cap_separation`**: the FULL application, with the conclusion
type ascribed. Every hypothesis (probability, sphere and orthant support, pairwise full
non-colinearity, colinear companion, and the whole cap-separation gate) is discharged concretely,
so the gated companion is genuinely invocable. -/
theorem lemma33CapSeparation_nonvacuity : True := by
  have hjcap : supportedIn (resFam 0)
      {x : Eucl 2 | (49 / 50 : ℝ) ≤ (⟪‖MeasureToMeasure.Leaves.barycenter (resFam 0)‖⁻¹ •
        MeasureToMeasure.Leaves.barycenter (resFam 0), x⟫ : ℝ)} := by
    rw [capOmega_eq]
    exact dirac_supportedIn_of_mem (closedCap_measurable resQ (49 / 50)) resQ_mem_closedCap
  have hνcap : supportedIn (Measure.dirac resQ)
      {x : Eucl 2 | (49 / 50 : ℝ) ≤ (⟪‖MeasureToMeasure.Leaves.barycenter (resFam 0)‖⁻¹ •
        MeasureToMeasure.Leaves.barycenter (resFam 0), x⟫ : ℝ)} := by
    rw [capOmega_eq]
    exact dirac_supportedIn_of_mem (closedCap_measurable resQ (49 / 50)) resQ_mem_closedCap
  have hbyst : ∀ i : Fin 2, i ≠ 0 →
      resFam i {x : Eucl 2 | (24 / 25 : ℝ) < (⟪‖MeasureToMeasure.Leaves.barycenter (resFam 0)‖⁻¹ •
        MeasureToMeasure.Leaves.barycenter (resFam 0), x⟫ : ℝ)} = 0 := by
    intro i hi
    rw [capOmega_eq]
    fin_cases i
    · exact absurd rfl hi
    · exact dirac_resP_null_cap
  have hcol : ∃ c : ℝ, MeasureToMeasure.Leaves.barycenter (Measure.dirac resQ)
      = c • MeasureToMeasure.Leaves.barycenter (resFam 0) :=
    ⟨1, by rw [show resFam 0 = Measure.dirac resQ from rfl, one_smul]⟩
  -- the FULL application, with the conclusion type ascribed
  have _h : ∃ θ : AttnSchedule 2, AttnSchedule.durationSum θ = 1 ∧
      supportedIn (attnMeasureFlow θ (Measure.dirac resQ))
        (Metric.ball (‖MeasureToMeasure.Leaves.barycenter (resFam 0)‖⁻¹ •
          MeasureToMeasure.Leaves.barycenter (resFam 0)) 1) ∧
      supportedIn (attnMeasureFlow θ (resFam 0))
        (Metric.ball (‖MeasureToMeasure.Leaves.barycenter (resFam 0)‖⁻¹ •
          MeasureToMeasure.Leaves.barycenter (resFam 0)) 1) ∧
      ∀ i, i ≠ (0 : Fin 2) → attnMeasureFlow θ (resFam i) = resFam i :=
    lemma_3_3_of_cap_separation (0 : Fin 2) resFam (Measure.dirac resQ) resFam_prob
      1 1 one_pos one_pos resFam_sphere resFam_orthant
      (dirac_supportedIn_sphere resQ_mem_sphere) (dirac_supportedIn_orthant2 resQ_mem_orthant)
      resFam_noncolinear_init hcol
      (cosR := 24 / 25) (m := 49 / 50) (by norm_num) (by norm_num) (by norm_num)
      hjcap hνcap hbyst
  trivial

end Regression.NonVacuity
