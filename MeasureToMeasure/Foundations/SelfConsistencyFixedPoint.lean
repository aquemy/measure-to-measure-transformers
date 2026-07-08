import MeasureToMeasure.Foundations.SelfConsistencyContraction
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The self-consistency map has a fixed point: existence of the McKean-Vlasov trajectory
(M3b existence, leaf E3n)

Leaf E3m banked the genuine contraction bound `bieleckiDist (Ξ η₁) (Ξ η₂) ≤ (2M/(λ-K)) ·
bieleckiDist η₁ η₂` for `Ξ η := selfConsistencyStepCM p hT η μ₀ hμ₀`. This leaf pins down a
concrete exponent `λ := K + 2M + 1` (so the coefficient `2M/(λ-K) = 2M/(2M+1) < 1` unconditionally,
no extra hypothesis needed), assembles `ContractingWith` on `(C(Icc 0 T, SphereProb d),
bieleckiDist)`, and extracts a fixed point via `ContractingWith.efixedPoint`:

  `exists_selfConsistent_trajectory : ∃ η, Ξ η = η`.

This `η` is the self-consistent measure trajectory the McKean-Vlasov mean-field ODE needs: a
Picard-Lindelöf point flow (already banked, `trajectoryFlow`) whose own pushforward reproduces the
trajectory that drove it. The starting point for the iteration is the constant trajectory at `μ₀`
itself (any point works, by contraction).

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The field's point-Lipschitz constant (leaf E3c/E2a-4), viewed as a real number. -/
noncomputable def campK (p : AttnParams d) : ℝ :=
  ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
    + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ)

/-- The field's measure-Lipschitz constant (leaf E3c). -/
noncomputable def campM (p : AttnParams d) : ℝ :=
  ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))

/-- The Bielecki exponent, chosen so `2M/(λ-K) = 2M/(2M+1) < 1` unconditionally. -/
noncomputable def campLam (p : AttnParams d) : ℝ := campK p + 2 * campM p + 1

theorem campM_nonneg (p : AttnParams d) : 0 ≤ campM p := by unfold campM; positivity

theorem campK_nonneg (p : AttnParams d) : 0 ≤ campK p := by unfold campK; positivity

theorem campLam_nonneg (p : AttnParams d) : 0 ≤ campLam p := by
  unfold campLam; have := campM_nonneg p; have := campK_nonneg p; linarith

theorem campK_lt_campLam (p : AttnParams d) : campK p < campLam p := by
  unfold campLam; have := campM_nonneg p; linarith

theorem campLam_sub_campK (p : AttnParams d) : campLam p - campK p = 2 * campM p + 1 := by
  unfold campLam; ring

/-- The contraction coefficient `2M/(2M+1)`, always in `[0,1)`. -/
noncomputable def contractionCoeff (p : AttnParams d) : ℝ := 2 * campM p / (2 * campM p + 1)

theorem contractionCoeff_nonneg (p : AttnParams d) : 0 ≤ contractionCoeff p := by
  unfold contractionCoeff; have h := campM_nonneg p; positivity

theorem contractionCoeff_lt_one (p : AttnParams d) : contractionCoeff p < 1 := by
  unfold contractionCoeff
  have h := campM_nonneg p
  rw [div_lt_one (by linarith)]
  linarith

theorem contractionCoeff_eq (p : AttnParams d) :
    contractionCoeff p = 2 * campM p / (campLam p - campK p) := by
  unfold contractionCoeff; rw [campLam_sub_campK]

/-- **The self-consistency map `Ξ` is a genuine contraction on `(C(Icc 0 T, SphereProb d),
bieleckiDist)`**, in the Bielecki metric with exponent `campLam p`. -/
theorem contractingWith_selfConsistencyStepCM (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0) :
    letI := bieleckiMetricSpace (d := d) (T := T) (lam := campLam p) (campLam_nonneg p) hT
    ContractingWith (contractionCoeff p).toNNReal
      (fun η : C(Set.Icc (0 : ℝ) T, SphereProb d) => selfConsistencyStepCM p hT η μ₀ hμ₀) := by
  letI M : MetricSpace C(Set.Icc (0 : ℝ) T, SphereProb d) :=
    bieleckiMetricSpace (d := d) (campLam_nonneg p) hT
  refine ⟨?_, ?_⟩
  · rw [show (1 : ℝ≥0) = (1 : ℝ).toNNReal by simp]
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (contractionCoeff_nonneg p)).mpr
      (contractionCoeff_lt_one p)
  · apply @LipschitzWith.of_dist_le_mul _ _ M.toPseudoMetricSpace M.toPseudoMetricSpace
    intro η₁ η₂
    show bieleckiDist (T := T) (lam := campLam p) (selfConsistencyStepCM p hT η₁ μ₀ hμ₀)
      (selfConsistencyStepCM p hT η₂ μ₀ hμ₀) ≤
      ((contractionCoeff p).toNNReal : ℝ) * bieleckiDist (T := T) (lam := campLam p) η₁ η₂
    rw [Real.coe_toNNReal _ (contractionCoeff_nonneg p), contractionCoeff_eq]
    have hbound := bieleckiDist_selfConsistencyStepCM_le p hT (campLam_nonneg p) η₁ η₂ μ₀ hμ₀
      (campK_lt_campLam p)
    have heq2 :
        2 * campM p / (campLam p - campK p) * bieleckiDist (T := T) (lam := campLam p) η₁ η₂
          = 2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
            bieleckiDist (T := T) (lam := campLam p) η₁ η₂ / (campLam p - campK p) := by
      unfold campM; ring
    rw [heq2]
    exact hbound

/-- **The McKean-Vlasov self-consistent trajectory exists.** `Ξ`'s Banach fixed point (starting the
iteration at the constant trajectory `μ₀`, but any starting point works by contraction). -/
theorem exists_selfConsistent_trajectory (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0) :
    ∃ η : C(Set.Icc (0 : ℝ) T, SphereProb d), selfConsistencyStepCM p hT η μ₀ hμ₀ = η := by
  letI M : MetricSpace C(Set.Icc (0 : ℝ) T, SphereProb d) :=
    bieleckiMetricSpace (d := d) (campLam_nonneg p) hT
  letI : CompleteSpace C(Set.Icc (0 : ℝ) T, SphereProb d) :=
    bieleckiPseudoMetricSpace.completeSpace (campLam_nonneg p) hT
  have hcontract := contractingWith_selfConsistencyStepCM p hT μ₀ hμ₀
  set η₀ : C(Set.Icc (0 : ℝ) T, SphereProb d) :=
    ContinuousMap.const _ (⟨μ₀, ‹IsProbabilityMeasure μ₀›, hμ₀⟩ : SphereProb d) with hη₀
  have hne : @edist _ M.toPseudoMetricSpace.toEDist η₀
      ((fun η : C(Set.Icc (0 : ℝ) T, SphereProb d) => selfConsistencyStepCM p hT η μ₀ hμ₀) η₀)
        ≠ ⊤ :=
    @edist_ne_top _ M.toPseudoMetricSpace _ _
  exact ⟨ContractingWith.efixedPoint _ hcontract η₀ hne,
    ContractingWith.efixedPoint_isFixedPt hcontract hne⟩

end MeasureToMeasure.Foundations
