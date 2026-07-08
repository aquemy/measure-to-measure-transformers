import MeasureToMeasure.Foundations.SelfConsistencyBielecki
import MeasureToMeasure.Foundations.BieleckiMetricSpace

/-!
# The self-consistency map is a genuine Bielecki contraction (M3b existence, leaf E3m)

Leaf E3l banked the pointwise Duhamel bound

  `dist (trajFlow η₁ x t) (trajFlow η₂ x t) ≤ (2M·bieleckiDist η₁ η₂/(λ-K))·(e^{λt}-e^{Kt})`.

This leaf transfers it, in two steps, up to the level the outer contraction needs:

1. `dist_pushforwardAt_le_bielecki` -- the same `W₁`-coupling transfer leaves E3i/E3k use, applied
   to the pointwise bound above instead of the constant-forcing Grönwall bound.
2. `bieleckiWeight_mul_dist_pushforwardAt_le` -- multiply by `bieleckiWeight t = e^{-λt}` and bound
   `e^{-λt}(e^{λt}-e^{Kt}) = 1 - e^{(K-λ)t} ≤ 1` (since `K < λ`, `t ≥ 0`), collapsing the bound to a
   single `t`-independent constant `Cf = 2M·bieleckiDist η₁ η₂/(λ-K)`.
3. `bieleckiDist_selfConsistencyStepCM_le` -- take `⨆ t` (nonempty since `hT : 0 ≤ T` makes
   `Icc 0 T` nonempty) to get the genuine contraction inequality at the `bieleckiDist` level:

  `bieleckiDist (Ξη₁) (Ξη₂) ≤ (2M/(λ-K)) · bieleckiDist η₁ η₂`,

where `Ξ η := selfConsistencyStepCM p hT η μ₀ hμ₀`. Choosing `λ > K + 2M` makes the coefficient
`2M/(λ-K) < 1`: `Ξ` is a genuine contraction on `(C(Icc 0 T, SphereProb d), bieleckiDist)`, the last
mathematical ingredient before assembling `ContractingWith` and extracting the fixed point.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

theorem bieleckiDist_nonneg' {T lam : ℝ} (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    0 ≤ bieleckiDist (T := T) (lam := lam) η₁ η₂ := by
  unfold bieleckiDist
  exact Real.iSup_nonneg fun t => mul_nonneg (bieleckiWeight_pos (T := T) (lam := lam) t).le dist_nonneg

/-- **Transfer of the pointwise Bielecki bound to the pushforward level**, via the same
`W₁`-coupling argument leaves E3i/E3k use. -/
theorem dist_pushforwardAt_le_bielecki (p : AttnParams d) {T lam : ℝ} (hT : 0 ≤ T)
    (hlam : 0 ≤ lam) (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d))
    [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0)
    (hlamK : ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
      + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) < lam)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    dist (pushforwardAt p hT η₁ μ₀ hμ₀ ht) (pushforwardAt p hT η₂ μ₀ hμ₀ ht) ≤
      (2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
        bieleckiDist (T := T) (lam := lam) η₁ η₂ /
        (lam - ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
          + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ))) *
      (Real.exp (lam * t) - Real.exp
        (((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
          + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) * t)) :=
  dist_pushforwardAt_sub_le_of_pointwise p hT η₁ η₂ μ₀ hμ₀ ht _
    (fun _ hx => dist_trajectoryFlow_sub_le_bielecki p hT hlam η₁ η₂ hx hlamK t ht)

/-- **Bielecki-weighting collapses the bound to a `t`-independent constant.** Multiplying the
pushforward bound by `bieleckiWeight t = e^{-λt}` gives `Cf·(1 - e^{(K-λ)t})`, and `e^{(K-λ)t} ≤ 1`
since `K < λ` and `t ≥ 0`, so the weighted bound is `≤ Cf`. -/
theorem bieleckiWeight_mul_dist_pushforwardAt_le (p : AttnParams d) {T lam : ℝ} (hT : 0 ≤ T)
    (hlam : 0 ≤ lam) (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d))
    [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0)
    (hlamK : ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
      + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) < lam)
    (t : Set.Icc (0 : ℝ) T) :
    bieleckiWeight (T := T) (lam := lam) t *
      dist (pushforwardAt p hT η₁ μ₀ hμ₀ t.2) (pushforwardAt p hT η₂ μ₀ hμ₀ t.2) ≤
      2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
        bieleckiDist (T := T) (lam := lam) η₁ η₂ /
        (lam - ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
          + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ)) := by
  set K : ℝ := ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
    + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) with hK
  set Cf : ℝ := 2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
    bieleckiDist (T := T) (lam := lam) η₁ η₂ / (lam - K) with hCf
  have hDnn : (0 : ℝ) ≤ bieleckiDist (T := T) (lam := lam) η₁ η₂ := bieleckiDist_nonneg' η₁ η₂
  have hCfnn : 0 ≤ Cf := by
    rw [hCf]
    have hMnn : (0 : ℝ) ≤ ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) := by
      positivity
    have hlamKpos : (0 : ℝ) < lam - K := by linarith
    positivity
  have hbound := dist_pushforwardAt_le_bielecki p hT hlam η₁ η₂ μ₀ hμ₀ hlamK t.2
  have hweight_pos := bieleckiWeight_pos (T := T) (lam := lam) t
  calc bieleckiWeight (T := T) (lam := lam) t *
        dist (pushforwardAt p hT η₁ μ₀ hμ₀ t.2) (pushforwardAt p hT η₂ μ₀ hμ₀ t.2)
      ≤ bieleckiWeight (T := T) (lam := lam) t *
          (Cf * (Real.exp (lam * t.1) - Real.exp (K * t.1))) := by gcongr
    _ = Cf * (Real.exp (-lam * t.1) * (Real.exp (lam * t.1) - Real.exp (K * t.1))) := by
        unfold bieleckiWeight; ring
    _ = Cf * (Real.exp (-lam * t.1) * Real.exp (lam * t.1)
          - Real.exp (-lam * t.1) * Real.exp (K * t.1)) := by ring
    _ = Cf * (1 - Real.exp ((K - lam) * t.1)) := by
        have h1 : Real.exp (-lam * t.1) * Real.exp (lam * t.1) = 1 := by rw [← Real.exp_add]; simp
        have h2 : Real.exp (-lam * t.1) * Real.exp (K * t.1) = Real.exp ((K - lam) * t.1) := by
          rw [← Real.exp_add]; ring_nf
        rw [h1, h2]
    _ ≤ Cf * 1 := by
        have hexp_le : Real.exp ((K - lam) * t.1) ≤ 1 := by
          have hnn : (K - lam) * t.1 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) t.2.1
          calc Real.exp ((K - lam) * t.1) ≤ Real.exp 0 := Real.exp_le_exp.mpr hnn
            _ = 1 := Real.exp_zero
        have hsub_le : 1 - Real.exp ((K - lam) * t.1) ≤ 1 := by
          linarith [Real.exp_pos ((K - lam) * t.1)]
        exact mul_le_mul_of_nonneg_left hsub_le hCfnn
    _ = Cf := mul_one _

/-- **The genuine McKean-Vlasov contraction, at the `bieleckiDist` level.** Taking `⨆ t` of the
weighted pushforward bound: `Ξ := fun η => selfConsistencyStepCM p hT η μ₀ hμ₀` satisfies
`bieleckiDist (Ξ η₁) (Ξ η₂) ≤ (2M/(λ-K)) · bieleckiDist η₁ η₂`. Choosing `λ > K + 2M` makes this a
genuine contraction. -/
theorem bieleckiDist_selfConsistencyStepCM_le (p : AttnParams d) {T lam : ℝ} (hT : 0 ≤ T)
    (hlam : 0 ≤ lam) (η₁ η₂ : C(Set.Icc (0 : ℝ) T, SphereProb d)) (μ₀ : Measure (Eucl d))
    [IsProbabilityMeasure μ₀] (hμ₀ : μ₀ (sphere d)ᶜ = 0)
    (hlamK : ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
      + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) < lam) :
    bieleckiDist (T := T) (lam := lam)
      (selfConsistencyStepCM p hT η₁ μ₀ hμ₀) (selfConsistencyStepCM p hT η₂ μ₀ hμ₀) ≤
      2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
        bieleckiDist (T := T) (lam := lam) η₁ η₂ /
        (lam - ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
          + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ)) := by
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_refl 0, hT⟩⟩
  unfold bieleckiDist
  apply ciSup_le
  intro t
  have h := bieleckiWeight_mul_dist_pushforwardAt_le p hT hlam η₁ η₂ μ₀ hμ₀ hlamK t
  unfold selfConsistencyStepCM selfConsistencyStep at *
  exact h

end MeasureToMeasure.Foundations
