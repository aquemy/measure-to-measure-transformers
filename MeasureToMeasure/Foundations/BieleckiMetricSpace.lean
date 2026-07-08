import MeasureToMeasure.Foundations.SphereProbComplete
import MeasureToMeasure.Foundations.BieleckiMetric

/-!
# `bieleckiDist` as a genuine `PseudoMetricSpace`/`MetricSpace`/`CompleteSpace` instance
(M3b existence, leaf E3b)

Leaf E3a (`BieleckiMetric.lean`) built `bieleckiDist` as a bare function, equivalent to the ambient
sup-metric on `C([0,T], SphereProb d)` but not registered as competing typeclass data. This leaf
packages it as one via `PseudoMetricSpace.replaceUniformity`: since `bieleckiDist` and the ambient
`dist` are mutually bounded (`bieleckiDist_le_dist`, `dist_le_exp_mul_bieleckiDist`), their induced
uniformities coincide, so swapping in `bieleckiDist` as the metric formula changes nothing about the
topology -- hence `CompleteSpace` transfers for free from the ambient sup-metric instance (itself
free from Mathlib's `C(α,β)` API given `[CompactSpace α] [CompleteSpace β]`, already confirmed for
`β = SphereProb d` by leaf S4, `instCompleteSpaceSphereProb`).

This gives everything `ContractingWith` needs on `C([0,T], SphereProb d)` (a `MetricSpace` -- hence
`EMetricSpace` -- and a `CompleteSpace`, both in the Bielecki metric) for the outer Picard
self-consistency map, once the contraction exponent `λ` is pinned down by the field's modulus.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Filter Topology

namespace MeasureToMeasure

variable {d : ℕ} {T lam : ℝ}

/-- `bieleckiDist` packaged as a `PseudoMetricSpace`, with its OWN (as yet unrelated) uniformity. -/
noncomputable abbrev bieleckiPseudoAux (hlam : 0 ≤ lam) :
    PseudoMetricSpace C(Set.Icc (0 : ℝ) T, SphereProb d) :=
  { dist := bieleckiDist (T := T) (lam := lam)
    dist_self := bieleckiDist_self
    dist_comm := bieleckiDist_comm
    dist_triangle := bieleckiDist_triangle hlam }

/-- **The Bielecki uniformity agrees with the ambient sup-metric uniformity.** Both directions
follow from the two-sided equivalence bound (leaf E3a): the identity map between the two metrics is
bi-Lipschitz, so their `ε`-ball filter bases refine each other. -/
theorem bieleckiUniformity_eq (hlam : 0 ≤ lam) (hT : 0 ≤ T) :
    uniformity C(Set.Icc (0 : ℝ) T, SphereProb d)
      = @uniformity C(Set.Icc (0 : ℝ) T, SphereProb d)
          (bieleckiPseudoAux (d := d) (T := T) (lam := lam) hlam).toUniformSpace := by
  have hambbasis := @Metric.uniformity_basis_dist C(Set.Icc (0 : ℝ) T, SphereProb d) inferInstance
  have hmbasis := @Metric.uniformity_basis_dist C(Set.Icc (0 : ℝ) T, SphereProb d)
    (bieleckiPseudoAux hlam)
  have hc2 : (0 : ℝ) < Real.exp (lam * T) := Real.exp_pos _
  apply le_antisymm
  · rw [hambbasis.le_basis_iff hmbasis]
    intro ε hε
    refine ⟨ε, hε, fun p hp => ?_⟩
    simp only [Set.mem_setOf_eq] at hp ⊢
    calc bieleckiDist (T := T) (lam := lam) p.1 p.2
        ≤ dist p.1 p.2 := bieleckiDist_le_dist hlam p.1 p.2
      _ < ε := hp
  · rw [hmbasis.le_basis_iff hambbasis]
    intro ε hε
    refine ⟨ε / Real.exp (lam * T), by positivity, fun p hp => ?_⟩
    simp only [Set.mem_setOf_eq] at hp ⊢
    calc dist p.1 p.2
        ≤ Real.exp (lam * T) * bieleckiDist (T := T) (lam := lam) p.1 p.2 :=
          dist_le_exp_mul_bieleckiDist hlam hT p.1 p.2
      _ < Real.exp (lam * T) * (ε / Real.exp (lam * T)) :=
          mul_lt_mul_of_pos_left hp hc2
      _ = ε := by field_simp

/-- **`bieleckiDist` as a `PseudoMetricSpace`, sharing the ambient uniformity/topology** (hence
`CompleteSpace`) via `PseudoMetricSpace.replaceUniformity`. -/
noncomputable abbrev bieleckiPseudoMetricSpace (hlam : 0 ≤ lam) (hT : 0 ≤ T) :
    PseudoMetricSpace C(Set.Icc (0 : ℝ) T, SphereProb d) :=
  (bieleckiPseudoAux hlam).replaceUniformity (bieleckiUniformity_eq hlam hT)

/-- **`bieleckiDist` as a genuine `MetricSpace`.** Identity of indiscernibles transfers from the
ambient `MetricSpace` via the domination bound `dist ≤ e^{λT}·bieleckiDist`. -/
noncomputable abbrev bieleckiMetricSpace (hlam : 0 ≤ lam) (hT : 0 ≤ T) :
    MetricSpace C(Set.Icc (0 : ℝ) T, SphereProb d) where
  toPseudoMetricSpace := bieleckiPseudoMetricSpace hlam hT
  eq_of_dist_eq_zero {f g} h := by
    have hle := dist_le_exp_mul_bieleckiDist hlam hT f g
    have h' : bieleckiDist (T := T) (lam := lam) f g = 0 := h
    rw [h', mul_zero] at hle
    exact dist_le_zero.mp hle

/-- **The Bielecki-metric space is complete**, transferred from the ambient sup-metric
`CompleteSpace` instance via the shared uniformity. -/
theorem bieleckiPseudoMetricSpace.completeSpace (hlam : 0 ≤ lam) (hT : 0 ≤ T) :
    @CompleteSpace _ (bieleckiPseudoMetricSpace (d := d) hlam hT).toUniformSpace := by
  unfold bieleckiPseudoMetricSpace PseudoMetricSpace.replaceUniformity
  infer_instance

end MeasureToMeasure
