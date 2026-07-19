import MeasureToMeasure.Statements.MidLevel

/-!
# Leaf 2 (`exists_disentangling_balls`, Phase-1 bookkeeping): shrink disjoint from bystanders

`exists_disentangling_balls`' strong induction (see the `exists-disentangling-balls-campaign` project
notes) processes family members one at a time via `lemma_3_3`: each new member `j` (with its collinear
companion `ν₀`) gets shrunk into a tiny ball around `j`'s own barycenter direction, while EVERY
bystander `i ≠ j` stays exactly fixed (`lemma_3_3`'s own literal conclusion). Phase 1 of the induction
needs the shrunk ball to land disjoint from every bystander's ALREADY-placed ball -- pure metric
bookkeeping, no new flow-bridging or analytic machinery, since `lemma_3_3` already supplies an
arbitrary target radius `ε > 0` to shrink into.

* `exists_ball_disjoint_of_dist_pos` -- the general geometric fact: a ball around a point stays
  disjoint from a FINITE family of other balls, for small enough radius, given the point is farther
  from each center than that ball's own radius. (`ε := min_i (dist α (β i) - r i)`, via
  `Metric.ball_disjoint_ball`.)
* `exists_shrink_disjoint_from_bystanders` -- composes this with `lemma_3_3`: given a separation
  hypothesis between `j`'s barycenter direction and every bystander's ball, `lemma_3_3`'s shrinking
  schedule can be chosen to land disjoint from all of them, while still fixing every bystander exactly.

M3b/mid-level staging: consumed when `exists_disentangling_balls`'s full induction is assembled; see
`Statements/MainResults.lean` and the `exists-disentangling-balls-campaign` project notes. The
separation hypothesis `hsep` itself (why `j`'s direction stays away from bystanders' balls as the
induction proceeds) is NOT supplied here -- that is the induction's OWN invariant, to be established
when the induction itself is assembled (this leaf is deliberately parametrized over an abstract
bystander family `β, r`, not tied to any specific induction step).
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements
open MeasureToMeasure.Leaves (barycenter)
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- A ball around `α` stays disjoint from every ball in a FINITE family `B(β i, r i)`, for a small
enough radius, given `α` is farther from each `β i` than that ball's own radius `r i`. -/
theorem exists_ball_disjoint_of_dist_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ι → Eucl d) (r : ι → ℝ) (α : Eucl d) (hsep : ∀ i, r i < dist α (β i)) :
    ∃ ε > 0, ∀ i, Disjoint (Metric.ball α ε) (Metric.ball (β i) (r i)) := by
  set ε := Finset.univ.inf' Finset.univ_nonempty (fun i => dist α (β i) - r i) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro i _
    linarith [hsep i]
  refine ⟨ε, hεpos, fun i => ?_⟩
  apply Metric.ball_disjoint_ball
  have hle : ε ≤ dist α (β i) - r i := Finset.inf'_le _ (Finset.mem_univ i)
  linarith

/-- **Leaf 2 (Phase-1 bookkeeping): the shrunk pair can be placed disjoint from every bystander.**
Given `lemma_3_3`'s shrinking mechanism applied to member `j` and companion `ν₀`, and a separation
hypothesis between `j`'s barycenter direction and every bystander's already-fixed ball, there is a
schedule shrinking `j`/`ν₀` into SOME ball around `j`'s barycenter direction that is disjoint from
every bystander's ball -- while leaving every bystander exactly fixed. -/
theorem exists_shrink_disjoint_from_bystanders {N : ℕ} (j : Fin N) (μ₀ : Fin N → Measure (Eucl d))
    (ν₀ : Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) [IsProbabilityMeasure ν₀]
    (T : ℝ) (hT : 0 < T)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hμo : ∀ i, supportedIn (μ₀ i) (orthant d))
    (hνs : supportedIn ν₀ (sphere d)) (hνo : supportedIn ν₀ (orthant d))
    (hnoncol : Pairwise fun i k => ∀ c : ℝ, barycenter (μ₀ i) ≠ c • barycenter (μ₀ k))
    (hνcol : ∃ c : ℝ, barycenter ν₀ = c • barycenter (μ₀ j))
    {ι : Type*} [Fintype ι] [Nonempty ι] (β : ι → Eucl d) (r : ι → ℝ)
    (hsep : ∀ i, r i < dist (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) (β i)) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      (∃ ε > 0, supportedIn (attnMeasureFlow θ ν₀)
          (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε) ∧
        supportedIn (attnMeasureFlow θ (μ₀ j))
          (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε) ∧
        ∀ i, Disjoint (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε)
          (Metric.ball (β i) (r i))) ∧
      ∀ i, i ≠ j → attnMeasureFlow θ (μ₀ i) = μ₀ i := by
  obtain ⟨ε, hεpos, hdisj⟩ := exists_ball_disjoint_of_dist_pos β r
    (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) hsep
  obtain ⟨θ, hdur, hshrinkν, hshrinkμ, hfix⟩ :=
    lemma_3_3 j μ₀ ν₀ hμ T ε hT hεpos hμs hμo hνs hνo hnoncol hνcol
  exact ⟨θ, hdur, ⟨ε, hεpos, hshrinkν, hshrinkμ, hdisj⟩, hfix⟩

end MeasureToMeasure.Leaves
