import MeasureToMeasure.Statements.MidLevel

/-!
# `exists_disentangling_balls` leaf 5, first piece: the Phase-3-regime non-degeneracy hypothesis

`exists_disentangling_balls`' induction (`exists-disentangling-balls-campaign` project notes) needs
`lemma_3_4_part2`'s Phase 3 applied specifically to a colinear-unequal pair ALREADY confined to a
shared small ball (produced by Phase 1's `lemma_3_3` shrinking step) -- and a dispatched research
fork found this near-Dirac regime almost certainly VIOLATES `lemma_3_4_part2`'s `hgenRest`
hypothesis (both measures' leftover-mass integrals collapse toward the same shared ball center to
leading order). So Phase 3 needs its OWN non-degeneracy hypothesis, restricted to this regime, rather
than reusing the public `lemma_3_4_part2` (which discards bystander-fixing anyway, via `U :=
Set.univ`) -- matching this project's `hgenRest` precedent (PR #260) of gating a genuinely open
degeneracy behind an explicit hypothesis rather than proving it unconditionally.

* `GenRestNearBall` -- `hgenRest`'s rest-component non-parallelism, universally quantified over
  every possible confining ball (center, radius) and every admissible confined pair, since the
  induction's own step doesn't get to choose which ball Phase 1 produces in advance.
* `exists_phase3_of_genRestNearBall` -- Phase 3 itself, applied inside the induction: given
  `GenRestNearBall`, a colinear-unequal pair already confined to a shared ball becomes fully
  non-colinear after some schedule, while fixing every point outside an ARBITRARY open carrier `U`
  -- retaining bystander-fixing (calls `Leaves.barycenter_nonColinear_of_massGapCollapse_meanField`
  directly, not the public `lemma_3_4_part2` wrapper, which fixes `U := Set.univ`).

M3b/mid-level staging: consumed when `exists_disentangling_balls`'s full induction is assembled; see
`Statements/MainResults.lean` and the `exists-disentangling-balls-campaign` project notes. Whether
`GenRestNearBall` itself holds is NOT addressed here -- it remains a genuinely open question (see the
project notes for the near-Dirac mechanistic argument suggesting it's a delicate, possibly false,
regime), staged as an explicit hypothesis for whoever assembles the rest of the induction.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements
open MeasureToMeasure.Leaves (barycenter restComp)
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Phase-3-regime non-degeneracy**: `hgenRest`'s rest-component non-parallelism, but only
required for measure pairs already confined to a SHARED small ball -- exactly the regime
`exists_disentangling_balls`' Phase 3 actually needs. -/
def GenRestNearBall (d : ℕ) : Prop :=
  ∀ (center : Eucl d) (ε' : ℝ), 0 < ε' →
    ∀ μ ν : Measure (Eucl d), [IsProbabilityMeasure μ] → [IsProbabilityMeasure ν] →
    μ ≠ ν →
    supportedIn μ (sphere d) → supportedIn ν (sphere d) →
    supportedIn μ (orthant d) → supportedIn ν (orthant d) →
    supportedIn μ (Metric.ball center ε') → supportedIn ν (Metric.ball center ε') →
    (∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ barycenter μ = γ • barycenter ν) →
    ∀ z : Eucl d, ‖z‖ = 1 → ∀ cosR : ℝ, cosR ∈ Set.Ioo (1 / 2 : ℝ) 1 →
      ∀ w : Eucl d, ‖w‖ = 1 → (⟪z, w⟫ : ℝ) = 0 →
      restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν) ≠ 0 ∧
      ∀ c : ℝ, restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ)
        ≠ c • restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν)

/-- **Phase 3, applied inside the induction**: given `GenRestNearBall`, a colinear-unequal pair
already confined to a shared ball becomes fully non-colinear after some schedule, while fixing every
point outside an arbitrary open carrier `U` -- retaining bystander-fixing (unlike the public
`lemma_3_4_part2`, which discards it by fixing `U := Set.univ`). -/
theorem exists_phase3_of_genRestNearBall [NeZero d] (hgen : GenRestNearBall d)
    (center : Eucl d) (ε' : ℝ) (hε' : 0 < ε') (μ ν : Measure (Eucl d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (hμball : supportedIn μ (Metric.ball center ε')) (hνball : supportedIn ν (Metric.ball center ε'))
    (hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ barycenter μ = γ • barycenter ν)
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hμU : supportedIn μ U) (hνU : supportedIn ν U) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧ AttnSchedule.switches θ ≤ 2 ∧
      (∀ γ₂ : ℝ, barycenter (attnMeasureFlow θ μ) ≠ γ₂ • barycenter (attnMeasureFlow θ ν)) ∧
      (∃ Φ : Eucl d → Eucl d, Measurable Φ ∧ attnMeasureFlow θ μ = μ.map Φ ∧
        ∀ x ∈ sphere d, x ∉ U → Φ x = x) ∧
      ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        supportedIn ρ Uᶜ → attnMeasureFlow θ ρ = ρ := by
  have hgenRest : ∀ z : Eucl d, ‖z‖ = 1 → ∀ cosR : ℝ, cosR ∈ Set.Ioo (1 / 2 : ℝ) 1 →
      ∀ w : Eucl d, ‖w‖ = 1 → (⟪z, w⟫ : ℝ) = 0 →
      restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν) ≠ 0 ∧
      ∀ c : ℝ, restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ)
        ≠ c • restComp z w (∫ x in {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂ν) :=
    hgen center ε' hε' μ ν hne hμs hνs hμ hν hμball hνball hcol
  exact Leaves.barycenter_nonColinear_of_massGapCollapse_meanField μ ν T hT hne hμs hνs hμ hν
    U hUopen hμU hνU hgenRest

end MeasureToMeasure.Leaves
