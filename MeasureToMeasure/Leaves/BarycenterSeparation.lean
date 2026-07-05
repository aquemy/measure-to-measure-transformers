import MeasureToMeasure.Leaves.Pigeonhole
import MeasureToMeasure.Leaves.BarycenterNonColinear

/-!
# Leaf L3a (Lemma 3.4 Part 1): the pigeonhole that picks a separating collapse point

The heart of Lemma 3.4 Part 1 (paper App. B.3, p.35). Having found an open ball `B` on which the two
measures carry **different mass** (`μ B ≠ ν B`), the perceptron collapses the `B`-mass of each measure
onto a single point `x* ∈ B` while fixing everything off `B` (Lemma B.2 for the collapse, the off-cap
parking `flowMap_gatedBlock_id_of_inner_le` for the fixing). The collapsed barycenters are then

  `ℰ_{ϕ#μ}[x] = μ(B)·x* + ∫_{∖B} x dμ`   and   `ℰ_{ϕ#ν}[x] = ν(B)·x* + ∫_{∖B} x dν`,

so **separating the barycenters reduces to choosing `x*` with**

  `μ(B)·x* + ∫_{∖B} x dμ ≠ ν(B)·x* + ∫_{∖B} x dν`.

The paper's argument for such an `x*`: if the equality held for *every* `x* ∈ B`, then `x*` would be
forced to the single fixed vector `[∫_{∖B} x d(ν−μ)]/(μ(B)−ν(B))` for all `x*` in an open ball —
impossible, since an open ball is not a point (leaf L10, `exists_ne_in_ball`). The scalar
`μ(B)−ν(B) ≠ 0` (the mass gap) is exactly what makes that fixed vector well-defined and the argument
bite; it is why the "measures differ on some ball" step is load-bearing.

The core is the *affine* pigeonhole `exists_mem_ball_smul_ne` (`c ≠ 0 ⇒ some ball point escapes
`c • x = w`); the barycenter form is its rearrangement. No integrability of the tail integrals is
needed — they enter only as fixed vectors.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory
open scoped RealInnerProductSpace

/-- The affine pigeonhole underlying Lemma 3.4 Part 1: for a nonzero scalar `c`, the equation
`c • x = w` has a unique solution, so an open ball (not a point) contains some `x` with `c • x ≠ w`.
Built directly on leaf L10 (`exists_ne_in_ball`). -/
theorem exists_mem_ball_smul_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {c : ℝ} (hc : c ≠ 0) (w a : E) {R : ℝ} (hR : 0 < R) :
    ∃ x ∈ Metric.ball a R, c • x ≠ w := by
  obtain ⟨x, hxB, hx⟩ := exists_ne_in_ball a (c⁻¹ • w) hR
  refine ⟨x, hxB, fun h => hx ?_⟩
  -- `c • x = w` forces `x = c⁻¹ • w`, contradicting `x ≠ c⁻¹ • w`
  have := congrArg (fun v => c⁻¹ • v) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using this

variable {d : ℕ}

/-- **L3a.** The barycenter-separation pigeonhole of Lemma 3.4 Part 1 (App. B.3). If the two finite
measures carry different mass on `B` (`μ B ≠ ν B`), then some `x*` in any positive-radius ball realizes

  `μ(B)·x* + ∫_{∖B} x dμ ≠ ν(B)·x* + ∫_{∖B} x dν`,

i.e. collapsing each measure's `B`-mass onto `x*` (Lemma B.2) and fixing the rest separates the two
barycenters. The mass gap `μ B ≠ ν B` supplies the nonzero scalar `(μ B).toReal − (ν B).toReal` that
the affine pigeonhole `exists_mem_ball_smul_ne` needs. -/
theorem exists_mem_ball_barycenter_collapse_ne [Nontrivial (Eucl d)]
    {μ ν : Measure (Eucl d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {B : Set (Eucl d)} (hmass : μ B ≠ ν B) (a : Eucl d) {R : ℝ} (hR : 0 < R) :
    ∃ x ∈ Metric.ball a R,
      (μ B).toReal • x + ∫ y in Bᶜ, y ∂μ ≠ (ν B).toReal • x + ∫ y in Bᶜ, y ∂ν := by
  set p : Eucl d := ∫ y in Bᶜ, y ∂μ with hp
  set q : Eucl d := ∫ y in Bᶜ, y ∂ν with hq
  have hc : (μ B).toReal - (ν B).toReal ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hmass (by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ B), ← ENNReal.ofReal_toReal (measure_ne_top ν B),
        h])
  obtain ⟨x, hxB, hx⟩ :=
    exists_mem_ball_smul_ne (E := Eucl d) hc (q - p) a hR
  refine ⟨x, hxB, fun h => hx ?_⟩
  -- rearrange `μ(B)·x + p = ν(B)·x + q` into `((μ B).toReal − (ν B).toReal) • x = q − p`
  rw [sub_smul]
  linear_combination (norm := module) h
end MeasureToMeasure.Leaves
