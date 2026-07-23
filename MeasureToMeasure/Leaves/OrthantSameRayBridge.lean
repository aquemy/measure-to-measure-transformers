import MeasureToMeasure.Leaves.OrthantBoundaryGap

/-!
# `SameRay` failure is full non-colinearity, on the orthant

`exists_disentangling_balls`' induction (`exists-disentangling-balls-campaign` / group G5,
`disentangle_insert_colinear`) needs, at several points, to certify a bystander's flowed barycenter
is not merely `¬ SameRay` but genuinely `∀ c : ℝ, ... ≠ c • ...` (the shape `lemma_3_3`'s own
`hnoncol`/`hνcol` hypotheses are stated in, and the shape the whole induction's non-colinearity
bookkeeping consistently uses). The one machine-checked separation-to-non-colinearity bridge on hand
(`GeodesicHullConvex.lean`'s `barycenter_not_sameRay_of_separated_balls`) only delivers `¬ SameRay`.

This file closes that gap for orthant-supported data (which is always the case here, since every
family member carries `supportedIn (orthant d)` throughout the induction): on the open positive
orthant `{x | ∀ i, 0 < x i}`, ANY scalar-multiple relation `x = c • y` between two orthant points
forces the scalar strictly POSITIVE (read off a single coordinate: both `x i, y i > 0` pin the sign
of `c`), so `¬ SameRay ℝ x y` -- which by definition already rules out every NONNEGATIVE-scalar
relation -- rules out literally every real scalar relation once orthant membership is known. This
turns the existing separation lemma into exactly the shape the induction needs, with no new
geometric content: `barycenter_ne_smul_of_separated_balls` composes it with
`barycenter_mem_orthant` (`OrthantBoundaryGap.lean`) directly.

M3b/mid-level staging: consumed by `disentangle_insert_colinear`'s bystander/companion
non-colinearity checks; see `Statements/MainResults.lean` and the
`exists-disentangling-balls-campaign` project notes. `r := max r₁ r₂` is the intended instantiation
for a pairwise check between two balls of possibly-different radii (shrinking either ball to the
smaller radius only helps containment, so the single shared-radius separation hypothesis
`2 * max r₁ r₂ ≤ dist α₁ α₂` is the easy direction to supply).
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Statements
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Orthant colinearity is `SameRay`.** In the open positive orthant, any scalar-multiple relation
`x = c • y` between two orthant points forces a POSITIVE scalar, hence `SameRay`. Contrapositive:
`¬ SameRay ℝ x y` already rules out EVERY real scalar relation between two orthant points, not just
the nonnegative ones a bare `SameRay` failure rules out in general. -/
theorem ne_smul_of_orthant_not_sameRay [NeZero d] {x y : Eucl d}
    (hx : x ∈ orthant d) (hy : y ∈ orthant d) (hnsr : ¬ SameRay ℝ x y) :
    ∀ c : ℝ, x ≠ c • y := by
  intro c hxy
  apply hnsr
  have hxi : 0 < x (0 : Fin d) := hx 0
  have hyi : 0 < y (0 : Fin d) := hy 0
  have hcxy : x (0 : Fin d) = c * y (0 : Fin d) := by
    have h := congrFun (congrArg (fun z : Eucl d => (z : Fin d → ℝ)) hxy) 0
    simpa using h
  have hcpos : 0 < c := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hyi.le]
  rw [hxy, sameRay_smul_left_iff]
  left; exact hcpos.le

/-- **Separated small balls give FULLY non-colinear orthant barycenters.** The measure form of
`barycenter_not_sameRay_of_separated_balls`, upgraded from `¬ SameRay` to the shape the induction
actually needs (`∀ c, barycenter μ ≠ c • barycenter ν`), by combining it with
`ne_smul_of_orthant_not_sameRay` once both barycenters are pinned into the orthant
(`barycenter_mem_orthant`). -/
theorem barycenter_ne_smul_of_separated_balls {μ ν : Measure (Eucl d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NeZero d] {α₁ α₂ : Eucl d}
    (hα₁ : ‖α₁‖ = 1) (hα₂ : ‖α₂‖ = 1) {r : ℝ} (hr : 0 < r) (hsep : 2 * r ≤ dist α₁ α₂)
    (hμs : μ (sphere d)ᶜ = 0) (hνs : ν (sphere d)ᶜ = 0)
    (hμb : μ (Metric.ball α₁ r)ᶜ = 0) (hνb : ν (Metric.ball α₂ r)ᶜ = 0)
    (hμo : μ (orthant d)ᶜ = 0) (hνo : ν (orthant d)ᶜ = 0) :
    ∀ c : ℝ, barycenter μ ≠ c • barycenter ν := by
  have hμint := integrable_id_of_sphere_support hμs
  have hνint := integrable_id_of_sphere_support hνs
  have hμmem : barycenter μ ∈ orthant d := barycenter_mem_orthant hμs hμint hμo
  have hνmem : barycenter ν ∈ orthant d := barycenter_mem_orthant hνs hνint hνo
  exact ne_smul_of_orthant_not_sameRay hμmem hνmem
    (barycenter_not_sameRay_of_separated_balls hα₁ hα₂ hr hsep hμs hνs hμb hνb)

end MeasureToMeasure.Leaves
