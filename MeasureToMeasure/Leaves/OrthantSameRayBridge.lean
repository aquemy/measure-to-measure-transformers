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

/-- **A nonzero vector has at most one colinear partner in a pairwise non-colinear family**
(the at-most-one-partner fact of arXiv:2411.04551v3, p.17, as pure algebra). Colinearity through a
NONZERO vector is transitive: if `v ≠ 0` is a scalar multiple of both `w₁` and `w₂`, then the
scalar against `w₁` is forced nonzero (else `v = 0`), so `w₁ = (c₁⁻¹ * c₂) • w₂`, contradicting
the standing non-colinearity of `w₁` and `w₂`. Sibling of `ne_smul_flip_of_ne_zero`
(`DisentangleInductionStep.lean`), which handles the one-vector flip the same way. -/
theorem colinear_partner_unique {v w₁ w₂ : Eucl d} (hv : v ≠ 0)
    (h1 : ∃ c : ℝ, v = c • w₁) (h2 : ∃ c : ℝ, v = c • w₂)
    (hne : ∀ c : ℝ, w₁ ≠ c • w₂) : False := by
  obtain ⟨c₁, hc₁⟩ := h1
  obtain ⟨c₂, hc₂⟩ := h2
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₁
    exact hv hc₁
  exact hne (c₁⁻¹ * c₂) (by rw [mul_smul, ← hc₂, hc₁, inv_smul_smul₀ hc₁0])

/-- **`Fin N`-indexed corollary: THE colinear partner is unique.** Given a family `b` that is
pairwise fully non-colinear (the `Pairwise (∀ c, b i ≠ c • b j)` shape the disentangling
induction's bookkeeping consistently carries, with nonzeroness of the members available separately
via `norm_barycenter_pos_of_orthant` when `b` is a barycenter family), a NONZERO vector `v`
colinear with two DISTINCT members' vectors is impossible. This is what lets the induction's case
split pick THE unique partner `j` of a new member and keep the bystander non-colinearity
(`hbys`-style hypotheses) establishable for every remaining index. -/
theorem colinear_partner_unique_pairwise {N : ℕ} {b : Fin N → Eucl d}
    (hnoncol : Pairwise (fun i j : Fin N => ∀ c : ℝ, b i ≠ c • b j))
    {v : Eucl d} (hv : v ≠ 0) {i j : Fin N} (hij : i ≠ j)
    (hi : ∃ c : ℝ, v = c • b i) (hj : ∃ c : ℝ, v = c • b j) : False :=
  colinear_partner_unique hv hi hj (hnoncol hij)

end MeasureToMeasure.Leaves
