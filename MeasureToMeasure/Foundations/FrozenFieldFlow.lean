import MeasureToMeasure.Foundations.FrozenFieldBlock

/-!
# The frozen-field characteristic flow (M3b existence, leaf E2b)

With `frozenBlock` (leaf E2a-4) a genuine well-posed `Block`, the generic `Block.blockFlow` machinery
of `FlowMap.lean` — proven for *every* `Block` (identity at `0`, semigroup, injectivity/bijectivity,
**sphere invariance** for `t ≥ 0` via the radial gate, Grönwall Lipschitz dependence, measurability) —
gives the point flow `Φ^t` of the frozen field `ẋ = attnFieldExt p ν x` essentially for free.

This leaf packages that flow as `frozenFlow p ν` and adds the one fact the generic machinery cannot
state: **on the sphere its velocity is the paper's field** `p.field ν`. On the sphere `attnFieldExt`
equals `p.field ν` (`attnFieldExt_eq_field_of_mem_sphere`), and the flow keeps `Φ^t x` on the sphere,
so the block field's integral-curve derivative `attnFieldExt p ν (Φ^t x)` is exactly
`p.field ν (Φ^t x)` — the `deriv` clause of `IsMeanFieldFlow`, for the **frozen** measure `ν`.

This is the inner step of the mean-field Picard iteration: it solves the characteristic ODE at a fixed
`ν`; the remaining existence work (E-crux/E3) makes `ν` self-consistent with the pushforward
trajectory `(Φ_t)_# μ₀`, via a fixed point in the measure variable.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The **frozen-field characteristic flow**: the point flow of `frozenBlock`, i.e. the solution
operator `Φ^t` of `ẋ = attnFieldExt p ν x` (which on the sphere is `ẋ = p.field ν x`). All the flow
algebra (identity at `0`, sphere invariance, Lipschitz/measurable dependence) is inherited from the
generic `Block.blockFlow`; the new fact is that on the sphere its velocity is the paper's field. -/
noncomputable def frozenFlow (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) : ℝ → Eucl d → Eucl d :=
  (frozenBlock p ν hν p.duration_nonneg).blockFlow

theorem frozenFlow_zero (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) : frozenFlow p ν hν 0 = id :=
  (frozenBlock p ν hν p.duration_nonneg).blockFlow_zero_eq_id

/-- The frozen flow **preserves the sphere** for `t ≥ 0` (radial-tangency of `attnFieldExt`). -/
theorem frozenFlow_mem_sphere (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : 0 ≤ t) :
    frozenFlow p ν hν t x ∈ sphere d :=
  (frozenBlock p ν hν p.duration_nonneg).blockFlow_mem_sphere hx ht

/-- Each time slice of the frozen flow is Lipschitz in the initial value (`t ≥ 0`). -/
theorem lipschitzWith_frozenFlow (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith (Real.exp ((frozenBlock p ν hν p.duration_nonneg).lipConst * t)).toNNReal
      (frozenFlow p ν hν t) :=
  (frozenBlock p ν hν p.duration_nonneg).lipschitzWith_blockFlow ht

/-- Each time slice of the frozen flow is measurable (`t ≥ 0`). -/
theorem measurable_frozenFlow (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {t : ℝ} (ht : 0 ≤ t) : Measurable (frozenFlow p ν hν t) :=
  (frozenBlock p ν hν p.duration_nonneg).measurable_blockFlow ht

/-- The frozen flow maps the sphere into itself for `t ≥ 0`. -/
theorem frozenFlow_mapsTo_sphere (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {t : ℝ} (ht : 0 ≤ t) :
    Set.MapsTo (frozenFlow p ν hν t) (sphere d) (sphere d) :=
  fun _ hx => frozenFlow_mem_sphere p ν hν hx ht

/-- **The frozen characteristic ODE on the sphere.** For `x ∈ 𝕊^{d-1}` and `t ≥ 0`, the trajectory
`s ↦ Φ^s x` solves `ẋ = p.field ν x`: the block field's integral curve has velocity
`attnFieldExt p ν (Φ^t x)`, which on the sphere (where the flow stays) is exactly `p.field ν (Φ^t x)`.
This is the `deriv` clause of `IsMeanFieldFlow` for the *frozen* measure `ν` — the inner step of the
mean-field Picard iteration, before `ν` is made self-consistent with `(Φ_t)_# μ₀`. -/
theorem frozenFlow_hasDerivAt_field (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => frozenFlow p ν hν s x) (p.field ν (frozenFlow p ν hν t x)) t := by
  set b := frozenBlock p ν hν p.duration_nonneg with hb
  have hcurve : HasDerivAt (b.blockCurve x) (b.field (b.blockCurve x t)) t :=
    b.blockCurve_isIntegralCurve x t
  have hmem : b.blockCurve x t ∈ sphere d := by
    have h := b.blockFlow_mem_sphere hx ht
    simpa only [Block.blockFlow] using h
  have hfield : b.field (b.blockCurve x t) = p.field ν (b.blockCurve x t) :=
    attnFieldExt_eq_field_of_mem_sphere p ν hmem
  rw [hfield] at hcurve
  exact hcurve

end MeasureToMeasure.Foundations
