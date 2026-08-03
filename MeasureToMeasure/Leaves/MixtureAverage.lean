import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Mixture-average bookkeeping: the uniform average of finitely many measures

The map-targets companion to `exists_parked_schedule` transports a FAMILY of measures
`ν : Fin N → Measure (Eucl d)` with one schedule by feeding their uniform average
`avgMeasure ν = N⁻¹ • ∑ i, ν i` to the single-measure engine and reading the per-member
conclusions back off the mixture. This file collects the generic measure-theoretic bookkeeping
that reading-back needs: the average is a probability measure supported where all members are,
each member is dominated by `N • avgMeasure ν`, a.e. properties pass from the members to the
mixture, and (Real-valued, nonnegative) integrals against a member are controlled by `N` times
the integral against the mixture, with the `Integrable` transfer that makes the comparison
meaningful.

Deliberately stated over an ABSTRACT measurable space `α`, in a file importing NO project
`Eucl d`-touching content, per the repo's PiLp-unification gotcha: `Eucl d`'s instances are
heavy enough to time out generic elaboration, and none of this is about `Eucl d` anyway.
Callers apply these lemmas (cheap term-mode instantiation) where `Eucl d` is needed. In
particular `avgMeasure_supportedIn` is stated in the raw `ν sᶜ = 0` form, which is
DEFINITIONALLY the `Statements.supportedIn` predicate at `Eucl d` (`supportedIn μ s : Prop :=
μ sᶜ = 0`), so consumers can use it for `supportedIn` without this file importing the
`Eucl d`-specific vocabulary.

The fiddly point is ENNReal-vs-Real integral domination: `integral_le_card_mul_avg` is stated
in the Real (Bochner) form with an explicit `Integrable` hypothesis ON THE MIXTURE side, and
`integrable_of_avgMeasure` supplies the member-side transfer from it via the domination
`ν i ≤ N • avgMeasure ν` (`Integrable.smul_measure` + `Integrable.mono_measure`), avoiding any
`lintegral` conversion at the use site.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {N : ℕ}

/-- The uniform average (mixture) of a finite family of measures: `N⁻¹ • ∑ i, ν i`. -/
noncomputable def avgMeasure (ν : Fin N → Measure α) : Measure α :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, ν i

/-- A set null for every member is null for the mixture. -/
theorem avgMeasure_null (ν : Fin N → Measure α) {s : Set α} (h : ∀ i, ν i s = 0) :
    avgMeasure ν s = 0 := by
  simp [avgMeasure, Measure.smul_apply, h]

/-- Support bookkeeping: if every member carries no mass outside `s`, neither does the mixture.
Stated in the raw `· sᶜ = 0` form, definitionally `supportedIn` at the `Eucl d` use site. -/
theorem avgMeasure_supportedIn (ν : Fin N → Measure α) {s : Set α} (h : ∀ i, ν i sᶜ = 0) :
    avgMeasure ν sᶜ = 0 :=
  avgMeasure_null ν h

/-- The uniform average of `N ≠ 0` probability measures is a probability measure. -/
theorem isProbabilityMeasure_avgMeasure (hN : N ≠ 0) (ν : Fin N → Measure α)
    (hν : ∀ i, IsProbabilityMeasure (ν i)) : IsProbabilityMeasure (avgMeasure ν) := by
  constructor
  have hsum : (∑ i, ν i) Set.univ = (N : ℝ≥0∞) := by
    rw [Measure.coe_finsetSum]
    simp [(hν _).measure_univ]
  rw [avgMeasure, Measure.smul_apply, hsum, smul_eq_mul,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hN) (natCast_ne_top N)]

/-- Each member is dominated by `N` times the mixture: `ν i ≤ N • avgMeasure ν`. -/
theorem member_le_smul_avgMeasure (hN : N ≠ 0) (ν : Fin N → Measure α) (i : Fin N) :
    ν i ≤ (N : ℝ≥0∞) • avgMeasure ν := by
  have hcancel : (N : ℝ≥0∞) • avgMeasure ν = ∑ j, ν j := by
    rw [avgMeasure, smul_smul,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hN) (natCast_ne_top N), one_smul]
  rw [hcancel]
  exact Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)

/-- A property holding a.e. against every member holds a.e. against the mixture. -/
theorem ae_avgMeasure_of_forall (ν : Fin N → Measure α) {P : α → Prop}
    (h : ∀ i, ∀ᵐ x ∂ν i, P x) : ∀ᵐ x ∂avgMeasure ν, P x := by
  rw [ae_iff]
  exact avgMeasure_null ν fun i => ae_iff.mp (h i)

/-- `Integrable` transfer from the mixture to each member, via the domination
`ν i ≤ N • avgMeasure ν` (this is what lets the displacement's square-norm integral against a
member be meaningful when the engine only certifies it against the mixture). -/
theorem integrable_of_avgMeasure {E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hN : N ≠ 0) (ν : Fin N → Measure α) (hf : Integrable f (avgMeasure ν)) (i : Fin N) :
    Integrable f (ν i) :=
  (hf.smul_measure (natCast_ne_top N)).mono_measure (member_le_smul_avgMeasure hN ν i)

/-- Nonnegative Real-integral domination: `∫ f ∂ν i ≤ N * ∫ f ∂avgMeasure ν`. The `Integrable`
hypothesis lives on the MIXTURE side (the side the engine certifies); the member side follows by
`integrable_of_avgMeasure`. -/
theorem integral_le_card_mul_avg {f : α → ℝ} (hN : N ≠ 0) (ν : Fin N → Measure α)
    (hf : 0 ≤ f) (hint : Integrable f (avgMeasure ν)) (i : Fin N) :
    ∫ x, f x ∂ν i ≤ N * ∫ x, f x ∂avgMeasure ν := by
  have hsmul : Integrable f ((N : ℝ≥0∞) • avgMeasure ν) := hint.smul_measure (natCast_ne_top N)
  calc ∫ x, f x ∂ν i
      ≤ ∫ x, f x ∂((N : ℝ≥0∞) • avgMeasure ν) :=
        integral_mono_measure (member_le_smul_avgMeasure hN ν i)
          (Filter.Eventually.of_forall hf) hsmul
    _ = N * ∫ x, f x ∂avgMeasure ν := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_natCast]

end MeasureToMeasure.Leaves
