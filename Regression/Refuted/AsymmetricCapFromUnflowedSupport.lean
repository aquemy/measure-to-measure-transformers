import MeasureToMeasure.Foundations.Sphere
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# A shared-support pair can never witness an asymmetric cap (`phase4_asymmetric_massgap_cap`, G2)

`phase4_asymmetric_massgap_cap`'s group G2 checked the most naive possible route to the campaign's
target axiom `exists_asymmetric_massgap_cap`: could an open cap `B` with `ν B = 0` but `μ B ≠ 0`
(an "asymmetric" cap) already be produced just from `μ.support = ν.support`, with no flow at all?

**It cannot.** `naive_hsupp_cap_infeasible` below is a genuine, kernel-checked negative finding: if
`μ.support = ν.support` and `B` is open with `ν B = 0`, then `μ B = 0` too. The one-line argument
is purely topological: an open null set for `ν` is disjoint from `ν`'s support
(`Measure.subset_compl_support_of_isOpen`), hence (via the shared-support hypothesis) disjoint from
`μ`'s support too, and the complement of any measure's support is itself null
(`Measure.measure_compl_support`, valid here since `Eucl d` is a hereditarily Lindelöf space), so
`μ B ≤ μ μ.supportᶜ = 0`. No sphere/orthant/probability/flow structure is used or needed.

**Scope warning, read before citing this lemma anywhere near `exists_asymmetric_massgap_cap`.**
This result is about a single, LITERALLY shared support between two UNFLOWED measures `μ`/`ν`
(the campaign's `μ0`/`ν0`, before any mean-field evolution is applied). It does **not** refute, nor
does it place any obstruction on, the real target `exists_asymmetric_massgap_cap`, which is a
statement about the FLOWED / pushed-forward measures `Φ_μ0(T) # μ0` and `Φ_ν0(T) # ν0` under two
flow maps `Φ_μ0 ≠ Φ_ν0` that are in general genuinely different from each other, because the
mean-field velocity field driving the flow is itself measure-dependent (`Φ_μ0` is built from `μ0`'s
own barycenter/cap data, `Φ_ν0` from `ν0`'s). Two flowed pushforwards of measures that started with
identical (or merely equal-support) unflowed data can easily end up with UNEQUAL supports after
evolving under two different flow maps -- that measure-dependence is exactly the mechanism the real
asymmetric-cap construction is expected to exploit, and this lemma's hypothesis (`hsupp` on the
UNFLOWED pair) simply never arises there. Do not read this file as bearing on, blocking, or
narrowing that separate, still-to-be-built axiom.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure

variable {d : ℕ}

/-- **Naive shared-support cap is always infeasible.** If two measures `μ`, `ν` on `Eucl d` share
literally the same support, no open cap `B` that is `ν`-null can carry positive `μ`-mass either.
Scoped strictly to the UNFLOWED entry measures: see the file docstring for why this does not
transfer to the flowed/pushforward pair the real `exists_asymmetric_massgap_cap` target needs. -/
theorem naive_hsupp_cap_infeasible {μ ν : Measure (Eucl d)} (hsupp : μ.support = ν.support)
    {B : Set (Eucl d)} (hB : IsOpen B) (hνB : ν B = 0) : μ B = 0 := by
  have hBsub : B ⊆ ν.supportᶜ := Measure.subset_compl_support_of_isOpen hB hνB
  rw [← hsupp] at hBsub
  have hle : μ B ≤ μ μ.supportᶜ := measure_mono hBsub
  rw [Measure.measure_compl_support] at hle
  exact le_antisymm hle bot_le

end Regression.Refuted
