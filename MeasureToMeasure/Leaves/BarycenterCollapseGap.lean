import MeasureToMeasure.Leaves.BarycenterWasserstein
import MeasureToMeasure.Leaves.WassersteinCompare

/-!
# Leaf (Lemma 3.4 Part 1, Path I assembly): barycenter separation from a `W₂` collapse gap

The App. B.3 Part 1 separation compares the two flowed barycenters through their collapse targets:
each flowed measure is `W₂`-close to a collapsed measure whose barycenter is known (Lemma B.2), and the
two collapse barycenters are forced apart by the mass gap. This leaf packages the bookkeeping — the
`W₁`-Lipschitz barycenter (`norm_barycenter_sub_le_W1`), the `W₁ ≤ W₂` comparison, the sphere-support
finiteness of `W₂` — into two reusable statements:

* `norm_barycenter_sub_le_W2` — `‖ℰ_μ − ℰ_ν‖ ≤ W₂(μ, ν)` for sphere-supported probability measures;
* `barycenter_ne_of_W2_gap` — if `P, Q` are `W₂`-close (within `rP, rQ`) to `α, β`, and the collapse
  barycenters satisfy `rP + rQ < ‖ℰ_α − ℰ_β‖`, then `ℰ_P ≠ ℰ_Q` (triangle inequality).
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- Sphere support gives `‖x‖ ≤ 1` almost everywhere. -/
private theorem ae_norm_le_one_of_sphere_support {μ : Measure (Eucl d)} (hμs : μ (sphere d)ᶜ = 0) :
    ∀ᵐ x ∂μ, ‖x‖ ≤ 1 := by
  have hmem : ∀ᵐ x ∂μ, x ∈ sphere d := mem_ae_iff.mpr hμs
  filter_upwards [hmem] with x hx
  rw [norm_eq_one_of_mem_sphere hx]

/-- **The barycenter is `W₂`-Lipschitz** for sphere-supported probability measures. Chains the
`W₁`-Lipschitz barycenter with `W₁ ≤ W₂`; the finiteness of `W₂` (bounded support) discharges both the
`W₁`-finiteness hypothesis and the `toReal` monotonicity. -/
theorem norm_barycenter_sub_le_W2 {μ ν : Measure (Eucl d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμs : μ (sphere d)ᶜ = 0) (hνs : ν (sphere d)ᶜ = 0) :
    ‖barycenter μ - barycenter ν‖ ≤ Axioms.W2 μ ν := by
  have hW2fin : MeasureToMeasure.W2 μ ν ≠ ⊤ :=
    MeasureToMeasure.W2_ne_top_of_ae_norm_le μ ν
      (ae_norm_le_one_of_sphere_support hμs) (ae_norm_le_one_of_sphere_support hνs)
  have hW1fin : MeasureToMeasure.W1 μ ν ≠ ⊤ :=
    ne_top_of_le_ne_top hW2fin MeasureToMeasure.W1_le_W2
  calc ‖barycenter μ - barycenter ν‖ ≤ Axioms.W1 μ ν := norm_barycenter_sub_le_W1 hμs hνs hW1fin
    _ ≤ Axioms.W2 μ ν := by
        show (MeasureToMeasure.W1 μ ν).toReal ≤ (MeasureToMeasure.W2 μ ν).toReal
        exact ENNReal.toReal_mono hW2fin MeasureToMeasure.W1_le_W2

/-- **Barycenter separation from a collapse gap.** If `P, Q` are `W₂`-close to `α, β` (within `rP, rQ`
respectively), all four sphere-supported probability measures, and the collapse barycenters are farther
apart than `rP + rQ`, then the flowed barycenters differ: `ℰ_P ≠ ℰ_Q`. -/
theorem barycenter_ne_of_W2_gap {P Q α β : Measure (Eucl d)}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hPs : P (sphere d)ᶜ = 0) (hQs : Q (sphere d)ᶜ = 0)
    (hαs : α (sphere d)ᶜ = 0) (hβs : β (sphere d)ᶜ = 0)
    {rP rQ : ℝ} (hPα : Axioms.W2 P α ≤ rP) (hQβ : Axioms.W2 Q β ≤ rQ)
    (hgap : rP + rQ < ‖barycenter α - barycenter β‖) :
    barycenter P ≠ barycenter Q := by
  intro hEq
  have h1 := norm_barycenter_sub_le_W2 hPs hαs
  have h2 := norm_barycenter_sub_le_W2 hQs hβs
  have htri : ‖barycenter α - barycenter β‖
      ≤ ‖barycenter P - barycenter α‖ + ‖barycenter Q - barycenter β‖ := by
    calc ‖barycenter α - barycenter β‖
        = ‖(barycenter α - barycenter P) + (barycenter Q - barycenter β)‖ := by
          rw [hEq]; congr 1; abel
      _ ≤ ‖barycenter α - barycenter P‖ + ‖barycenter Q - barycenter β‖ := norm_add_le _ _
      _ = ‖barycenter P - barycenter α‖ + ‖barycenter Q - barycenter β‖ := by rw [norm_sub_rev]
  linarith [h1, h2, hPα, hQβ, htri, hgap]

end MeasureToMeasure.Leaves
