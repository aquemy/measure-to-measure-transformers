import MeasureToMeasure.Foundations.SphereMeasureBridge
import MeasureToMeasure.Foundations.WassersteinFinite

/-!
# The `W₁` pseudometric on sphere-supported probability measures (M3b existence, leaf S2)

Third leaf of the Wasserstein completeness sub-campaign toward `exists_meanFieldFlow` (M3b existence),
following the subtype bridge S1 and the `W₁` finiteness S2a. We equip the carrier
`SphereProb d := {μ : Measure (Eucl d) // IsProbabilityMeasure μ ∧ μ (sphere d)ᶜ = 0}` (leaf S1) with
its `W₁` (pseudo)metric `dist μ ν := (W1 μ.val ν.val).toReal`.

We register a `PseudoMetricSpace`, not yet a `MetricSpace`: the three pseudometric axioms are the
banked `W1_self_eq_zero`, `W1_comm`, `W1_triangle` (the last, an `ℝ≥0∞` inequality, becomes the
`ℝ`-valued triangle inequality via `ENNReal.toReal_add`/`toReal_mono` using the S2a finiteness
`W1_ne_top_of_sphere_supported`). Identity of indiscernibles `W₁ = 0 ⇒ μ = ν` is **deliberately
deferred**: it is not standalone here (it follows from the crux `W₁ ↔ Lévy–Prokhorov` comparison — a
metric distinguishing the measures — via the LP metric's own `T₀`), so the `MetricSpace` upgrade and
the completeness transport are the following leaves (S3/S4). What this leaf fixes is the `W₁`
**uniformity/topology** on `SphereProb d`, the object those leaves compare against the (complete)
Lévy–Prokhorov uniformity banked in `SphereMeasureCompletion`.
-/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace MeasureToMeasure

variable {d : ℕ}

namespace SphereProb

/-- The `W₁` distance between sphere-supported probability measures (finite by S2a, so `toReal` is
faithful). -/
noncomputable def w1dist (μ ν : SphereProb d) : ℝ := (W1 μ.val ν.val).toReal

theorem w1dist_ne_top (μ ν : SphereProb d) : W1 μ.val ν.val ≠ ⊤ :=
  haveI := μ.property.1
  haveI := ν.property.1
  W1_ne_top_of_sphere_supported μ.property.2 ν.property.2

/-- The `W₁` distance is bounded by the diameter of the sphere, `2`. -/
theorem w1dist_le_two (μ ν : SphereProb d) : w1dist μ ν ≤ 2 := by
  haveI := μ.property.1
  haveI := ν.property.1
  have h : W1 μ.val ν.val ≤ 2 := W1_le_two_of_sphere_supported μ.property.2 ν.property.2
  calc w1dist μ ν = (W1 μ.val ν.val).toReal := rfl
    _ ≤ (2 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by norm_num) h
    _ = 2 := by simp

end SphereProb

/-- **The `W₁` pseudometric on sphere-supported probability measures.** `dist μ ν = (W₁ μ ν).toReal`,
with the three pseudometric axioms from the banked `W₁` self/symmetry/triangle facts (the triangle via
S2a finiteness). Not yet a `MetricSpace` — identity of indiscernibles awaits the `W₁ ↔ LP` comparison. -/
noncomputable instance : PseudoMetricSpace (SphereProb d) where
  dist μ ν := SphereProb.w1dist μ ν
  dist_self μ := by rw [SphereProb.w1dist, W1_self_eq_zero, ENNReal.toReal_zero]
  dist_comm μ ν := by rw [SphereProb.w1dist, SphereProb.w1dist, W1_comm]
  dist_triangle μ ν ρ := by
    haveI := μ.property.1; haveI := ν.property.1; haveI := ρ.property.1
    have hμν := SphereProb.w1dist_ne_top μ ν
    have hνρ := SphereProb.w1dist_ne_top ν ρ
    calc SphereProb.w1dist μ ρ
        ≤ (W1 μ.val ν.val + W1 ν.val ρ.val).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hμν, hνρ⟩) (W1_triangle μ.val ν.val ρ.val)
      _ = SphereProb.w1dist μ ν + SphereProb.w1dist ν ρ := ENNReal.toReal_add hμν hνρ

/-- The `W₁` `dist` on `SphereProb d` unfolds to `(W₁ · ·).toReal` (for rewriting). -/
theorem SphereProb.dist_eq (μ ν : SphereProb d) : dist μ ν = (W1 μ.val ν.val).toReal := rfl

/-- Distances in `SphereProb d` are bounded by `2` (the sphere's diameter). -/
theorem SphereProb.dist_le_two (μ ν : SphereProb d) : dist μ ν ≤ 2 := SphereProb.w1dist_le_two μ ν

end MeasureToMeasure
