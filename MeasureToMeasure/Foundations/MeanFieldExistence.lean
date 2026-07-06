import MeasureToMeasure.Foundations.MeanFieldWellPosed
import MeasureToMeasure.Foundations.SphereFlow

/-!
# Frozen-field bounds for mean-field existence (M3b, leaf E2-groundwork)

Groundwork toward discharging `exists_meanFieldFlow` (M3b existence). The existence proof solves the
characteristic ODE `ẋ = field(ν, x)` for a *frozen* sphere-supported measure `ν` (inside a Picard
iteration over the measure trajectory), and keeps the solution on the sphere via
`SphereFlow.sphere_invariant`. Applying that machinery to the attention field needs two facts about
the frozen field, both assembled here from the banked moduli of `MeanFieldWellPosed`:

* the field is **tangent** on the sphere — its radial component is `⟪x, rawField⟫·(1 - ‖x‖²)`, which
  vanishes on `‖x‖ = 1` (`inner_field_left`, from `SphereFlow.inner_tangentialProjector_left`); this
  is the identity `sphere_invariant`'s Grönwall consumes;
* the raw (pre-projection) field is **uniformly bounded** on the sphere by an explicit block constant
  (`norm_rawField_le_onSphere`, from `norm_attnAvg_le` + `norm_reluVec_le`), giving the radial-drift
  bound `sphere_invariant` needs.

These are the sphere-side inputs; the remaining existence work (NOT here) is the globally-Lipschitz
bounded *extension* of the field off the sphere (so Mathlib's `IsPicardLindelof.of_time_independent`
applies, as for the linear `blockFlow`), then the Picard fixed point over the measure trajectory.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The raw (pre-tangential-projection) attention velocity of a block at measure `ν`:
`V · A_B[ν](x) + W · (U x + b)₊`. The field is its tangential projection,
`p.field ν x = P_x^⊥ (rawField p ν x)`. -/
noncomputable def rawField (p : AttnParams d) (ν : Measure (Eucl d)) (x : Eucl d) : Eucl d :=
  p.V (attnAvg p.B ν x) + p.W (reluVec (p.U x + p.b))

theorem field_eq_tangentialProjector_rawField (p : AttnParams d) (ν : Measure (Eucl d))
    (x : Eucl d) : p.field ν x = tangentialProjector x (rawField p ν x) := rfl

/-- **Tangency / radial identity.** The radial component of the field is `⟪x, rawField⟫·(1 - ‖x‖²)`,
so on the sphere (`‖x‖ = 1`) the field is tangent. This is exactly the `hrad` hypothesis of
`SphereFlow.sphere_invariant` (with raw drift `⟪x, rawField p ν x⟫`). -/
theorem inner_field_left (p : AttnParams d) (ν : Measure (Eucl d)) (x : Eucl d) :
    ⟪x, p.field ν x⟫ = ⟪x, rawField p ν x⟫ * (1 - ‖x‖ ^ 2) := by
  rw [field_eq_tangentialProjector_rawField, inner_tangentialProjector_left]

/-- **Uniform bound on the raw field over the sphere.** For a sphere-supported probability measure
`ν`, the raw attention velocity is bounded on the sphere by the explicit block constant
`‖V‖·e^{2‖B‖} + ‖W‖·(‖U‖ + ‖b‖)`: the attention average is bounded by `e^{2‖B‖}` (`norm_attnAvg_le`)
and the perceptron term by `‖W‖·(‖U‖ + ‖b‖)` (`reluVec` is nonexpansive, `‖x‖ = 1`). -/
theorem norm_rawField_le_onSphere (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {x : Eucl d} (hx : x ∈ sphere d) :
    ‖rawField p ν x‖ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by
  have hx1 : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  -- attention term: ‖V (A_B[ν] x)‖ ≤ ‖V‖ · e^{2‖B‖}
  have hV : ‖p.V (attnAvg p.B ν x)‖ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) := by
    refine (p.V.le_opNorm _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_attnAvg_le p.B hν (le_of_eq hx1)) (norm_nonneg _)
  -- perceptron term: ‖W ((U x + b)₊)‖ ≤ ‖W‖ · (‖U‖ + ‖b‖)
  have hW : ‖p.W (reluVec (p.U x + p.b))‖ ≤ ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by
    refine (p.W.le_opNorm _).trans ?_
    refine mul_le_mul_of_nonneg_left ((norm_reluVec_le _).trans ?_) (norm_nonneg _)
    calc ‖p.U x + p.b‖ ≤ ‖p.U x‖ + ‖p.b‖ := norm_add_le _ _
      _ ≤ ‖p.U‖ * ‖x‖ + ‖p.b‖ := by gcongr; exact p.U.le_opNorm x
      _ = ‖p.U‖ + ‖p.b‖ := by rw [hx1, mul_one]
  calc ‖rawField p ν x‖ ≤ ‖p.V (attnAvg p.B ν x)‖ + ‖p.W (reluVec (p.U x + p.b))‖ :=
        norm_add_le _ _
    _ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by gcongr

end MeasureToMeasure.Foundations
