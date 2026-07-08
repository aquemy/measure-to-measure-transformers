import MeasureToMeasure.Foundations.FrozenFieldBlock
import MeasureToMeasure.Foundations.MeanFieldWellPosed

/-!
# The extended field's global measure-Lipschitz modulus (M3b existence, leaf E3c)

`MeanFieldWellPosed.norm_field_sub_measure_W1_le` gives the paper's field `p.field` a `W₁`-Lipschitz
modulus in the measure, but only **on the sphere** (`x ∈ sphere d`) — it is built from
`attnAvg_sub_measure_le`, whose on-sphere Kantorovich–Rubinstein step needs the *coupling* to live on
`sphere × sphere`. The outer Picard self-consistency map (E3+) evaluates the field along a whole
trajectory of frozen flows, `attnFieldExt p (ν t) (Φ_ν s x)`, and the continuity-in-`t` clause of
Mathlib's time-dependent `IsPicardLindelof` needs this modulus **off** the sphere too (the frozen
flow point stays on the sphere, but stating/using continuity of `t ↦ attnFieldExt p (ν t) x` for a
generic `x` in the ball where `IsPicardLindelof`'s hypotheses are phrased is cleaner with a global
bound).

This leaf lifts the modulus to the whole space, through the same `ballProj` retraction that made
`rawFieldBall`/`attnFieldExt` globally well-behaved in the *point* variable (leaf E2a):

* `norm_rawFieldBall_sub_measure_le` — `rawFieldBall` (softmax + perceptron, ball-retracted) is
  globally `W₁`-Lipschitz in the measure with exactly `MeanFieldWellPosed`'s sphere-only constant,
  since `ballProj x` always lands in the unit ball where `attnAvg_sub_measure_le` already applies;
* `norm_attnFieldExt_sub_measure_le` — pushing that through the tangential projector (linear in its
  argument, `‖P_x^⊥ v‖ ≤ (1+‖x‖²)‖v‖`) gives `attnFieldExt`'s global modulus, growing quadratically in
  `‖x‖` (no cutoff-driven flattening here, since the two measures being compared, not a base point,
  vary — `normCutoff` bounds the *scalar* factor by `1`, it does not need the on-ball projector bound
  `5C` from leaf E2a-3, which is for *two base points, one field value*, not *one base point, two
  field values*).

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **`rawFieldBall` is globally Lipschitz in the measure for `W₁`**, with exactly the sphere-only
constant of `MeanFieldWellPosed.attnAvg_sub_measure_le`: the ball retraction `ballProj x` always
lands in the closed unit ball, where that bound already applies. -/
theorem norm_rawFieldBall_sub_measure_le (p : AttnParams d) {ν ν' : Measure (Eucl d)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hνS : ν (sphere d)ᶜ = 0) (hν'S : ν' (sphere d)ᶜ = 0) (hW1 : W1 ν ν' ≠ ⊤) (x : Eucl d) :
    ‖rawFieldBall p ν x - rawFieldBall p ν' x‖ ≤
      ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) * (W1 ν ν').toReal := by
  have hball : ‖ballProj x‖ ≤ 1 := norm_ballProj_le x
  have e1 : rawFieldBall p ν x - rawFieldBall p ν' x
      = p.V (attnAvg p.B ν (ballProj x) - attnAvg p.B ν' (ballProj x)) := by
    simp only [rawFieldBall, rawField, map_sub]; abel
  rw [e1]
  calc ‖p.V (attnAvg p.B ν (ballProj x) - attnAvg p.B ν' (ballProj x))‖
      ≤ ‖p.V‖ * ‖attnAvg p.B ν (ballProj x) - attnAvg p.B ν' (ballProj x)‖ := p.V.le_opNorm _
    _ ≤ ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖) * (W1 ν ν').toReal) := by
        gcongr
        exact attnAvg_sub_measure_le p.B hνS hν'S hW1 hball
    _ = ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) * (W1 ν ν').toReal := by
        ring

/-- **`attnFieldExt`'s global measure modulus.** The extended field is Lipschitz in the measure for
`W₁`, with the `rawFieldBall` constant scaled by `(1 + ‖x‖²)` from the tangential projector's
linearity in its (fixed base point, varying) argument. Unlike the point-Lipschitz composite bounds
of leaf E2a-3 (`ProjectorVarying`), which compare *two base points* against *one* field value on the
ball of radius `2`, this compares *one base point* against *two* field values (from the two
measures) globally — so it needs only `norm_tangentialProjector_le_general`, not the on-ball
`5`-constant. -/
theorem norm_attnFieldExt_sub_measure_le (p : AttnParams d) {ν ν' : Measure (Eucl d)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hνS : ν (sphere d)ᶜ = 0) (hν'S : ν' (sphere d)ᶜ = 0) (hW1 : W1 ν ν' ≠ ⊤) (x : Eucl d) :
    ‖attnFieldExt p ν x - attnFieldExt p ν' x‖ ≤
      (1 + ‖x‖ ^ 2) *
      (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) * (W1 ν ν').toReal) := by
  unfold attnFieldExt
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  have hproj : tangentialProjector x (rawFieldBall p ν x)
      - tangentialProjector x (rawFieldBall p ν' x)
      = tangentialProjector x (rawFieldBall p ν x - rawFieldBall p ν' x) := by
    simp only [tangentialProjector_apply, inner_sub_right, sub_smul]; abel
  rw [hproj]
  calc |normCutoff x| * ‖tangentialProjector x (rawFieldBall p ν x - rawFieldBall p ν' x)‖
      ≤ 1 * ((1 + ‖x‖ ^ 2) * ‖rawFieldBall p ν x - rawFieldBall p ν' x‖) := by
        gcongr
        · exact abs_normCutoff_le_one x
        · exact norm_tangentialProjector_le_general x _
    _ ≤ 1 * ((1 + ‖x‖ ^ 2) *
        (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) * (W1 ν ν').toReal)) := by
        gcongr
        exact norm_rawFieldBall_sub_measure_le p hνS hν'S hW1 x
    _ = (1 + ‖x‖ ^ 2) *
        (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) * (W1 ν ν').toReal) := by
        ring

end MeasureToMeasure.Foundations
