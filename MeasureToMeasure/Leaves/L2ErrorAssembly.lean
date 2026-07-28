import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# L2(mu) error bookkeeping for the lemma_5_4 campaign (G2)

`lemma_5_4`'s conclusion measures the distance between two MAPS as the raw sqrt-integral
`Real.sqrt (∫ x, ‖f x - g x‖ ^ 2 ∂μ)`, not through any of Mathlib's packaged `Lp` vocabulary.
The campaign needs exactly two abstract facts about that quantity; this file proves the first,
the triangle inequality (Minkowski), by bridging to `eLpNorm _ 2 μ` and Mathlib's
`eLpNorm_add_le`, plus the induced integrability of the composite error term.

Deliberately stated over an ABSTRACT `[MeasurableSpace α]` / `[NormedAddCommGroup E]`, in a file
importing NO project-specific `Eucl d`-touching content: `Eucl d = EuclideanSpace ℝ (Fin d)`'s
instances (via `PiLp`) are definitionally heavy enough that elaborating this kind of generic
unification INSIDE a proof can time out with `Eucl d` in scope, even though the same proof is
fast over an abstract space (see `UniformRadiusPacking.lean`). Callers at `Eucl d` should APPLY
these already-proven theorems, not re-elaborate their tactic proofs.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- **Bridge to `eLpNorm`.** For an `L²(μ)` function, the repo's raw sqrt-integral form of the
`L²` norm agrees with `(eLpNorm f 2 μ).toReal`. This is the single point where the campaign's
bespoke `Real.sqrt (∫ ‖·‖²)` vocabulary meets Mathlib's `Lp` seminorm theory. -/
theorem sqrt_integral_sq_norm_eq_toReal_eLpNorm {f : α → E} (hf : MemLp f 2 μ) :
    Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hf]
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [ENNReal.toReal_ofReal (by positivity), h2, Real.sqrt_eq_rpow]
  norm_num

/-- **Minkowski for the raw sqrt-integral `L²(μ)` distance between maps.** If the two error legs
`f - g` and `g - h` are (a.e. measurable and) square-integrable, the composite error `f - h`
satisfies the triangle inequality in the campaign's raw sqrt-integral form. Proved by bridging
each side to `eLpNorm _ 2 μ` and invoking Mathlib's `eLpNorm_add_le`. -/
theorem sqrtIntegral_sub_le_add {f g h : α → E}
    (hfg_m : AEStronglyMeasurable (fun x => f x - g x) μ)
    (hgh_m : AEStronglyMeasurable (fun x => g x - h x) μ)
    (hfg_i : Integrable (fun x => ‖f x - g x‖ ^ 2) μ)
    (hgh_i : Integrable (fun x => ‖g x - h x‖ ^ 2) μ) :
    Real.sqrt (∫ x, ‖f x - h x‖ ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, ‖f x - g x‖ ^ 2 ∂μ) + Real.sqrt (∫ x, ‖g x - h x‖ ^ 2 ∂μ) := by
  have hsum : ((fun x => f x - g x) + fun x => g x - h x) = fun x => f x - h x := by
    funext x
    simp [sub_add_sub_cancel]
  have hfg : MemLp (fun x => f x - g x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hfg_m).mpr hfg_i
  have hgh : MemLp (fun x => g x - h x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hgh_m).mpr hgh_i
  have hfh : MemLp (fun x => f x - h x) 2 μ := hsum ▸ hfg.add hgh
  rw [sqrt_integral_sq_norm_eq_toReal_eLpNorm hfg, sqrt_integral_sq_norm_eq_toReal_eLpNorm hgh,
    sqrt_integral_sq_norm_eq_toReal_eLpNorm hfh]
  have hadd : eLpNorm (fun x => f x - h x) 2 μ ≤
      eLpNorm (fun x => f x - g x) 2 μ + eLpNorm (fun x => g x - h x) 2 μ :=
    hsum ▸ eLpNorm_add_le hfg_m hgh_m (one_le_two : (1 : ℝ≥0∞) ≤ 2)
  have h1 : eLpNorm (fun x => f x - g x) 2 μ ≠ ⊤ := hfg.eLpNorm_ne_top
  have h2 : eLpNorm (fun x => g x - h x) 2 μ ≠ ⊤ := hgh.eLpNorm_ne_top
  calc (eLpNorm (fun x => f x - h x) 2 μ).toReal
      ≤ (eLpNorm (fun x => f x - g x) 2 μ + eLpNorm (fun x => g x - h x) 2 μ).toReal :=
        ENNReal.toReal_mono (by finiteness) hadd
    _ = (eLpNorm (fun x => f x - g x) 2 μ).toReal + (eLpNorm (fun x => g x - h x) 2 μ).toReal :=
        ENNReal.toReal_add h1 h2

/-- The integrability side condition induced by `sqrtIntegral_sub_le_add`'s hypotheses: if both
legs' squared errors are integrable, so is the composite `‖f - h‖²` (via `MemLp.add` at `p = 2`).
Keeps callers from re-deriving integrability of the assembled error term by hand. -/
theorem integrable_sq_norm_sub_of_legs {f g h : α → E}
    (hfg_m : AEStronglyMeasurable (fun x => f x - g x) μ)
    (hgh_m : AEStronglyMeasurable (fun x => g x - h x) μ)
    (hfg_i : Integrable (fun x => ‖f x - g x‖ ^ 2) μ)
    (hgh_i : Integrable (fun x => ‖g x - h x‖ ^ 2) μ) :
    Integrable (fun x => ‖f x - h x‖ ^ 2) μ := by
  have hsum : ((fun x => f x - g x) + fun x => g x - h x) = fun x => f x - h x := by
    funext x
    simp [sub_add_sub_cancel]
  have hfg : MemLp (fun x => f x - g x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hfg_m).mpr hfg_i
  have hgh : MemLp (fun x => g x - h x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hgh_m).mpr hgh_i
  have hfh : MemLp (fun x => f x - h x) 2 μ := hsum ▸ hfg.add hgh
  exact (memLp_two_iff_integrable_sq_norm hfh.aestronglyMeasurable).mp hfh

end MeasureToMeasure.Leaves
