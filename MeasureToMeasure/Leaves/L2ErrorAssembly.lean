import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# L2(mu) error bookkeeping for the lemma_5_4 campaign (G2)

`lemma_5_4`'s conclusion measures the distance between two MAPS as the raw sqrt-integral
`Real.sqrt (∫ x, ‖f x - g x‖ ^ 2 ∂μ)`, not through any of Mathlib's packaged `Lp` vocabulary.
The campaign needs exactly two abstract facts about that quantity; this file proves both:
the triangle inequality (Minkowski), by bridging to `eLpNorm _ 2 μ` and Mathlib's
`eLpNorm_add_le`, plus the induced integrability of the composite error term; and the good/bad
collar-mass ledger `sqrtIntegral_le_of_good_bad`, with its induced integrability side condition
`integrable_sq_norm_of_ae_bound`.

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

/-- A uniform a.e. bound gives integrability of the squared norm on a finite measure: the
`Integrable` side condition every use of the good/bad ledger (and of `sqrtIntegral_sub_le_add`)
needs at the call site. -/
theorem integrable_sq_norm_of_ae_bound [IsFiniteMeasure μ] {φ : α → E} {C : ℝ}
    (hm : AEStronglyMeasurable φ μ) (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C) :
    Integrable (fun x => ‖φ x‖ ^ 2) μ := by
  refine Integrable.mono' (integrable_const (C ^ 2)) ?_ ?_
  · exact (hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  · filter_upwards [hb] with x hx
    have h0 : (0 : ℝ) ≤ ‖φ x‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith

/-- **The good/bad collar-mass ledger.** If the pointwise error of a pair of maps is a.e. at most
`δ` off a measurable bad set `S`, a.e. at most `C` globally, and `μ S ≤ η` with `η` FINITE, then
the raw sqrt-integral `L²(μ)` error is at most `√(δ² + C²·η.toReal)`: the good set pays `δ²`, the
collar pays `C²` per unit of its `≤ η` mass (on-sphere maps have `C = 2`, so the collar pays
`4η`). The finiteness hypothesis `hη` is load-bearing, not bookkeeping: with `η = ∞` the claimed
bound is FALSE, since `η.toReal` collapses to `0` while the remaining hypotheses still allow
error `C` on all of `S`. The nonnegativity hypotheses `0 ≤ δ`, `0 ≤ C` are the paper's scope
(error tolerances); this proof happens not to consume them, so they are underscore-prefixed per
house rule, never dropped. -/
theorem sqrtIntegral_le_of_good_bad [IsProbabilityMeasure μ] {f g : α → E}
    (hm : AEStronglyMeasurable (fun x => f x - g x) μ)
    {S : Set α} (hS : MeasurableSet S) {δ C : ℝ} {η : ℝ≥0∞}
    (_hδ : 0 ≤ δ) (_hC : 0 ≤ C) (hη : η ≠ ⊤)
    (hgood : ∀ᵐ x ∂μ, x ∉ S → ‖f x - g x‖ ≤ δ)
    (hbound : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ C)
    (hbad : μ S ≤ η) :
    Real.sqrt (∫ x, ‖f x - g x‖ ^ 2 ∂μ) ≤ Real.sqrt (δ ^ 2 + C ^ 2 * η.toReal) := by
  have hint : Integrable (fun x => ‖f x - g x‖ ^ 2) μ :=
    integrable_sq_norm_of_ae_bound hm hbound
  have hpt : ∀ᵐ x ∂μ, ‖f x - g x‖ ^ 2 ≤ S.indicator (fun _ => C ^ 2) x + δ ^ 2 := by
    filter_upwards [hgood, hbound] with x hx1 hx2
    have h0 : (0 : ℝ) ≤ ‖f x - g x‖ := norm_nonneg _
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      nlinarith
    · rw [Set.indicator_of_notMem hxS, zero_add]
      have := hx1 hxS
      nlinarith
  have hrhs_int : Integrable (fun x => S.indicator (fun _ => C ^ 2) x + δ ^ 2) μ :=
    ((integrable_const (C ^ 2)).indicator hS).add (integrable_const _)
  have h1 : ∫ x, ‖f x - g x‖ ^ 2 ∂μ ≤ ∫ x, (S.indicator (fun _ => C ^ 2) x + δ ^ 2) ∂μ :=
    integral_mono_ae hint hrhs_int hpt
  have h2 : ∫ x, (S.indicator (fun _ => C ^ 2) x + δ ^ 2) ∂μ = C ^ 2 * (μ S).toReal + δ ^ 2 := by
    rw [integral_add ((integrable_const (C ^ 2)).indicator hS) (integrable_const _),
      integral_indicator_const _ hS, integral_const]
    simp [mul_comm, measureReal_def]
  have h3 : (μ S).toReal ≤ η.toReal := ENNReal.toReal_mono hη hbad
  apply Real.sqrt_le_sqrt
  have hC2 : (0 : ℝ) ≤ C ^ 2 := by positivity
  nlinarith [h1, h2.le, h2.ge, ENNReal.toReal_nonneg (a := μ S)]

end MeasureToMeasure.Leaves
