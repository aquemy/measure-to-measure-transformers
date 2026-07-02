import MeasureToMeasure.Foundations.Wasserstein

/-!
# Wasserstein distance and optimal transport: definitions and remaining axioms

Mathlib `v4.31.0` has no developed optimal-transport theory. `Foundations/Wasserstein.lean` now
builds the genuine `W₁`/`W₂` Kantorovich costs (over couplings) with their metric structure, the
Kantorovich-Rubinstein bound, the `W₂` triangle/convexity/map facts, and `W₂` finiteness for
boundedly-supported measures. This file exposes the ℝ-valued interface the paper's proofs use and
**discharges it all**:

* `W1` is a **definition** (`(Foundations.W1 μ ν).toReal`), and `W1_ge_of_lipschitz` is a **proved
  theorem** (from `ofReal_integral_sub_le_W1`).

* `W2` is now a **definition** too (`(Foundations.W2 μ ν).toReal`), and its structural facts
  (`W2_nonneg`, `W2_comm`, `W2_triangle`, `W2_map_le_L2`, `W2_convexCombo_le`) are **proved theorems**
  over the `ℝ≥0∞` Kantorovich cost. `toReal` sends `⊤` to `0`, so the triangle/convexity facts carry
  the **finiteness** hypotheses a faithful `ℝ` statement needs (`Foundations.W2 · · ≠ ⊤`, discharged at
  the call sites from bounded/sphere support via `W2_ne_top_of_ae_norm_le`), and the map bound carries
  the **measurability + integrability** hypotheses that make the `ℝ≥0∞ → ℝ` bridge sound. Nothing about
  `W₂` is axiomatised any more.
-/

namespace MeasureToMeasure.Axioms

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The quadratic Wasserstein distance `W_2`, ℝ-valued interface: the real part of the `ℝ≥0∞`-valued
root Kantorovich cost built in `Foundations/Wasserstein.lean`. **Now a definition, not an axiom.** -/
noncomputable def W2 (μ ν : Measure (Eucl d)) : ℝ := (MeasureToMeasure.W2 μ ν).toReal

/-- `W_2` is nonnegative (a `toReal`). -/
theorem W2_nonneg (μ ν : Measure (Eucl d)) : 0 ≤ W2 μ ν := ENNReal.toReal_nonneg

/-- `W_2` is symmetric. Discharged from `Foundations.W2_comm`. -/
theorem W2_comm (μ ν : Measure (Eucl d)) : W2 μ ν = W2 ν μ := by
  show (MeasureToMeasure.W2 μ ν).toReal = (MeasureToMeasure.W2 ν μ).toReal
  rw [MeasureToMeasure.W2_comm]

/-- `W_2` satisfies the triangle inequality, for probability measures with finite pairwise distances.
Discharged from `Foundations.W2_triangle` (an `ℝ≥0∞` inequality) via `toReal` monotonicity, which needs
the two right-hand distances finite. -/
theorem W2_triangle (μ ν ρ : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] (hμν : MeasureToMeasure.W2 μ ν ≠ ⊤) (hνρ : MeasureToMeasure.W2 ν ρ ≠ ⊤) :
    W2 μ ρ ≤ W2 μ ν + W2 ν ρ := by
  show (MeasureToMeasure.W2 μ ρ).toReal ≤ (MeasureToMeasure.W2 μ ν).toReal + (MeasureToMeasure.W2 ν ρ).toReal
  rw [← ENNReal.toReal_add hμν hνρ]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hμν, hνρ⟩) (MeasureToMeasure.W2_triangle μ ν ρ)

/-- The map-induced coupling bound (content of Lemma 5.2): the `W_2` distance between two pushforwards
of `μ` is controlled by the `L²(μ)` distance of the maps. Discharged from the map coupling
`(T₁, T₂)_# μ`; measurability and integrability of the displacement make the `ℝ≥0∞ → ℝ` bridge sound. -/
theorem W2_map_le_L2 (μ : Measure (Eucl d)) (T₁ T₂ : Eucl d → Eucl d)
    (hT₁ : Measurable T₁) (hT₂ : Measurable T₂)
    (hint : Integrable (fun x => ‖T₁ x - T₂ x‖ ^ 2) μ) :
    W2 (μ.map T₁) (μ.map T₂) ≤ Real.sqrt (∫ x, ‖T₁ x - T₂ x‖ ^ 2 ∂μ) := by
  set I : ℝ := ∫ x, ‖T₁ x - T₂ x‖ ^ 2 ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hcpl : MeasureToMeasure.IsCoupling (μ.map fun x => (T₁ x, T₂ x)) (μ.map T₁) (μ.map T₂) :=
    ⟨Measure.fst_map_prodMk hT₂, Measure.snd_map_prodMk hT₁⟩
  have hcost : MeasureToMeasure.sqTransportCost (μ.map fun x => (T₁ x, T₂ x)) = ENNReal.ofReal I := by
    rw [MeasureToMeasure.sqTransportCost, lintegral_map (by fun_prop) (by fun_prop),
      hI, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hchain : MeasureToMeasure.W2 (μ.map T₁) (μ.map T₂) ≤ ENNReal.ofReal (Real.sqrt I) := by
    calc MeasureToMeasure.W2 (μ.map T₁) (μ.map T₂)
        ≤ MeasureToMeasure.sqTransportCost (μ.map fun x => (T₁ x, T₂ x)) ^ (2⁻¹ : ℝ) :=
          MeasureToMeasure.W2_le_rpow_sqTransportCost hcpl
      _ = ENNReal.ofReal I ^ (2⁻¹ : ℝ) := by rw [hcost]
      _ = ENNReal.ofReal (I ^ (2⁻¹ : ℝ)) := ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt I) := by rw [Real.sqrt_eq_rpow, one_div]
  show (MeasureToMeasure.W2 (μ.map T₁) (μ.map T₂)).toReal ≤ Real.sqrt I
  rw [← ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain

/-- The `W_1` Kantorovich distance, ℝ-valued interface: the real part of the `ℝ≥0∞`-valued cost built
in `Foundations/Wasserstein.lean`. **Now a definition, not an axiom.** -/
noncomputable def W1 (μ ν : Measure (Eucl d)) : ℝ := (MeasureToMeasure.W1 μ ν).toReal

/-- **Kantorovich-Rubinstein bound (the `W_1` direction used for the Markov bound, Claim 2), now a
theorem.** For a `1`-Lipschitz `f` (integrable against both measures) and finite `W₁`, the dual
pairing lower-bounds `W₁`. Proved from `Foundations.ofReal_integral_sub_le_W1`; the integrability and
finiteness hypotheses are what the faithful statement requires (the earlier axiom silently assumed
finite first moments, valid for the compactly-supported measures on the sphere the paper uses). -/
theorem W1_ge_of_lipschitz (μ ν : Measure (Eucl d)) (f : Eucl d → ℝ) (hf : LipschitzWith 1 f)
    (hfμ : Integrable f μ) (hfν : Integrable f ν) (hfin : MeasureToMeasure.W1 μ ν ≠ ⊤) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ W1 μ ν := by
  show ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ (MeasureToMeasure.W1 μ ν).toReal
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  exact MeasureToMeasure.ofReal_integral_sub_le_W1 hf hfμ hfν

/-- Convexity of `W₂` under mixtures: if every component pair is within `ε` (and at finite `W₂`), so is
the mixture. The gluing-of-couplings estimate `W₂(∑ aₖ Pₖ, ∑ aₖ Qₖ) ≤ ε`, discharged from
`Foundations.W2_convexCombo_le`. The per-component finiteness lets each `ℝ` bound `W2 (P k) (Q k) ≤ ε`
lift to the `ℝ≥0∞` bound `Foundations.W2 (P k) (Q k) ≤ ofReal ε` the `ℝ≥0∞` lemma consumes. -/
theorem W2_convexCombo_le {M : ℕ} (a : Fin M → ℝ≥0∞) (P Q : Fin M → Measure (Eucl d))
    (ha : ∑ k, a k = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ k, IsProbabilityMeasure (P k)) (hQ : ∀ k, IsProbabilityMeasure (Q k))
    (hfin : ∀ k, MeasureToMeasure.W2 (P k) (Q k) ≠ ⊤)
    (hbound : ∀ k, W2 (P k) (Q k) ≤ ε) :
    W2 (∑ k, a k • P k) (∑ k, a k • Q k) ≤ ε := by
  have hcomp : ∀ k, MeasureToMeasure.W2 (P k) (Q k) ≤ ENNReal.ofReal ε := fun k => by
    rw [ENNReal.le_ofReal_iff_toReal_le (hfin k) hε]; exact hbound k
  show (MeasureToMeasure.W2 (∑ k, a k • P k) (∑ k, a k • Q k)).toReal ≤ ε
  rw [← ENNReal.toReal_ofReal hε]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (MeasureToMeasure.W2_convexCombo_le a ha hcomp)

end MeasureToMeasure.Axioms
