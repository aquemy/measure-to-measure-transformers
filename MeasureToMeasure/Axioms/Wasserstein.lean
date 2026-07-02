import MeasureToMeasure.Foundations.Wasserstein

/-!
# Wasserstein distance and optimal transport: definitions and remaining axioms

Mathlib `v4.31.0` has no developed optimal-transport theory. `Foundations/Wasserstein.lean` now
builds the genuine `W₁`/`W₂²` Kantorovich costs (over couplings) with their metric structure and the
Kantorovich-Rubinstein bound. This file exposes the ℝ-valued interface the paper's proofs use and
**discharges what has been built**:

* `W1` is now a **definition** (`(Foundations.W1 μ ν).toReal`), and `W1_ge_of_lipschitz` is a **proved
  theorem** (from `ofReal_integral_sub_le_W1`), carrying the integrability and finiteness hypotheses
  the honest statement requires. So the Markov bound (Claim 2, `Leaves/MarkovBound.lean`) no longer
  rests on any `W₁` axiom.

`W₂` is kept as an **opaque axiom** for now: its remaining facts (`W2_map_le_L2`, `W2_triangle`,
`W2_convexCombo_le`) are consumed by the mid-level assembly *without* the integrability hypotheses a
faithful discharge needs, so turning `W₂` into a concrete definition while keeping those as
hypothesis-free axioms would risk an unsound axiom about a concrete term. Discharging them is future
work (it requires threading integrability through the mid-levels, plus the `W₂` triangle/Minkowski
and convexity facts).
-/

namespace MeasureToMeasure.Axioms

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- AXIOM: the quadratic Wasserstein distance `W_2` between (Borel) measures on `ℝ^d`.
Absent from Mathlib `v4.31.0`. -/
axiom W2 (μ ν : Measure (Eucl d)) : ℝ

/-- AXIOM: `W_2` is nonnegative. -/
axiom W2_nonneg (μ ν : Measure (Eucl d)) : 0 ≤ W2 μ ν

/-- AXIOM: `W_2` is symmetric. -/
axiom W2_comm (μ ν : Measure (Eucl d)) : W2 μ ν = W2 ν μ

/-- AXIOM: `W_2` satisfies the triangle inequality. -/
axiom W2_triangle (μ ν ρ : Measure (Eucl d)) : W2 μ ρ ≤ W2 μ ν + W2 ν ρ

/-- AXIOM (the content of Lemma 5.2, map-induced coupling bound): the `W_2` distance between two
pushforwards of `μ` is controlled by the `L²(μ)` distance of the maps. This is the optimal-transport
fact that Lemma 5.2 invokes; with no Mathlib `W_2` it is taken as an axiom. -/
axiom W2_map_le_L2 (μ : Measure (Eucl d)) (T₁ T₂ : Eucl d → Eucl d) :
    W2 (μ.map T₁) (μ.map T₂) ≤ Real.sqrt (∫ x, ‖T₁ x - T₂ x‖ ^ 2 ∂μ)

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

/-- AXIOM (convexity of `W₂` under mixtures). For probability measures, the `W₂` distance between two
convex combinations sharing the same weights is at most the uniform bound on the component distances.
This is the gluing-of-couplings estimate `W₂(∑ aₖ Pₖ, ∑ aₖ Qₖ)² ≤ ∑ aₖ W₂(Pₖ, Qₖ)²` (couple each pair
optimally and sum the couplings), packaged in the form actually used: if every component is within
`ε`, so is the mixture. A standard optimal-transport fact, absent from Mathlib `v4.31.0`. -/
axiom W2_convexCombo_le {M : ℕ} (a : Fin M → ℝ≥0∞) (P Q : Fin M → Measure (Eucl d))
    (ha : ∑ k, a k = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ k, IsProbabilityMeasure (P k)) (hQ : ∀ k, IsProbabilityMeasure (Q k))
    (hbound : ∀ k, W2 (P k) (Q k) ≤ ε) :
    W2 (∑ k, a k • P k) (∑ k, a k • Q k) ≤ ε

end MeasureToMeasure.Axioms
