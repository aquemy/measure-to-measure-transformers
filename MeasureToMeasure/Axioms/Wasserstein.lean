import MeasureToMeasure.Foundations.Sphere

/-!
# Labeled axioms: Wasserstein distance and optimal transport

Mathlib `v4.31.0` has no developed optimal-transport theory: it provides the Lévy-Prokhorov metric
and the topology of weak convergence, but not the Wasserstein distances `W_p`, Kantorovich-
Rubinstein duality, or transport-map existence. The paper uses all of these. We introduce them here
as clearly labeled axioms. Every downstream result that touches them is therefore `math.axiomatised`
(its CKC effective status is the minimum over its dependency closure), not `math.machine-checked`.

These declarations are faithful to the standard theory; replacing them with a real Mathlib
development is the (multi-year) way to discharge them.
-/

namespace MeasureToMeasure.Axioms

open MeasureTheory

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

/-- AXIOM (Kantorovich-Rubinstein duality, the `W_1` form used for the Markov bound, Claim 2):
`W_1(μ, ν)` equals the supremum over `1`-Lipschitz test functions of `∫ f dμ - ∫ f dν`. We expose the
one direction the paper uses, that any `1`-Lipschitz `f` lower-bounds `W_1`. -/
axiom W1 (μ ν : Measure (Eucl d)) : ℝ

axiom W1_ge_of_lipschitz (μ ν : Measure (Eucl d)) (f : Eucl d → ℝ)
    (hf : LipschitzWith 1 f) : ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ W1 μ ν

end MeasureToMeasure.Axioms
