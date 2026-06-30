import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.ContinuityEquation

/-!
# Blueprint statements: the main results (Theorems 1.1 and 1.2) and disentanglement (Prop 3.1)

These are the headline targets of the paper, stated type-correctly in Lean against the labeled
axiom layer (`W2`, `measureFlow`). They are currently `sorry` stubs: their status is `math.open`.
Each one's full proof is the disentangle / cluster / match construction, whose self-contained pieces
are the kernel-checked leaves L1-L10 and whose analytic scaffolding is the axiom layer.

The hypotheses of the paper (a shared missing direction off all supports, eq. 1.4-1.5; pairwise
matchability by a transport map; pairwise disjoint supports) are recorded as named opaque predicates
so the statements stay faithful without re-deriving the (absent) Mathlib support / optimal-transport
API. The switch-complexity refinements (`O(d N)` switches, norm bounds) are documented in the
blueprint prose; here we state the controllability conclusion that is the mathematical core.
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms

variable {d : ℕ}

/-- There is a direction off the (closed) support of every measure in the family (eq. 1.4-1.5). -/
axiom SharedMissingDirection {N : ℕ} (μ : Fin N → Measure (Eucl d)) : Prop

/-- Each input/target pair is matchable by some transport map (the minimal assumption of Thm 1.2). -/
axiom Matchable {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d)) : Prop

/-- The measures in the family have pairwise disjoint (geodesic-convex-hull) supports. -/
axiom DisjointSupports {N : ℕ} (ν : Fin N → Measure (Eucl d)) : Prop

/-- **Theorem 1.2** (general targets). If every input/target pair is matchable by a transport map
and the families share a missing direction, then for any horizon `T` and tolerance `ε` there is a
piecewise-constant parameter `θ` whose solution map steers each input measure to within `ε` of its
target in `W₂`. Stub (`sorry`): status `math.open`. -/
theorem theorem_1_2 (hd : 3 ≤ d) {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d))
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hmiss₀ : SharedMissingDirection μ₀) (hmiss₁ : SharedMissingDirection μ₁)
    (hmatch : Matchable μ₀ μ₁) :
    ∃ θ : Params d, ∀ i, W2 (measureFlow θ T (μ₀ i)) (μ₁ i) ≤ ε := by
  sorry

/-- **Theorem 1.1** (Dirac targets). If the targets are point masses `δ_{x i}` and the inputs share
a missing direction, then for any horizon and tolerance a single piecewise-constant `θ` steers each
input to within `ε` of its target in `W₂`. Stub (`sorry`): status `math.open`. The proof also gives
`O(d N)` switches and the stated norm bound (see the blueprint). -/
theorem theorem_1_1 (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (x : Fin N → Eucl d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) (hmiss : SharedMissingDirection μ₀) :
    ∃ θ : Params d, ∀ i, W2 (measureFlow θ T (μ₀ i)) (Measure.dirac (x i)) ≤ ε := by
  sorry

/-- **Proposition 3.1** (disentanglement). There is a piecewise-constant `θ` whose solution map
renders the supports of the family pairwise disjoint. Stub (`sorry`): status `math.open`. The proof
is the induction of Section 3.3 using Lemmas 3.2-3.4; the barycenter dynamics are the kernel-checked
leaf L6. -/
theorem prop_3_1 (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (T : ℝ) (hT : 0 < T) :
    ∃ θ : Params d, DisjointSupports (fun i => measureFlow θ T (μ₀ i)) := by
  sorry

end MeasureToMeasure.Statements
