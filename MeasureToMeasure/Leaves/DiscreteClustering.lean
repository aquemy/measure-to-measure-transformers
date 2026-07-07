import MeasureToMeasure.Axioms.Dynamics
import MeasureToMeasure.Axioms.Wasserstein

/-!
# Discrete-clustering assembly core (linear layer)

The machine-checked **combination step** of Proposition 2.2. On the linear layer the solution flow
distributes over a weighted mixture (`measureFlow_sum_smul`, the flow is a pushforward), so if ONE
schedule `θ` drives every piece `P k` of a convex decomposition `W₂`-near its prescribed on-sphere
Dirac `δ_{x k}`, the whole mixture `∑ αₖ • Pₖ` lands `W₂`-near the discrete target `∑ αₖ • δ_{x k}`
(`W2_convexCombo_le`, mixture-convexity of `W₂`).

This isolates the *provable* assembly glue of `prop_2_2` from the genuinely hard construction it is
missing: the existence of a SINGLE gated schedule that transports each disjoint piece into a small
ball around its target while parking the others — the paper's §2.2 gated-perceptron mass sweep, whose
per-piece step is `lemma_B_1`/`lemma_B_2` but whose *simultaneous, prescribed-weight, geometrically
localized* orchestration Mathlib `v4.31.0` has no continuity-equation theory to express. That
construction stays open; this leaf is the interface a future discharge plugs into (supply the shared
`θ` and the per-piece `W₂` bounds, obtain the mixture bound).

Contrast with `exists_parked_schedule`: that family-form parking lives on the mean-field layer, where
a mixture does NOT evolve as the mixture of its pieces' flows (finding F14). Here, on the linear
layer, distributivity is a genuine identity — which is exactly why `prop_2_2`'s paper construction
is placed on the linear layer.
-/

open MeasureTheory MeasureToMeasure.Axioms
open scoped ENNReal

namespace MeasureToMeasure.Leaves

variable {d : ℕ}

/-- **Discrete-clustering assembly (linear layer).** If a single schedule `θ` drives every piece
`P k` of a convex decomposition `W₂`-within `ε` of the Dirac at `x k` (with each transported piece at
finite `W₂` cost), then that same `θ` drives the mixture `∑ αₖ • Pₖ` `W₂`-within `ε` of the discrete
measure `∑ αₖ • δ_{x k}`. Pure consequence of the linear flow's distributivity
(`measureFlow_sum_smul`) and mixture-convexity of `W₂` (`W2_convexCombo_le`); the schedule, the
switch budget, and the per-piece transport are supplied by the caller. `_hP` is retained for
statement fidelity to the paper's probability-mixture setting, even though neither consequence needs
it (both are unconditional pushforward/gluing facts). -/
theorem measureFlow_W2_discrete_of_perPiece {M : ℕ} (θ : Params d) (T : ℝ)
    (P : Fin M → Measure (Eucl d)) (_hP : ∀ k, IsProbabilityMeasure (P k))
    (α : Fin M → ℝ≥0∞) (hα : ∑ k, α k = 1)
    (x : Fin M → Eucl d) {ε : ℝ} (hε : 0 ≤ ε)
    (hfin : ∀ k, MeasureToMeasure.W2 (measureFlow θ T (P k)) (Measure.dirac (x k)) ≠ ⊤)
    (hpiece : ∀ k, Axioms.W2 (measureFlow θ T (P k)) (Measure.dirac (x k)) ≤ ε) :
    Axioms.W2 (measureFlow θ T (∑ k, α k • P k))
        (∑ k, α k • Measure.dirac (x k)) ≤ ε := by
  rw [measureFlow_sum_smul]
  exact Axioms.W2_convexCombo_le α (fun k => measureFlow θ T (P k)) (fun k => Measure.dirac (x k))
    hα ε hε hfin hpiece

end MeasureToMeasure.Leaves
