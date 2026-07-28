import MeasureToMeasure.Leaves.ThreePullCluster

/-!
# Clustering to a prescribed point, discharged: the three-pull chain

`cluster_to_point` (formerly an axiom in `Statements/MidLevel.lean`) is here a kernel-clean
`theorem`, with the axiom's signature verbatim. It lives in its own file, not in `MidLevel`, per
the `Prop21.lean` / `Lemma34Part1.lean` precedent: the proof consumes the
`Leaves/ThreePullCluster.lean` machinery, which `MidLevel` must not import (the leaf layer already
imports the statement vocabulary).

The witness is the three-pull chain of `Leaves.exists_three_pull_cluster_to_target`: pull the
hemisphere's mass towards its pole `e`, relay it towards a unit vector `α` orthogonal to BOTH `e`
and the target `z` (the only consumer of `3 ≤ d`; the relay handles `z = e` and `z = -e`
uniformly), then pull towards `z`. Exactly three constant pieces of duration `T/3` each, so
`durationSum = T` on the nose and `switches = 3 ≤ 7` sharpens the axiom's budget. The public
statement is therefore byte-for-byte the former axiom, with no added hypothesis.
-/

set_option autoImplicit false

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **Clustering to a prescribed point** (Proposition 2.1 followed by Proposition 4.1). A
sphere-supported probability measure in an open hemisphere can be driven `W₂`-close to the Dirac
mass at *any chosen* point `z` of the sphere, within the paper's `1 + 6` piece budget.
DISCHARGED (`math.machine-checked`): the witness is the three-pull chain of
`Leaves.exists_three_pull_cluster_to_target` -- pull towards the hemisphere pole `e`, relay
towards a unit `α` orthogonal to both `e` and `z`, then pull towards `z` -- three `V = 0` gated
perceptron pieces of duration `T/3` each, `switches = 3 ≤ 7`. The `ε²/8` off-cap budget is handed
off along the chain, not accumulated: the tight `7/8`-cap of each pull clears the next pull's
`-(1/2)` entry level around any orthogonal pole (`inner_orthogonal_ge_of_mem_cap`).

**Honest witness note:** the paper's own construction (Prop 2.1 + Prop 4.1, §5.2, p.29,
arXiv:2411.04551v3) is a genuine attention piece (`(V, B, W) ≡ (I_d, B, 0)`) clustering the
hemisphere to a point, followed by six perceptron switches steering that point to `z`, `1 + 6`
pieces. The machine-checked witness realizes the same conclusion (same budget as an upper bound,
same horizon, same target class) with three `V = 0` gated pulls instead; this is faithful because
the axiom's `switches ≤ 7` was always an upper bound, and it is a stronger realization, not a
narrowing (the `prop_2_1` precedent, finding F29). `3 ≤ d` is genuinely consumed: the relay pole
`α` must be orthogonal to both `e` and `z` at once (`exists_unit_orthogonal_two`), which is
exactly a doubly-orthogonal direction.

**Fidelity (soundness):** the sphere support, `d ≥ 3` (the paper inherits it from Proposition
4.1's steering; the witness spends it on the relay pole), the on-sphere target (restored by
finding F12: the flow keeps sphere mass on the sphere, so an off-sphere `z` is kernel-refuted),
and the `1 + 6` switch budget are the paper's. Stated on the mean-field layer (F14): the paper's
clustering half is the self-attention dynamics, so the linear model cannot host the statement
faithfully, even though the witness blocks happen to be measure-independent. -/
theorem cluster_to_point (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (hd : 3 ≤ d) (T ε : ℝ)
    (hT : 0 < T) (hε : 0 < ε)
    (z e : Eucl d) (hz : z ∈ sphere d) (he : ‖e‖ = 1)
    (hμs : supportedIn μ (sphere d)) (hhemi : supportedIn μ {x | 0 < ⟪e, x⟫}) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧ AttnSchedule.switches θ ≤ 7 ∧
      Axioms.W2 (attnMeasureFlow θ μ) (Measure.dirac z) ≤ ε := by
  obtain ⟨θ, hdur, hlen, hW2⟩ :=
    Leaves.exists_three_pull_cluster_to_target μ hd T ε hT hε z e hz he hμs hhemi
  refine ⟨θ, hdur, ?_, hW2⟩
  show θ.length ≤ 7
  rw [hlen]
  norm_num

end MeasureToMeasure.Statements
