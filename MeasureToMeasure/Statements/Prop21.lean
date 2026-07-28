import MeasureToMeasure.Leaves.HemisphereCollapse

/-!
# Proposition 2.1, discharged: hemisphere clustering to a Dirac

`prop_2_1` (formerly an axiom in `Statements/MidLevel.lean`) is here a kernel-clean `theorem`,
with the axiom's signature verbatim. It lives in its own file, not in `MidLevel`, per the
`Lemma34Part1.lean` precedent: the proof consumes the `Leaves/HemisphereCollapse.lean` machinery,
which `MidLevel` must not import (the leaf layer already imports the statement vocabulary).

The witness is `θ := [p]` with `p` the single amplitude-scaled gated block of
`Leaves.exists_collapse_block_hemisphere_W2` and `z := e` the hemisphere's own pole: one constant
piece (`switches = 1 ≤ 1`), duration exactly `T` (`durationSum [p] = p.duration = T`), target on
the sphere. The `NeZero d` instance the engine needs is derived, not assumed: `d = 0` contradicts
`‖e‖ = 1` because `Eucl 0` has only the zero vector. The public statement is therefore byte-for-byte
the former axiom, with no added hypothesis.
-/

set_option autoImplicit false

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **Proposition 2.1** (clustering to a point). A sphere-supported probability measure in an open
hemisphere can be driven arbitrarily `W₂`-close to a Dirac mass at some point `z` of the sphere,
with a single constant parameter (one switch). DISCHARGED (`math.machine-checked`): the witness is
the single amplitude-scaled gated pull block of `Leaves.exists_collapse_block_hemisphere_W2`
(`pParkScaled A e e (-1) T`, a `V = 0` gated perceptron piece whose amplitude `A` absorbs the reach
budget at horizon exactly `T`), collapsing the hemisphere onto its own pole `z := e`. No LaSalle
invariance principle or linearization is needed, so the axiom's earlier appeal to that machinery
was too pessimistic (the `lemma_5_1` precedent); the elementary route is: mass split below an inner
level `m` (continuity of measure, the only consumer of the OPEN hemisphere hypothesis), gated pull
of the sub-cap above the cap level `b`, chordal-ball conversion, and the `W₂`-vs-ball-mass bound.

**Honest witness note:** the paper's own construction (Prop 2.1, p.11, arXiv:2411.04551v3) is the
attention flow `(V, B, W) ≡ (I_d, B, 0)` with the geodesic-hull nesting argument; the
machine-checked witness realizes the same conclusion (same budget, same horizon, same target class)
with a `V = 0` gated perceptron block instead. The paper's printed proof also has a real gap for
hulls with empty interior, where its nesting chain `conv_g supp μ(t₂) ⊂ int conv_g supp μ(t₁)` is
vacuous, and the fix (footnote 7's dimension reduction) appears only in Appendix B, not in the
Section 2.1 proof (finding F29 in `RESEARCH.md`).

**Fidelity (soundness):** the sphere support and the on-sphere location of `z` are the paper's
(`μ₀ ∈ P(S^{d-1})`, the cluster point is a limit of sphere points); without sphere support the
`W₂ ≤ ε` conclusion held only through the `⊤.toReal = 0` collapse for infinite-cost pairs. The
one-piece budget is the paper's parameter choice (one constant piece; `switches` counts constant
pieces). Stated on the mean-field layer (F14): the clustering IS the self-attention dynamics, so
the linear model cannot host the paper's statement faithfully, even though the witness block
happens to be measure-independent. -/
theorem prop_2_1 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (e : Eucl d) (he : ‖e‖ = 1)
    (hμs : supportedIn μ (sphere d)) (hhemi : supportedIn μ {x | 0 < ⟪e, x⟫}) :
    ∃ (θ : AttnSchedule d) (z : Eucl d), AttnSchedule.durationSum θ = T ∧
      AttnSchedule.switches θ ≤ 1 ∧ z ∈ sphere d ∧
      Axioms.W2 (attnMeasureFlow θ μ) (Measure.dirac z) ≤ ε := by
  haveI : NeZero d := ⟨by
    intro hd
    subst hd
    have h0 : e = 0 := by ext i; exact i.elim0
    rw [h0, norm_zero] at he
    exact zero_ne_one he⟩
  obtain ⟨p, hdur, hW2⟩ :=
    Leaves.exists_collapse_block_hemisphere_W2 he hT hε μ hμs hhemi
  refine ⟨[p], e, ?_, ?_, ?_, hW2⟩
  · simpa [Foundations.AttnSchedule.durationSum] using hdur
  · simp [Foundations.AttnSchedule.switches]
  · rw [sphere, Metric.mem_sphere, dist_zero_right, he]

end MeasureToMeasure.Statements
