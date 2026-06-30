import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.ContinuityEquation
import MeasureToMeasure.Leaves.BarycenterNonColinear

/-!
# Mid-level statements: the connective lemmas of Sections 2-5 and Appendix B

The kernel-checked leaves (L1-L11) capture the self-contained computational cores, and
`Statements/MainResults.lean` states the three headline theorems. This file fills the gap: it states,
**type-correctly in Lean**, the mid-level lemmas the paper chains together — Propositions 2.1, 2.2,
4.1, 4.2; Lemmas 3.2, 3.3, 3.4; Lemmas 5.1, 5.4; Lemmas B.1, B.2. Together with the leaves and the
headlines this puts 100% of the paper's statements into Lean.

All are `sorry` stubs: their status is `math.open`. They are stated against the existing axiom layer
(`measureFlow`, `flowMap`, `switches`, `W2`) and add **no new axioms**: "the support of `μ` lies in
`S`" is expressed measure-theoretically as `μ Sᶜ = 0`, and the barycenter `ℰ_μ[x]` is the genuine
Bochner integral `∫ x ∂μ`. Each proof is the construction reviewed in `RESEARCH.md` and rests, when
discharged, on the optimal-transport / continuity-equation / geodesic-convexity axioms — so the
effective status of anything built on them is `math.axiomatised` at best, honestly.
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Leaves (barycenter)
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- The open positive orthant `Q₁^{d-1} = 𝕊^{d-1} ∩ (ℝ_{>0})^d`, as a subset of `ℝ^d`. -/
def orthant (d : ℕ) : Set (Eucl d) := {x | ∀ i, 0 < x i}

/-- "The support of `μ` is contained in `S`", expressed measure-theoretically as `μ(Sᶜ) = 0` (no mass
outside `S`). Avoids the (absent) packaged measure-support API while staying faithful. The barycenter
`ℰ_μ[x] = ∫ x dμ` is reused from the L11 leaf (`MeasureToMeasure.Leaves.barycenter`). -/
def supportedIn (μ : Measure (Eucl d)) (S : Set (Eucl d)) : Prop := μ Sᶜ = 0

/-- **Proposition 2.1** (clustering to a point). A measure supported in an open hemisphere can be
driven arbitrarily `W₂`-close to a Dirac mass. Stub (`sorry`): `math.open`. The rate
`O(log 1/ε)` and the LaSalle/Hartman-Grobman convergence are in the axiom layer. -/
theorem prop_2_1 (μ : Measure (Eucl d)) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (e : Eucl d) (he : ‖e‖ = 1) (hhemi : supportedIn μ {x | 0 < ⟪e, x⟫}) :
    ∃ (θ : Params d) (z : Eucl d), W2 (measureFlow θ T μ) (Measure.dirac z) ≤ ε := by
  sorry

/-- **Proposition 2.2** (clustering to a discrete measure). An atomless measure whose support lies in
a region `S` disjoint from the others can be driven `W₂`-close to a prescribed `M`-atom empirical
measure. Stub (`sorry`): `math.open`. -/
theorem prop_2_2 (μ ν_target : Measure (Eucl d)) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hatomless : ∀ x : Eucl d, μ {x} = 0)
    (M : ℕ) (x : Fin M → Eucl d) (α : Fin M → ℝ≥0∞)
    (htgt : ν_target = ∑ k : Fin M, α k • Measure.dirac (x k)) :
    ∃ θ : Params d, W2 (measureFlow θ T μ) ν_target ≤ ε := by
  sorry

/-- **Lemma 3.2** (transport into the orthant). One parameter switch moves the measure into
`Q₁^{d-1}`. Stub (`sorry`): `math.open`. -/
theorem lemma_3_2 (μ : Measure (Eucl d)) (T : ℝ) (hT : 0 < T) :
    ∃ θ : Params d, switches θ ≤ 1 ∧ supportedIn (measureFlow θ T μ) (orthant d) := by
  sorry

/-- **Lemma 3.3** (shrink a measure's hull toward its barycenter direction). For any tolerance the
measure can be concentrated into a small ball around some direction `α`, with `O(dN)` switches.
Stub (`sorry`): `math.open`. -/
theorem lemma_3_3 (μ : Measure (Eucl d)) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∃ (θ : Params d) (α : Eucl d), supportedIn (measureFlow θ T μ) (Metric.ball α ε) := by
  sorry

/-- **Lemma 3.4, Part 1** (`γ₁ = 1` case). If two measures have equal barycenters, a constant
parameter makes the barycenters differ. Stub (`sorry`): `math.open`. The self-contained pigeonhole
core is leaf L10. -/
theorem lemma_3_4_part1 (μ ν : Measure (Eucl d)) (T : ℝ) (hT : 0 < T)
    (hbar : barycenter μ = barycenter ν) :
    ∃ θ : Params d, barycenter (measureFlow θ T μ) ≠ barycenter (measureFlow θ T ν) := by
  sorry

/-- **Lemma 3.4, Part 2** (`γ₁ ≠ 1` case). At most two switches make the barycenters non-colinear
(not `SameRay`). Stub (`sorry`): `math.open`. The "disjoint hulls ⟹ non-colinear barycenters"
implication used alongside this is the machine-checked leaf L11. -/
theorem lemma_3_4_part2 (μ ν : Measure (Eucl d)) (T : ℝ) (hT : 0 < T) :
    ∃ θ : Params d, switches θ ≤ 2 ∧
      ¬ SameRay ℝ (barycenter (measureFlow θ T μ)) (barycenter (measureFlow θ T ν)) := by
  sorry

/-- **Proposition 4.2** (steer one active point). With `d ≥ 3` and the inactive points already at
their targets, at most `6` switches move every input to its target, keeping the inactive ones fixed
(`x₀ i = y i` is preserved by `flowMap θ T (x₀ i) = y i`). Stub (`sorry`): `math.open`. Step 1 is
leaf L3, the geodesic gradient is leaf L4. -/
theorem prop_4_2 (hd : 3 ≤ d) (M : ℕ) (x₀ y : Fin M → Eucl d) (T : ℝ) (hT : 0 < T)
    (hfix : ∀ i : Fin M, (i : ℕ) < M - 1 → x₀ i = y i) :
    ∃ θ : Params d, switches θ ≤ 6 ∧ ∀ i, flowMap θ T (x₀ i) = y i := by
  sorry

/-- **Proposition 4.1** (match an ensemble). With `d ≥ 3` and distinct inputs/targets, at most `6M`
switches steer every `x₀ i` to `y i`. Stub (`sorry`): `math.open`. Follows from Proposition 4.2 by
induction. -/
theorem prop_4_1 (hd : 3 ≤ d) (M : ℕ) (x₀ y : Fin M → Eucl d) (T : ℝ) (hT : 0 < T)
    (hx₀ : Function.Injective x₀) (hy : Function.Injective y) :
    ∃ θ : Params d, switches θ ≤ 6 * M ∧ ∀ i, flowMap θ T (x₀ i) = y i := by
  sorry

/-- **Lemma 5.1** (transport map after disentanglement). If each disentangled pair is matchable, a
single bijective map matches them all. Stub (`sorry`): `math.open`. -/
theorem lemma_5_1 {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d))
    (hmatch : ∀ i, ∃ Ti : Eucl d → Eucl d, (μ₀ i).map Ti = μ₁ i) :
    ∃ ψ : Eucl d → Eucl d, Function.Bijective ψ ∧ ∀ i, (μ₀ i).map ψ = μ₁ i := by
  sorry

/-- **Lemma 5.4** (`L²` approximation by a flow map). Any transport map `ψ` is approximated in
`L²(μ)` by a flow map of the dynamics, to any tolerance, with finitely many switches. Stub
(`sorry`): `math.open`. Combined with the coupling bound (leaf L7) this controls `W₂`. -/
theorem lemma_5_4 (μ : Measure (Eucl d)) (ψ : Eucl d → Eucl d) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∃ (θ : Params d) (ψε : Eucl d → Eucl d),
      measureFlow θ T μ = μ.map ψε ∧ Real.sqrt (∫ x, ‖ψ x - ψε x‖ ^ 2 ∂μ) ≤ ε := by
  sorry

/-- **Lemma B.1** (ball-chain retention). For a chain of `K+1` overlapping balls, `K` switches retain
`(1-ε)^K` of the mass into the last ball. Stub (`sorry`): `math.open`. The arithmetic core is leaf
L9; the geometric non-interference is the parking axiom. -/
theorem lemma_B_1 (μ : Measure (Eucl d)) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (K : ℕ) (B : ℕ → Set (Eucl d)) :
    ∃ θ : Params d, switches θ ≤ K ∧
      (1 - ENNReal.ofReal ε) ^ K * μ (⋃ k, B k) ≤ (measureFlow θ T μ) (B K) := by
  sorry

/-- **Lemma B.2** (single ball pair). Mass in `B₀` is pushed into `B₀ ∩ B₁`, retaining `(1-ε)`. Stub
(`sorry`): `math.open`. (Review finding F1: the paper's printed gate parameters have the activation
side reversed; the corrected sign is `U = +z 1ᵀ, b = -cos(R) 1`. See `ERRATA.md`.) -/
theorem lemma_B_2 (μ : Measure (Eucl d)) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (B₀ B₁ : Set (Eucl d)) (hcap : (B₀ ∩ B₁).Nonempty) :
    ∃ θ : Params d, (1 - ENNReal.ofReal ε) * μ B₀ ≤ (measureFlow θ T μ) (B₀ ∩ B₁) := by
  sorry

end MeasureToMeasure.Statements
