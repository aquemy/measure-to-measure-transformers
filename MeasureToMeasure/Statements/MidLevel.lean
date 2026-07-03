import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.ContinuityEquation
import MeasureToMeasure.Axioms.Dynamics
import MeasureToMeasure.Leaves.BarycenterNonColinear
import MeasureToMeasure.Foundations.AtomlessSplitting
import MeasureToMeasure.Foundations.GeodesicDistance
import MeasureToMeasure.Foundations.Attention

/-!
# Mid-level statements: the connective lemmas of Sections 2-5 and Appendix B

The kernel-checked leaves (L1-L11) capture the self-contained computational cores, and
`Statements/MainResults.lean` states the three headline theorems. This file fills the gap: the
mid-level lemmas the paper chains together (Propositions 2.1, 2.2, 4.1, 4.2; Lemmas 3.2, 3.3, 3.4;
Lemmas 5.1, 5.4; Lemmas B.1, B.2).

## Status policy (closing the open statements)

Each mid-level result rests on machinery Mathlib does not have (continuity-equation flow existence,
LaSalle / Hartman-Grobman, optimal transport, geodesic convexity). Those are **irreducible analytic
facts**: we state them as clearly labeled `axiom`s (status `math.axiomatised`), each citing the paper
section and the classical theorem it encodes, and each `Depends-On` the kernel-checked geometric leaf
that supplies its self-contained core.

Soundness of this posture requires each axiom's STATEMENT to be true -- something no per-node
`#print axioms` check can see. Statement fidelity is therefore enforced by its own adversarial
review: candidate stubs are attacked with kernel refutation attempts, and every dropped hypothesis
found this way is restored to the paper's form before the axiom is trusted (findings F11-F16 in
`RESEARCH.md`; earlier instances: `prop_4_2`'s injectivity, `lemma_B_1`/`lemma_B_2`'s geodesic
balls).

## The two dynamics layers (finding F14)

The paper's velocity field (1.2) is *measure-dependent* through self-attention, and eq. (1.7)
shows measure dependence is essential for the family-level results. Each statement below therefore
lives on the layer its own paper construction uses:

* **Linear layer** (`Params d` / `measureFlow`, the measure-independent characteristic flow of
  `Foundations/FlowMap.lean`): statements whose paper proofs use only perceptron parameters
  (`V ≡ 0`, so the field never reads the measure) -- `lemma_3_2` (W-only rotation),
  `lemma_3_4_part1` (V ≡ 0), `prop_4_2`/`prop_4_1` (eq. (4.1)), `lemma_B_2`/`lemma_B_1`
  (Appendix B gates), and `prop_2_2` (the Section 2.2 gated construction).
* **Mean-field layer** (`AttnSchedule d` / `attnMeasureFlow`, the self-attention flow interface of
  `Foundations/Attention.lean`): statements whose paper constructions switch on attention
  (`V ≠ 0`) -- `prop_2_1` (attention clustering), `lemma_3_3`, `lemma_3_4_part2`,
  `cluster_to_point`, `lemma_5_4`, `exists_parked_schedule`, and the disentanglement/main results
  in `MainResults.lean`.

The horizon convention on the mean-field layer: a schedule spans `[0, T]` through its pieces'
durations (`AttnSchedule.durationSum θ = T`); `AttnSchedule.switches` counts pieces, exactly like
the linear `switches`.

`lemma_B_1` is **proved** (not axiomatized): it is a genuine assembly of `lemma_B_2` and the
structural flow algebra (`Axioms/Dynamics.lean`) by induction on the length of the ball chain, so its
mass-retention bound is machine-checked given the single-ball transport fact.
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Leaves (barycenter)
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- The open positive orthant `Q₁^{d-1} = 𝕊^{d-1} ∩ (ℝ_{>0})^d`, as a subset of `ℝ^d`. -/
def orthant (d : ℕ) : Set (Eucl d) := {x | ∀ i, 0 < x i}

/-- "The support of `μ` is contained in `S`", expressed measure-theoretically as `μ(Sᶜ) = 0` (no mass
outside `S`). Avoids the (absent) packaged measure-support API while staying faithful. The barycenter
`ℰ_μ[x] = ∫ x dμ` is reused from the L11 leaf (`MeasureToMeasure.Leaves.barycenter`). -/
def supportedIn (μ : Measure (Eucl d)) (S : Set (Eucl d)) : Prop := μ Sᶜ = 0

/-- A family of measures has pairwise disjoint supports: a family of carrier sets `S i` (each holding
the full mass of `ν i`) that are pairwise disjoint. -/
def DisjointSupports {N : ℕ} (ν : Fin N → Measure (Eucl d)) : Prop :=
  ∃ S : Fin N → Set (Eucl d), (∀ i, supportedIn (ν i) (S i)) ∧
    Pairwise (fun i j => Disjoint (S i) (S j))

/-- The support misses a spherical cap: some unit direction `ω` has a positive gap `δ` with
`⟪ω, x⟫ ≤ 1 - δ` on the full mass of `μ`. This is the faithful encoding of the paper's
`supp μ ⊊ S^{d-1}` hypothesis (eq. 1.4, Lemma 3.2): a closed support avoiding `ω` leaves a
mass-free open cap around `ω`. -/
def MissingCap (μ : Measure (Eucl d)) : Prop :=
  ∃ ω : Eucl d, ‖ω‖ = 1 ∧ ∃ δ : ℝ, 0 < δ ∧ supportedIn μ {x | ⟪ω, x⟫ ≤ 1 - δ}

/-- **Proposition 2.1** (clustering to a point). A sphere-supported probability measure in an open
hemisphere can be driven arbitrarily `W₂`-close to a Dirac mass at some point `z` of the sphere,
with a single constant parameter (one switch). AXIOM (`math.axiomatised`): the convergence rests on
the LaSalle invariance principle and Hartman-Grobman linearization for the attention flow
(Section 2.1), which Mathlib lacks. `Depends-On` the barycenter ODE leaf L6.

**Fidelity (soundness):** the sphere support and the on-sphere location of `z` are the paper's
(`μ₀ ∈ P(S^{d-1})`, the cluster point is a limit of sphere points); without sphere support the
`W₂ ≤ ε` conclusion held only through the `⊤.toReal = 0` collapse for infinite-cost pairs. The
one-piece budget is the paper's parameter choice `(V, B, W) ≡ (I_d, B, 0)` -- attention-only,
one constant piece (`switches` counts constant pieces). Stated on the mean-field layer (F14): the
clustering IS the self-attention dynamics, so the linear model cannot host it faithfully. -/
axiom prop_2_1 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (e : Eucl d) (he : ‖e‖ = 1)
    (hμs : supportedIn μ (sphere d)) (hhemi : supportedIn μ {x | 0 < ⟪e, x⟫}) :
    ∃ (θ : AttnSchedule d) (z : Eucl d), AttnSchedule.durationSum θ = T ∧
      AttnSchedule.switches θ ≤ 1 ∧ z ∈ sphere d ∧
      Axioms.W2 (attnMeasureFlow θ μ) (Measure.dirac z) ≤ ε

/-- **Lemma 3.2** (transport into the orthant). Two constant parameter pieces move a
sphere-supported probability measure whose support misses a cap into `Q₁^{d-1}`. AXIOM
(`math.axiomatised`): realizes a separating-hyperplane rotation as a flow; rests on
continuity-equation flow existence. `Depends-On` the separating-hyperplane leaf L3.

**Fidelity (soundness):** the paper's hypotheses (Lemma 3.2, p.15) are `μ₀^i ∈ P(S^{d-1})` with
`⋃_i supp μ₀^i ⊊ S^{d-1}`; the missing direction `ω` is where the rotation field `-P_x^⊥ ω` pushes
mass away from. The original stub quantified over EVERY measure and was kernel-refuted with the
Lebesgue measure: `flowMap` is a Lipschitz bijection of `Eucl d`, so the pushforward of an
open-positive infinite measure cannot be annihilated off the orthant (review finding F12). The
missing-cap gap is what `MissingCap` encodes.

Budget convention: Lean's `switches` counts constant PIECES of the schedule; the paper's "at most
one switch" counts discontinuities. The paper's proof runs two constant phases (`W ≡ W₁` pushing
off `-ω`, then `W ≡ W₂` pulling toward `α`), hence `switches θ ≤ 2` here.

Layer (F14): stays on the LINEAR layer faithfully -- the paper's construction sets
`V ≡ B ≡ U ≡ 0, b = 1` (p.15), so the field `P_x^⊥ (W 1)` never reads the measure. -/
axiom lemma_3_2 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 < T)
    (hμs : supportedIn μ (sphere d)) (hgap : MissingCap μ) :
    ∃ θ : Params d, switches θ ≤ 2 ∧ supportedIn (measureFlow θ T μ) (orthant d)

/-- **Lemma 3.3** (shrink a measure's hull toward its barycenter direction). For any tolerance a
sphere-supported probability measure on the orthant can be concentrated into a small ball around
some unit direction `α`. AXIOM (`math.axiomatised`): the contraction is driven by the barycenter
dynamics (leaf L6) but its realization as a flow on measures rests on the missing
continuity-equation theory.

**Fidelity (soundness):** this is the single-measure core of the paper's Lemma 3.3 (p.16), whose
family form concentrates one measure while FIXING the others and carries an `O(d·N)` switch budget
with a non-explicit constant (deferred to the mean-field restatement, F14). The paper works over
`P(Q₁^{d-1})`, hence the probability, sphere, and orthant hypotheses. The original stub quantified
over EVERY measure and was kernel-refuted with the Lebesgue measure (no bijection supports an
open-positive infinite measure inside a bounded ball; review finding F12); on-sphere full-support
measures are equally impossible (a homeomorphism preserves the support's density).

Layer (F14): mean-field -- the paper's construction (B.2, p.33) switches on the value matrix
(`V(t) = ∑ α_k α_k^⊤` pieces with `W ≡ 0`), so the field reads the flowing measure's barycenter. -/
axiom lemma_3_3 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hμs : supportedIn μ (sphere d)) (hμo : supportedIn μ (orthant d)) :
    ∃ (θ : AttnSchedule d) (α : Eucl d), AttnSchedule.durationSum θ = T ∧ α ∈ sphere d ∧
      supportedIn (attnMeasureFlow θ μ) (Metric.ball α ε)

/-- **Lemma 3.4, Part 1** (`γ₁ = 1` case). For two **distinct** probability measures on the orthant
`Q₁^{d-1}` with **equal** barycenters, a constant parameter (`V ≡ 0`) makes the barycenters differ.
AXIOM (`math.axiomatised`). The self-contained pigeonhole core (non-constancy over an open ball) is the
kernel-checked leaf L10 (`exists_ne_in_ball`).

**Fidelity (soundness):** the hypotheses `μ ≠ ν`, `IsProbabilityMeasure`, and support in the orthant
are the paper's ("let `μ₀, ν₀ ∈ P(Q₁^{d-1})` be two *different* measures", Lemma 3.4). The original
stub omitted all of them, which makes the statement **false**: taking `μ = ν` satisfies the equal-
barycenter hypothesis yet no `θ` can separate the (identical) flowed barycenters. The sphere support
is also the paper's (`Q₁^{d-1} = S^{d-1} ∩ (ℝ_{>0})^d`, while `orthant d` is only the ambient
orthant): without it the statement remained refutable by heavy-tailed orthant measures whose
identity map is not Bochner-integrable, so both barycenters are the junk value `0` and no flow can
separate them (review finding F12). On the sphere the identity is bounded, hence integrable, and
the orthant support makes the barycenter genuinely nonzero.

Layer (F14): stays on the LINEAR layer faithfully -- the paper's part-1 construction sets `V ≡ 0`
(perceptron only, §B.3), so the field never reads the measure. -/
axiom lemma_3_4_part1 (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (hbar : barycenter μ = barycenter ν) :
    ∃ θ : Params d, barycenter (measureFlow θ T μ) ≠ barycenter (measureFlow θ T ν)

/-- **Lemma 3.4, Part 2** (`γ₁ ∈ (0,1)` case). For two **distinct** probability measures on the orthant
whose barycenters are **colinear but unequal** (`ℰ_μ = γ·ℰ_ν` for some `γ ∈ (0,1)`), at most two
switches make the barycenters non-colinear (not `SameRay`). AXIOM (`math.axiomatised`). The "disjoint
geodesic hulls ⟹ non-colinear barycenters" implication used alongside this is the machine-checked leaf
L11 (`barycenter_noncolinear_of_disjoint_hull`, review finding F2).

**Fidelity (soundness):** the hypotheses are the paper's (`μ₀, ν₀ ∈ P(Q₁^{d-1})` different, with
`ℰ_{μ₀} = γ₁ ℰ_{ν₀}`, `γ₁ ∈ (0,1)`). The original stub omitted **every** hypothesis, which makes the
statement **false**: with no relation between `μ` and `ν`, taking `μ = ν` gives coincident flowed
barycenters, and `SameRay ℝ v v` always holds, so `¬ SameRay …` is unsatisfiable for every `θ`. The
sphere support is likewise required (F12): heavy-tailed orthant measures have junk-zero Bochner
barycenters, `0 = γ • 0` satisfies the colinearity, and `SameRay ℝ 0 0` always holds. On the sphere
the barycenters are genuine and the orthant support forces them nonzero, so the initial
`γ ∈ (0,1)` colinearity has content.

Layer (F14): mean-field -- the paper's part-2 construction (§B.3) switches on the value matrix
(`B ≡ 0` but `V ≠ 0`), so the field reads the flowing measures' barycenters. The conclusion pairs
the two flows of the SAME schedule applied to the two measures (two separate mean-field systems
sharing the parameters, as in the paper). -/
axiom lemma_3_4_part2 (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ barycenter μ = γ • barycenter ν) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧ AttnSchedule.switches θ ≤ 2 ∧
      ¬ SameRay ℝ (barycenter (attnMeasureFlow θ μ)) (barycenter (attnMeasureFlow θ ν))

/-- **Proposition 4.2** (steer one active point). With `d ≥ 3`, distinct inputs/targets, and the
inactive points (the first `M-1`) already at their targets, at most `6` switches move every input to
its target, keeping the inactive ones fixed. AXIOM (`math.axiomatised`): the gather/corridor/restore
construction is a geodesic gradient flow. Step 1 is leaf L3, the geodesic gradient is leaf L4.

The injectivity hypotheses are required for soundness: the flow map is bijective
(`flowMap_bijective`), so steering `x₀ (M-1)` to `y (M-1)` while fixing the inactive points is
possible only if the targets (and inputs) are distinct -- otherwise the map would need two preimages
for one point. The original stub omitted them.

**Fidelity (soundness):** the sphere memberships are the paper's (Proposition 4.2 steers points of
`S^{d-1}`). Without them the axiom contradicts the kernel-checked `flowMap_mem_sphere`: it would
steer `e₁` (on the sphere) to `2 • e₁` (off it), an in-system proof of `False` (review finding
F12). -/
axiom prop_4_2 (hd : 3 ≤ d) (M : ℕ) (x₀ y : Fin M → Eucl d) (T : ℝ) (hT : 0 < T)
    (hx₀s : ∀ i, x₀ i ∈ sphere d) (hys : ∀ i, y i ∈ sphere d)
    (hx₀ : Function.Injective x₀) (hy : Function.Injective y)
    (hfix : ∀ i : Fin M, (i : ℕ) < M - 1 → x₀ i = y i) :
    ∃ θ : Params d, switches θ ≤ 6 ∧ ∀ i, flowMap θ T (x₀ i) = y i

/-- **Proposition 4.1** (match an ensemble). With `d ≥ 3` and distinct inputs/targets, at most `6M`
switches steer every `x₀ i` to `y i`.

**Proved** (effective `math.axiomatised`) by induction on `M` over Proposition 4.2 and the structural
flow algebra. Base case `M = 0`: the identity schedule (`idParams`, `0` switches). Step `M = k+1`:
place the first `k` points by the induction hypothesis on the subfamily `x₀ ∘ castSucc`,
`y ∘ castSucc` (`≤ 6k` switches), giving a schedule `φ`; then one Proposition 4.2 step moves the last
point to `y (last)` while the first `k` -- now at their targets via `φ`, so the `hfix` hypothesis
holds -- stay fixed (`≤ 6` switches); compose with `comp`. The switch budget is `6k + 6 = 6(k+1)`
(`switches_comp`), and `flowMap_comp` gives the conclusion for every index at once. The injectivity
needed for the Proposition 4.2 step is exactly `flowMap φ T ∘ x₀` injective (bijective flow composed
with injective `x₀`) and `y` injective. `Depends-On prop_4_2`. -/
theorem prop_4_1 (hd : 3 ≤ d) (M : ℕ) (x₀ y : Fin M → Eucl d) (T : ℝ) (hT : 0 < T)
    (hx₀s : ∀ i, x₀ i ∈ sphere d) (hys : ∀ i, y i ∈ sphere d)
    (hx₀ : Function.Injective x₀) (hy : Function.Injective y) :
    ∃ θ : Params d, switches θ ≤ 6 * M ∧ ∀ i, flowMap θ T (x₀ i) = y i := by
  induction M with
  | zero => exact ⟨idParams d, by simp [switches_id], fun i => i.elim0⟩
  | succ k ih =>
    -- Place the first k points by the induction hypothesis on the castSucc subfamily.
    have hx₀' : Function.Injective (x₀ ∘ Fin.castSucc) := hx₀.comp (Fin.castSucc_injective k)
    have hy' : Function.Injective (y ∘ Fin.castSucc) := hy.comp (Fin.castSucc_injective k)
    obtain ⟨φ, hφsw, hφ⟩ := ih (x₀ ∘ Fin.castSucc) (y ∘ Fin.castSucc)
      (fun i => hx₀s _) (fun i => hys _) hx₀' hy'
    simp only [Function.comp_apply] at hφ
    -- Current positions of all k+1 points after φ.
    set p : Fin (k + 1) → Eucl d := fun i => flowMap φ T (x₀ i) with hp
    have hpinj : Function.Injective p := (flowMap_bijective φ T).injective.comp hx₀
    -- The flow keeps every point on the sphere.
    have hps : ∀ i, p i ∈ sphere d := fun i => flowMap_mem_sphere φ hT.le (hx₀s i)
    -- The first k points already sit at their targets, so prop_4_2's hypothesis holds.
    have hfix : ∀ i : Fin (k + 1), (i : ℕ) < (k + 1) - 1 → p i = y i := by
      intro i hi
      have hlt : (i : ℕ) < k := by omega
      calc p i = flowMap φ T (x₀ (Fin.castSucc (Fin.castLT i hlt))) := by
                rw [Fin.castSucc_castLT]
        _ = y (Fin.castSucc (Fin.castLT i hlt)) := hφ (Fin.castLT i hlt)
        _ = y i := by rw [Fin.castSucc_castLT]
    obtain ⟨ψ, hψsw, hψ⟩ := prop_4_2 hd (k + 1) p y T hT hps hys hpinj hy hfix
    refine ⟨comp φ ψ, ?_, ?_⟩
    · calc switches (comp φ ψ) ≤ switches φ + switches ψ := switches_comp φ ψ
        _ ≤ 6 * k + 6 := Nat.add_le_add hφsw hψsw
        _ = 6 * (k + 1) := by ring
    · intro i
      rw [flowMap_comp]
      exact hψ i

/-- **Clustering to a prescribed point** (Proposition 2.1 followed by Proposition 4.1). A
sphere-supported measure in an open hemisphere can be driven `W₂`-close to the Dirac mass at *any
chosen* point `z` of the sphere: first cluster it to a point (Proposition 2.1, one switch), then
steer that point to `z` (Proposition 4.2 with a single active point, six switches). AXIOM
(`math.axiomatised`): a combination of the two axiomatized propositions; it is the single-measure
controllability fact that Theorem 1.1 lifts to a family by disentanglement and parking.
`Depends-On prop_2_1`, `Depends-On prop_4_1`.

**Fidelity (soundness):** the original stub let `z` range over ALL of `Eucl d` and was
kernel-refuted: the flow keeps sphere mass on the sphere, so no flowed Dirac can `W₂`-approach an
off-sphere target (`W₂(δ_p, δ_q) = dist p q`, and the distance from the sphere to `3 • e` is at
least `2`; review finding F12). The sphere support, `d ≥ 3` (inherited from Proposition 4.1's
steering), and the `1 + 6` switch budget are the paper's.

Layer (F14): mean-field -- the clustering half is the attention dynamics (Proposition 2.1); the
steering half (Proposition 4.1) is a perceptron tail, so the composite schedule lives on the
mean-field layer. -/
axiom cluster_to_point (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (hd : 3 ≤ d) (T ε : ℝ)
    (hT : 0 < T) (hε : 0 < ε)
    (z e : Eucl d) (hz : z ∈ sphere d) (he : ‖e‖ = 1)
    (hμs : supportedIn μ (sphere d)) (hhemi : supportedIn μ {x | 0 < ⟪e, x⟫}) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧ AttnSchedule.switches θ ≤ 7 ∧
      Axioms.W2 (attnMeasureFlow θ μ) (Measure.dirac z) ≤ ε

/-- **Lemma 5.1** (transport map after disentanglement). If the pairs are **disentangled** -- both the
source family `μ₀` and the target family `μ₁` have pairwise disjoint supports (this is what Proposition
3.1 achieves for `μ^i₀` and `μ^i₁` in the paper) -- and each pair is individually matchable, then a
single bijective map matches them all. AXIOM (`math.axiomatised`): gluing the per-pair transport maps
across disjoint supports rests on the optimal-transport / measurable-selection theory Mathlib lacks.

**Fidelity (soundness):** the disjoint-supports hypotheses are load-bearing and are the paper's context
(Lemma 5.1 takes the measures from Proposition 3.1 applied to both `μ^i₀` and `μ^i₁`, i.e. already
disentangled into disjoint regions). The original stub omitted them, which makes the statement
**false**: with `μ₀ 0 = μ₀ 1 = δ_a` and targets `μ₁ 0 = δ_b`, `μ₁ 1 = δ_e` (`b ≠ e`) each pair is
matchable (`a ↦ b`, `a ↦ e`) but a single `ψ` would need `ψ a = b` and `ψ a = e` at once.

The earlier conclusion additionally claimed `Function.Bijective ψ`, which is unsatisfiable even
WITH disjoint supports: within one pair an atomless source with a Dirac target is matchable, but no
injection pushes an atomless measure onto an atom (review finding F13). The paper's Lemma 5.1
(p.24) does print "invertible", but its own proof (B.4) composes `ψ^i = T^i_{Φ₃} ∘ T^i ∘
(T^i_{Φ₁})^{-1}` where the per-pair transport `T^i` need not be invertible -- a statement/proof
mismatch recorded as erratum candidate E2 in `ERRATA.md`. The faithful conclusion keeps
measurability (required for the pushforward to be meaningful) and drops invertibility. -/
axiom lemma_5_1 {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d))
    (hdisj₀ : DisjointSupports μ₀) (hdisj₁ : DisjointSupports μ₁)
    (hmatch : ∀ i, ∃ Ti : Eucl d → Eucl d, (μ₀ i).map Ti = μ₁ i) :
    ∃ ψ : Eucl d → Eucl d, Measurable ψ ∧ ∀ i, (μ₀ i).map ψ = μ₁ i

/-- **Lemma 5.4** (`L²` approximation by a flow map). Any measurable, a.e. sphere-valued transport
map `ψ` of a sphere-supported probability measure is approximated in `L²(μ)` by a flow map of the
dynamics, to any tolerance, with finitely many switches. AXIOM (`math.axiomatised`): the density of
attention-flow maps in `L²` rests on the missing continuity-equation theory. Combined with the
coupling bound (leaf L7) this controls `W₂`. The approximant `ψε` is measurable and the
displacement is `L²`-integrable -- both implicit in the `∫` bound being meaningful, made explicit
so the `W₂` map bound (`W2_map_le_L2`) can consume them.

**Fidelity (soundness):** the paper's Lemma 5.4 (p.24) has `μ ∈ P(S^{d-1})` and
`ψ ∈ L²(S^{d-1}; S^{d-1})` -- the map is sphere-valued. The original stub quantified over every
measure and every `ψ` and was refutable: flow approximants are sphere-valued on sphere mass, so
`ψ = const (3 • e₁)` on `μ = δ_{e₁}` keeps every approximant at `L²` distance at least `2`
(review finding F12). Sphere-valued `ψ` on sphere-supported `μ` is automatically `L²`.

Layer (F14): mean-field -- the paper's density argument ranges over the full attention dynamics. -/
axiom lemma_5_4 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (ψ : Eucl d → Eucl d) (T ε : ℝ)
    (hT : 0 < T) (hε : 0 < ε)
    (hμs : supportedIn μ (sphere d)) (hψm : Measurable ψ)
    (hψs : ∀ᵐ x ∂μ, ψ x ∈ sphere d) :
    ∃ (θ : AttnSchedule d) (ψε : Eucl d → Eucl d),
      AttnSchedule.durationSum θ = T ∧
      attnMeasureFlow θ μ = μ.map ψε ∧ Measurable ψε ∧
      Integrable (fun x => ‖ψ x - ψε x‖ ^ 2) μ ∧
      Real.sqrt (∫ x, ‖ψ x - ψε x‖ ^ 2 ∂μ) ≤ ε

/-- **Lemma B.2** (single ball pair). Mass in the geodesic ball `ℬ₀ = B(z₀, R₀)` is pushed into
`ℬ₀ ∩ ℬ₁` (`ℬ₁ = B(z₁, R₁)`), retaining a `(1-ε)` fraction, with a single parameter switch. AXIOM
(`math.axiomatised`): the ReLU-gated transport is the construction of Appendix B (review finding F1:
the paper's printed gate parameters have the activation side reversed; the corrected sign is
`U = +z 1ᵀ, b = -cos(R) 1`, see `ERRATA.md`). The gate algebra and the "active iff inside the ball"
fact are the kernel-checked leaf L2 (`gate_pos_iff_dist`). Note the `switches θ ≤ 1` bound, which the
original type-correct stub omitted; it is needed (and true: one switch per ball) for the chain bound
in `lemma_B_1`.

**Fidelity (soundness):** the hypotheses are now genuine **geodesic balls** `B(zᵢ, Rᵢ)` with centers
on the sphere, not arbitrary sets. The gated characteristic funnels a *cap* toward its overlap with
another cap; stated for arbitrary `B₀, B₁` the retention claim is false (nothing steers an arbitrary
set into another). This restriction matches Appendix B and is what the eventual discharge (via
`gatedBlock` + the logistic reaching estimate `logistic_flow_reach` + the cap-mass estimate
`exists_closed_sublevel_mass_ge`) will prove.

The dimension and radius bounds are likewise load-bearing (review finding F12): at `d = 1` radial
tangency forces the field to vanish at `±1`, so both sphere points are fixed and no transport
happens at all (with `R₀ > π` the ball `ℬ₀` is the whole two-point sphere and a Dirac at `1`
refutes the retention into `ℬ₁ = {-1}`). Appendix B's balls are proper caps, `R ∈ (0, π)`. -/
axiom lemma_B_2 (μ : Measure (Eucl d)) (hd : 2 ≤ d) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (z₀ z₁ : Eucl d) (hz₀ : z₀ ∈ sphere d) (hz₁ : z₁ ∈ sphere d) (R₀ R₁ : ℝ)
    (hR₀ : R₀ ∈ Set.Ioo 0 Real.pi) (hR₁ : R₁ ∈ Set.Ioo 0 Real.pi)
    (hcap : (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁).Nonempty) :
    ∃ θ : Params d, switches θ ≤ 1 ∧
      (1 - ENNReal.ofReal ε) * μ (geodesicBall z₀ R₀) ≤
        (measureFlow θ T μ) (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁)

/-- **Lemma B.1** (ball-chain retention). For a chain of `K+1` consecutively overlapping balls, `K`
switches retain a `(1-ε)^K` fraction of the mass initially in `ℬ₀` into the last ball `ℬ_K`.

**Proved** (`math.axiomatised`, the only axioms are `lemma_B_2` and the structural flow algebra): a
genuine induction on `K`. The base case is the identity schedule (`idParams`); each step composes a
single-ball `lemma_B_2` transport via `comp`, using `measureFlow_comp` to carry the previous mass
forward, `measure_mono` to pass from `ℬ_k ∩ ℬ_{k+1}` to `ℬ_{k+1}`, and `switches_comp` for the budget.

The statement keeps the retained fraction on `μ ℬ₀` (the mass that starts in the first ball,
funneled along the chain) rather than the paper's `μ (⋃ ℬ_k)`. The union form is out of reach here
NOT because of any base-case issue (at `K = 0` the paper's bounded union IS `ℬ₀`, and its base case
is true) but because the Lean `lemma_B_2` drops two clauses the paper's B.1 induction needs for the
union: the localization clause "the flow is the identity on `S^{d-1} ∖ ℬ₀`" and the
`|k - k'| ≥ 2` disjointness hypothesis, which together let mass already sitting in later balls stay
put during earlier legs (review finding F16). The chain-overlap hypothesis `hchain` and the
per-step switch bound (now in `lemma_B_2`) are required for the bound to hold. The chain is a
sequence of genuine **geodesic balls** `B(z_k, R_k)` (centers on the sphere, proper radii),
matching the faithful `lemma_B_2` signature. -/
theorem lemma_B_1 (μ : Measure (Eucl d)) (hd : 2 ≤ d) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (K : ℕ) (z : ℕ → Eucl d) (hz : ∀ k, z k ∈ sphere d) (R : ℕ → ℝ)
    (hR : ∀ k, R k ∈ Set.Ioo 0 Real.pi)
    (hchain : ∀ k, (geodesicBall (z k) (R k) ∩ geodesicBall (z (k + 1)) (R (k + 1))).Nonempty) :
    ∃ θ : Params d, switches θ ≤ K ∧
      (1 - ENNReal.ofReal ε) ^ K * μ (geodesicBall (z 0) (R 0)) ≤
        (measureFlow θ T μ) (geodesicBall (z K) (R K)) := by
  set c : ℝ≥0∞ := 1 - ENNReal.ofReal ε with hc
  induction K with
  | zero =>
    refine ⟨idParams d, ?_, ?_⟩
    · simp [switches_id]
    · simp [measureFlow_id]
  | succ k ih =>
    obtain ⟨θ, hsw, hmass⟩ := ih
    obtain ⟨ψ, hψsw, hψmass⟩ :=
      lemma_B_2 (measureFlow θ T μ) hd T ε hT hε (z k) (z (k + 1)) (hz k) (hz (k + 1))
        (R k) (R (k + 1)) (hR k) (hR (k + 1)) (hchain k)
    refine ⟨comp θ ψ, (switches_comp θ ψ).trans (Nat.add_le_add hsw hψsw), ?_⟩
    rw [measureFlow_comp]
    calc c ^ (k + 1) * μ (geodesicBall (z 0) (R 0))
        = c * (c ^ k * μ (geodesicBall (z 0) (R 0))) := by rw [pow_succ', mul_assoc]
      _ ≤ c * (measureFlow θ T μ) (geodesicBall (z k) (R k)) := by gcongr
      _ ≤ (measureFlow ψ T (measureFlow θ T μ))
            (geodesicBall (z k) (R k) ∩ geodesicBall (z (k + 1)) (R (k + 1))) := hψmass
      _ ≤ (measureFlow ψ T (measureFlow θ T μ)) (geodesicBall (z (k + 1)) (R (k + 1))) :=
          measure_mono Set.inter_subset_right

/-- AXIOM (parking / simultaneous action, Appendix B). If a family of measures has pairwise disjoint
supports and each member can be steered to within `ε` of its target by *some* schedule of at most
`s i` switches, then a *single* schedule of at most `∑ s i` switches steers all of them
simultaneously to within `ε`: each member's schedule is gated to its (disjoint) support region and
parks on the others (`flowMap_id_on_parked`). Mathlib has no continuity-equation theory to derive
this, so it is a labeled structural axiom.

**Fidelity (soundness):** the dimension hypothesis is load-bearing (review finding F12): at `d = 1`
every flow map is an increasing homeomorphism of the line, so two Dirac targets cannot be swapped,
and at `d = 2` the cyclic order of the circle gives the same obstruction; the paper's gating
construction needs room to route around parked regions, available from `d ≥ 3`. The switch budget
is the sum of the per-member budgets, matching the gate-and-concatenate construction.

Layer (F14): mean-field -- the parked family members are SEPARATE mean-field systems sharing one
schedule (each `ν i` evolves under its own self-attention field), which is exactly the paper's
family setting. Note this family form does NOT apply to pieces of a single mixture: a mixture
evolves as one system and its flow is not the mixture of its pieces' flows (that distinction is
why `prop_2_2` lives on the linear layer, where its paper construction is). -/
axiom exists_parked_schedule {N : ℕ} (hd : 3 ≤ d) (ν target : Fin N → Measure (Eucl d)) (T ε : ℝ)
    (s : Fin N → ℕ)
    (hdisj : DisjointSupports ν)
    (hper : ∀ i, ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      AttnSchedule.switches θ ≤ s i ∧
      Axioms.W2 (attnMeasureFlow θ (ν i)) (target i) ≤ ε) :
    ∃ Θ : AttnSchedule d, AttnSchedule.durationSum Θ = T ∧ AttnSchedule.switches Θ ≤ ∑ i, s i ∧
      ∀ i, Axioms.W2 (attnMeasureFlow Θ (ν i)) (target i) ≤ ε

/-- Atomless decomposition (Sierpiński/Lyapunov splitting). An atomless probability measure splits
into `M` probability measures `P k` with prescribed convex weights `α k` (`∑ α k = 1`, each `α k ≠ 0`)
and pairwise disjoint supports: `μ = ∑ α k • P k`.

**Proved** (`Foundations.exists_probability_decomposition`): the pieces are the normalized restrictions
`P k = (α k)⁻¹ • μ.restrict (A k)` to a prescribed-mass disjoint partition `A k`, which is carved by
iterating **Sierpiński's intermediate-value theorem** for nonatomic measures. The bespoke partition
axiom is thereby removed; what remains is the single primitive
`Foundations.exists_measurableSet_subset_measure_eq` (that IVT, absent from Mathlib `v4.31.0`; Fremlin,
*Measure Theory* Vol. 2, §215D). Positive weights (`α k ≠ 0`) are assumed so each normalized piece is a
genuine probability measure; a zero-weight atom is vacuous for a discrete target.

Soundness note: an earlier form additionally required each piece to sit in an open hemisphere. That
clause is inconsistent at `M = 1` -- it would force the whole measure into a half-space through the
origin, which no centrally-symmetric atomless measure (a Gaussian, or the uniform law on a ball or
sphere) satisfies -- so it is dropped here. The hemisphere is instead acquired dynamically per piece
inside `prop_2_2` (rotate into the orthant via `lemma_3_2`), the way the paper actually proceeds. -/
theorem exists_atomless_partition (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hatomless : ∀ x : Eucl d, μ {x} = 0)
    {M : ℕ} (α : Fin M → ℝ≥0∞) (hα : ∑ k, α k = 1) (hα0 : ∀ k, α k ≠ 0) :
    ∃ P : Fin M → Measure (Eucl d), (∀ k, IsProbabilityMeasure (P k)) ∧
      μ = ∑ k, α k • P k ∧ DisjointSupports P := by
  haveI : NoAtoms μ := ⟨hatomless⟩
  obtain ⟨P, S, hProb, hμeq, hsupp, hSdisj⟩ :=
    Foundations.exists_probability_decomposition μ α hα hα0
  exact ⟨P, hProb, hμeq, S, hsupp, hSdisj⟩

/-- A piece of a convex decomposition inherits the support of the whole: if `∑ αₖ • Pₖ` is supported in
`S` and every weight is nonzero, each `Pₖ` is supported in `S`. (In `ℝ≥0∞` a sum of nonnegatives
vanishes iff each term does, and `αₖ ≠ 0` cancels.) -/
theorem supportedIn_of_sum_smul {M : ℕ} (α : Fin M → ℝ≥0∞) (P : Fin M → Measure (Eucl d))
    (hα0 : ∀ k, α k ≠ 0) {S : Set (Eucl d)} (h : supportedIn (∑ k, α k • P k) S) (k : Fin M) :
    supportedIn (P k) S := by
  have hsum : ∑ j, α j * P j Sᶜ = 0 := by
    have := h
    simp only [supportedIn, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul] at this
    exact this
  have hk : α k * P k Sᶜ = 0 := (Finset.sum_eq_zero_iff.mp hsum) k (Finset.mem_univ k)
  exact (mul_eq_zero.mp hk).resolve_left (hα0 k)

/-- The solution map preserves sphere support: pushing a sphere-supported measure forward by `flowMap`
(which maps the sphere into itself for `t ≥ 0`) keeps the mass on the sphere. -/
theorem measureFlow_supportedIn_sphere (θ : Params d) {T : ℝ} (hT : 0 ≤ T)
    {ν : Measure (Eucl d)} (h : supportedIn ν (sphere d)) :
    supportedIn (measureFlow θ T ν) (sphere d) := by
  show (ν.map (flowMap θ T)) (sphere d)ᶜ = 0
  have hms : MeasurableSet (sphere d)ᶜ := (Metric.isClosed_sphere.measurableSet).compl
  rw [Measure.map_apply (measurable_flowMap θ hT) hms]
  refine measure_mono_null (fun x hx => ?_) h
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
  exact fun hxs => hx (flowMap_mem_sphere θ hT hxs)

/-- A sphere-supported measure is a.e. bounded in norm by any `R ≥ 1` (on the sphere `‖y‖ = 1`). -/
theorem ae_norm_le_of_supportedIn_sphere {ν : Measure (Eucl d)} {R : ℝ} (hR : 1 ≤ R)
    (h : supportedIn ν (sphere d)) : ∀ᵐ y ∂ν, ‖y‖ ≤ R := by
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h
  simp only [Set.mem_setOf_eq, not_le] at hy
  simp only [sphere, Set.mem_compl_iff, Metric.mem_sphere, dist_zero_right]
  intro hy1; rw [hy1] at hy; linarith

/-- **Proposition 2.2** (clustering to a discrete measure). An atomless probability measure on the
sphere can be driven `W₂`-close to a prescribed `M`-atom discrete measure `∑ α k • δ_{x k}` on the
sphere (convex weights, `∑ α k = 1`, each `α k ≠ 0`). AXIOM (`math.axiomatised`): the paper's own
proof (Section 2.2 and Remark 2.3) is a GATED PERCEPTRON construction -- prescribed-mass splitting
(machine-checked here as `exists_atomless_partition`) followed by ball-chain transport of each
piece (Lemmas B.1/B.2), all with `V ≡ 0` parameters -- so the statement lives faithfully on the
linear layer, and its honest Lean derivation is a future assembly over `lemma_B_1` and the
Appendix-B gated machinery (milestone M4). `Depends-On exists_atomless_partition`,
`Depends-On lemma_B_1`.

History (F14): an earlier machine-checked assembly routed each piece through `lemma_3_2` and the
attention-based `cluster_to_point`, then parked the pieces and used the linearity
`measureFlow Θ (∑ αₖ • Pₖ) = ∑ αₖ • measureFlow Θ (Pₖ)`. That route is valid ONLY in the
measure-independent model: under the mean-field dynamics a mixture evolves as one system, and its
flow is NOT the mixture of its pieces' flows. With `cluster_to_point` restated on the mean-field
layer (where it belongs), the old route is no longer meaningful, and the earlier `MissingCap`
hypothesis (an artifact of the `lemma_3_2` rotation step) and the `9 M` budget (an artifact of the
composite) are dropped; the paper's own switch count for this regime is `O(M)` with a non-explicit
constant (§1.4.3), deferred rather than invented.

**Fidelity (soundness):** probability, atomless, sphere support, and on-sphere targets are the
paper's hypotheses (`μ₀ ∈ P(S^{d-1})` atomless, targets `δ_{x_k}` with `x_k ∈ S^{d-1}`); `d ≥ 3`
matches the ball-chain construction's room requirement (cf. `lemma_B_2`'s `d ≥ 2` plus the
routing/parking obstruction at `d = 2`, finding F12). -/
axiom prop_2_2 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (hd : 3 ≤ d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hatomless : ∀ x : Eucl d, μ {x} = 0)
    (hμsupp : supportedIn μ (sphere d))
    (M : ℕ) (x : Fin M → Eucl d) (hx : ∀ k, x k ∈ sphere d)
    (α : Fin M → ℝ≥0∞) (hα : ∑ k, α k = 1)
    (hα0 : ∀ k, α k ≠ 0)
    (ν_target : Measure (Eucl d))
    (htgt : ν_target = ∑ k : Fin M, α k • Measure.dirac (x k)) :
    ∃ θ : Params d, Axioms.W2 (measureFlow θ T μ) ν_target ≤ ε

end MeasureToMeasure.Statements
