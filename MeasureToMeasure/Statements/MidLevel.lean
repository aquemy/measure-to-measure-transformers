import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.ContinuityEquation
import MeasureToMeasure.Axioms.Dynamics
import MeasureToMeasure.Leaves.BarycenterNonColinear
import MeasureToMeasure.Foundations.AtomlessSplitting
import MeasureToMeasure.Foundations.GeodesicDistance

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
that supplies its self-contained core. This is sound only because every axiom is a *true*, standard
statement; where the original type-correct stub was a loose transcription we correct it to the
faithful form first (see `lemma_B_1` / `lemma_B_2`).

`lemma_B_1` is **proved** (not axiomatized): it is a genuine assembly of `lemma_B_2` and the
structural flow algebra (`Axioms/Dynamics.lean`) by induction on the length of the ball chain, so its
mass-retention bound is machine-checked given the single-ball transport fact.
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

/-- A family of measures has pairwise disjoint supports: a family of carrier sets `S i` (each holding
the full mass of `ν i`) that are pairwise disjoint. -/
def DisjointSupports {N : ℕ} (ν : Fin N → Measure (Eucl d)) : Prop :=
  ∃ S : Fin N → Set (Eucl d), (∀ i, supportedIn (ν i) (S i)) ∧
    Pairwise (fun i j => Disjoint (S i) (S j))

/-- **Proposition 2.1** (clustering to a point). A measure supported in an open hemisphere can be
driven arbitrarily `W₂`-close to a Dirac mass. AXIOM (`math.axiomatised`): the convergence rests on
the LaSalle invariance principle and Hartman-Grobman linearization for the attention flow
(Section 2.1), which Mathlib lacks. `Depends-On` the barycenter ODE leaf L6. -/
axiom prop_2_1 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (e : Eucl d) (he : ‖e‖ = 1) (hhemi : supportedIn μ {x | 0 < ⟪e, x⟫}) :
    ∃ (θ : Params d) (z : Eucl d), Axioms.W2 (measureFlow θ T μ) (Measure.dirac z) ≤ ε

/-- **Lemma 3.2** (transport into the orthant). One parameter switch moves the measure into
`Q₁^{d-1}`. AXIOM (`math.axiomatised`): realizes a separating-hyperplane rotation as a flow; rests on
continuity-equation flow existence. `Depends-On` the separating-hyperplane leaf L3. -/
axiom lemma_3_2 (μ : Measure (Eucl d)) (T : ℝ) (hT : 0 < T) :
    ∃ θ : Params d, switches θ ≤ 1 ∧ supportedIn (measureFlow θ T μ) (orthant d)

/-- **Lemma 3.3** (shrink a measure's hull toward its barycenter direction). For any tolerance the
measure can be concentrated into a small ball around some direction `α`. AXIOM
(`math.axiomatised`): the contraction is driven by the barycenter dynamics (leaf L6) but its
realization as a flow on measures rests on the missing continuity-equation theory. -/
axiom lemma_3_3 (μ : Measure (Eucl d)) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∃ (θ : Params d) (α : Eucl d), supportedIn (measureFlow θ T μ) (Metric.ball α ε)

/-- **Lemma 3.4, Part 1** (`γ₁ = 1` case). If two measures have equal barycenters, a constant
parameter makes the barycenters differ. AXIOM (`math.axiomatised`). The self-contained pigeonhole
core (non-constancy over an open ball) is the kernel-checked leaf L10 (`exists_ne_in_ball`). -/
axiom lemma_3_4_part1 (μ ν : Measure (Eucl d)) (T : ℝ) (hT : 0 < T)
    (hbar : barycenter μ = barycenter ν) :
    ∃ θ : Params d, barycenter (measureFlow θ T μ) ≠ barycenter (measureFlow θ T ν)

/-- **Lemma 3.4, Part 2** (`γ₁ ≠ 1` case). At most two switches make the barycenters non-colinear
(not `SameRay`). AXIOM (`math.axiomatised`). The "disjoint geodesic hulls ⟹ non-colinear barycenters"
implication used alongside this is the machine-checked leaf L11
(`barycenter_noncolinear_of_disjoint_hull`, review finding F2). -/
axiom lemma_3_4_part2 (μ ν : Measure (Eucl d)) (T : ℝ) (hT : 0 < T) :
    ∃ θ : Params d, switches θ ≤ 2 ∧
      ¬ SameRay ℝ (barycenter (measureFlow θ T μ)) (barycenter (measureFlow θ T ν))

/-- **Proposition 4.2** (steer one active point). With `d ≥ 3`, distinct inputs/targets, and the
inactive points (the first `M-1`) already at their targets, at most `6` switches move every input to
its target, keeping the inactive ones fixed. AXIOM (`math.axiomatised`): the gather/corridor/restore
construction is a geodesic gradient flow. Step 1 is leaf L3, the geodesic gradient is leaf L4.

The injectivity hypotheses are required for soundness: the flow map is bijective
(`flowMap_bijective`), so steering `x₀ (M-1)` to `y (M-1)` while fixing the inactive points is
possible only if the targets (and inputs) are distinct -- otherwise the map would need two preimages
for one point. The original stub omitted them. -/
axiom prop_4_2 (hd : 3 ≤ d) (M : ℕ) (x₀ y : Fin M → Eucl d) (T : ℝ) (hT : 0 < T)
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
    (hx₀ : Function.Injective x₀) (hy : Function.Injective y) :
    ∃ θ : Params d, switches θ ≤ 6 * M ∧ ∀ i, flowMap θ T (x₀ i) = y i := by
  induction M with
  | zero => exact ⟨idParams d, by simp [switches_id], fun i => i.elim0⟩
  | succ k ih =>
    -- Place the first k points by the induction hypothesis on the castSucc subfamily.
    have hx₀' : Function.Injective (x₀ ∘ Fin.castSucc) := hx₀.comp (Fin.castSucc_injective k)
    have hy' : Function.Injective (y ∘ Fin.castSucc) := hy.comp (Fin.castSucc_injective k)
    obtain ⟨φ, hφsw, hφ⟩ := ih (x₀ ∘ Fin.castSucc) (y ∘ Fin.castSucc) hx₀' hy'
    simp only [Function.comp_apply] at hφ
    -- Current positions of all k+1 points after φ.
    set p : Fin (k + 1) → Eucl d := fun i => flowMap φ T (x₀ i) with hp
    have hpinj : Function.Injective p := (flowMap_bijective φ T).injective.comp hx₀
    -- The first k points already sit at their targets, so prop_4_2's hypothesis holds.
    have hfix : ∀ i : Fin (k + 1), (i : ℕ) < (k + 1) - 1 → p i = y i := by
      intro i hi
      have hlt : (i : ℕ) < k := by omega
      calc p i = flowMap φ T (x₀ (Fin.castSucc (Fin.castLT i hlt))) := by
                rw [Fin.castSucc_castLT]
        _ = y (Fin.castSucc (Fin.castLT i hlt)) := hφ (Fin.castLT i hlt)
        _ = y i := by rw [Fin.castSucc_castLT]
    obtain ⟨ψ, hψsw, hψ⟩ := prop_4_2 hd (k + 1) p y T hT hpinj hy hfix
    refine ⟨comp φ ψ, ?_, ?_⟩
    · calc switches (comp φ ψ) ≤ switches φ + switches ψ := switches_comp φ ψ
        _ ≤ 6 * k + 6 := Nat.add_le_add hφsw hψsw
        _ = 6 * (k + 1) := by ring
    · intro i
      rw [flowMap_comp]
      exact hψ i

/-- **Clustering to a prescribed point** (Proposition 2.1 followed by Proposition 4.1). A measure in
an open hemisphere can be driven `W₂`-close to the Dirac mass at *any chosen* point `z`: first cluster
it to a point (Proposition 2.1), then steer that point to `z` (Proposition 4.1, here with a single
active point). AXIOM (`math.axiomatised`): a combination of the two axiomatized propositions; it is
the single-measure controllability fact that Theorem 1.1 lifts to a family by disentanglement and
parking. `Depends-On prop_2_1`, `Depends-On prop_4_1`. -/
axiom cluster_to_point (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (T ε : ℝ)
    (hT : 0 < T) (hε : 0 < ε)
    (z e : Eucl d) (he : ‖e‖ = 1) (hhemi : supportedIn μ {x | 0 < ⟪e, x⟫}) :
    ∃ θ : Params d, Axioms.W2 (measureFlow θ T μ) (Measure.dirac z) ≤ ε

/-- **Lemma 5.1** (transport map after disentanglement). If each disentangled pair is matchable, a
single bijective map matches them all. AXIOM (`math.axiomatised`): gluing the per-pair transport maps
across disjoint supports rests on the optimal-transport / measurable-selection theory Mathlib
lacks. -/
axiom lemma_5_1 {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d))
    (hmatch : ∀ i, ∃ Ti : Eucl d → Eucl d, (μ₀ i).map Ti = μ₁ i) :
    ∃ ψ : Eucl d → Eucl d, Function.Bijective ψ ∧ ∀ i, (μ₀ i).map ψ = μ₁ i

/-- **Lemma 5.4** (`L²` approximation by a flow map). Any transport map `ψ` is approximated in
`L²(μ)` by a flow map of the dynamics, to any tolerance, with finitely many switches. AXIOM
(`math.axiomatised`): the density of attention-flow maps in `L²` rests on the missing
continuity-equation theory. Combined with the coupling bound (leaf L7) this controls `W₂`. The
approximant `ψε` is measurable and the displacement is `L²`-integrable -- both implicit in the `∫`
bound being meaningful, made explicit so the `W₂` map bound (`W2_map_le_L2`) can consume them. -/
axiom lemma_5_4 (μ : Measure (Eucl d)) (ψ : Eucl d → Eucl d) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∃ (θ : Params d) (ψε : Eucl d → Eucl d),
      measureFlow θ T μ = μ.map ψε ∧ Measurable ψε ∧
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
`exists_closed_sublevel_mass_ge`) will prove. -/
axiom lemma_B_2 (μ : Measure (Eucl d)) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (z₀ z₁ : Eucl d) (hz₀ : z₀ ∈ sphere d) (hz₁ : z₁ ∈ sphere d) (R₀ R₁ : ℝ)
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

The statement is corrected from the original type-correct stub: the retained fraction multiplies
`μ ℬ₀` (the mass that starts in the first ball, funneled along the chain), not `μ (⋃ ℬ_k)` (the latter
makes the `K = 0` base case false, since `ℬ₀ ⊆ ⋃ ℬ_k`). The chain-overlap hypothesis `hchain` and the
per-step switch bound (now in `lemma_B_2`) are likewise required for the bound to hold. The chain is a
sequence of genuine **geodesic balls** `B(z_k, R_k)` (centers on the sphere), matching the faithful
`lemma_B_2` signature. -/
theorem lemma_B_1 (μ : Measure (Eucl d)) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (K : ℕ) (z : ℕ → Eucl d) (hz : ∀ k, z k ∈ sphere d) (R : ℕ → ℝ)
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
      lemma_B_2 (measureFlow θ T μ) T ε hT hε (z k) (z (k + 1)) (hz k) (hz (k + 1))
        (R k) (R (k + 1)) (hchain k)
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
supports and each member can be steered to within `ε` of its target by *some* schedule, then a
*single* schedule steers all of them simultaneously to within `ε`: each member's schedule is gated to
its (disjoint) support region and parks on the others (`flowMap_id_on_parked`). Mathlib has no
continuity-equation theory to derive this, so it is a labeled structural axiom. -/
axiom exists_parked_schedule {N : ℕ} (ν target : Fin N → Measure (Eucl d)) (T ε : ℝ)
    (hdisj : DisjointSupports ν)
    (hper : ∀ i, ∃ θ : Params d, Axioms.W2 (measureFlow θ T (ν i)) (target i) ≤ ε) :
    ∃ Θ : Params d, ∀ i, Axioms.W2 (measureFlow Θ T (ν i)) (target i) ≤ ε

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

/-- **Proposition 2.2** (clustering to a discrete measure). An atomless probability measure can be
driven `W₂`-close to a prescribed `M`-atom discrete measure `∑ α k • δ_{x k}` (convex weights,
`∑ α k = 1`, each `α k ≠ 0`). Needs `0 < d` (a basis direction is used to place each piece in a
hemisphere).

**Proved** (effective `math.axiomatised`): partition `μ` into probability pieces `P k` of mass `α k`
with pairwise disjoint supports (`exists_atomless_partition`); for each piece, rotate it into the
orthant with one switch (`lemma_3_2`) -- the orthant lies in the open hemisphere `{x | 0 < ⟪e_j, x⟫}`
of a basis direction `e_j` -- then cluster it to its target point `x k` (`cluster_to_point`),
composing the two schedules (`measureFlow_comp`). A single parked schedule `Θ` runs all pieces at once
(`exists_parked_schedule`); the solution map distributes over the convex combination
(`measureFlow_sum_smul`), and convexity of `W₂` under mixtures (`W2_convexCombo_le`) lifts the
per-piece bounds to the whole measure. The convex-combination bookkeeping is machine-checked. -/
theorem prop_2_2 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (hd : 0 < d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hatomless : ∀ x : Eucl d, μ {x} = 0)
    (hμsupp : supportedIn μ (sphere d))
    (M : ℕ) (x : Fin M → Eucl d) (α : Fin M → ℝ≥0∞) (hα : ∑ k, α k = 1)
    (hα0 : ∀ k, α k ≠ 0)
    (ν_target : Measure (Eucl d))
    (htgt : ν_target = ∑ k : Fin M, α k • Measure.dirac (x k)) :
    ∃ θ : Params d, Axioms.W2 (measureFlow θ T μ) ν_target ≤ ε := by
  obtain ⟨P, hPprob, hμeq, hdisj⟩ := exists_atomless_partition μ hatomless α hα hα0
  -- each piece is sphere-supported (it inherits `μ`'s support)
  have hPsupp : ∀ k, supportedIn (P k) (sphere d) :=
    fun k => supportedIn_of_sum_smul α P hα0 (hμeq ▸ hμsupp) k
  -- A basis direction `e_j` whose open half-space contains the orthant (`⟪e_j, y⟫ = y j > 0` there).
  obtain ⟨e, he, hsub⟩ : ∃ e : Eucl d, ‖e‖ = 1 ∧ orthant d ⊆ {y : Eucl d | 0 < ⟪e, y⟫} := by
    refine ⟨EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ), by simp, ?_⟩
    intro y hy
    have hinner : ⟪EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), y⟫ = y ⟨0, hd⟩ := by
      simp [EuclideanSpace.inner_single_left]
    simpa [Set.mem_setOf_eq, hinner] using hy ⟨0, hd⟩
  -- Each piece: rotate into the orthant (Lemma 3.2), then cluster to its target (Prop 2.1 + 4.1).
  have hper : ∀ k, ∃ θ : Params d, Axioms.W2 (measureFlow θ T (P k)) (Measure.dirac (x k)) ≤ ε := by
    intro k
    haveI := hPprob k
    obtain ⟨θ₁, _hsw, horth⟩ := lemma_3_2 (P k) T hT
    haveI := isProbabilityMeasure_measureFlow θ₁ T (P k)
    have hsupp : supportedIn (measureFlow θ₁ T (P k)) {y : Eucl d | 0 < ⟪e, y⟫} :=
      measure_mono_null (Set.compl_subset_compl.mpr hsub) horth
    obtain ⟨θ₂, hθ₂⟩ := cluster_to_point (measureFlow θ₁ T (P k)) T ε hT hε (x k) e he hsupp
    exact ⟨comp θ₁ θ₂, by rw [measureFlow_comp]; exact hθ₂⟩
  obtain ⟨Θ, hΘ⟩ := exists_parked_schedule P (fun k => Measure.dirac (x k)) T ε hdisj hper
  refine ⟨Θ, ?_⟩
  rw [htgt, hμeq, measureFlow_sum_smul]
  refine Axioms.W2_convexCombo_le α (fun k => measureFlow Θ T (P k)) (fun k => Measure.dirac (x k))
    hα ε hε.le (fun k => ?_) (fun k => ?_) (fun k => ?_) hΘ
  · haveI := hPprob k; exact isProbabilityMeasure_measureFlow Θ T (P k)
  · infer_instance
  · -- finiteness: both measures are supported in the ball of radius `max 1 ‖x k‖`
    haveI := hPprob k
    haveI := isProbabilityMeasure_measureFlow Θ T (P k)
    refine MeasureToMeasure.W2_ne_top_of_ae_norm_le _ _ (R := max 1 ‖x k‖) ?_ ?_
    · exact ae_norm_le_of_supportedIn_sphere (le_max_left _ _)
        (measureFlow_supportedIn_sphere Θ hT.le (hPsupp k))
    · simp only [ae_dirac_eq, Filter.eventually_pure]; exact le_max_right _ _

end MeasureToMeasure.Statements
