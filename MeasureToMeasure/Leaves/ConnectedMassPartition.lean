import MeasureToMeasure.Leaves.AtomlessDirection
import MeasureToMeasure.Leaves.ThresholdExtraction
import MeasureToMeasure.Leaves.SlabConnected

/-!
# Assembly: a connected, prescribed-mass partition of the sphere (Proposition 2.2)

The final assembly of Steps A-C into `prop_2_2`'s connected-prescribed-mass partition: given `d ≥ 3`
and any strictly increasing sequence of cumulative mass targets `m₀=0 < m₁ < ... < m_M=1`, the
sphere splits into `M` pieces `P₀,...,P_{M-1}` such that each `Pₖ` is *connected*, has *exact* mass
`mₖ₊₁ - mₖ`, and is measure-disjoint from every other piece.

**The construction.** Pick a generic atomless direction `u` (Step A). Simultaneously extract a
threshold `tₖ` for every cumulative target `mₖ` (Step B, bundled over the whole index family via
`choose`; monotonicity of the resulting `t` follows from strict monotonicity of `m` plus
monotonicity of the underlying CDF). Each piece `Pₖ := {x ∈ sphere d | tₖ ≤ ⟪u,x⟫ ≤ tₖ₊₁}` is then
connected by Step C (`d ≥ 3`), has mass `mₖ₊₁ - mₖ` by a slab/threshold bookkeeping identity, and is
measure-disjoint from any other piece because two slabs can only meet at a shared endpoint
`{x | ⟪u,x⟫ = tⱼ}`, which is null (Step B's threshold-is-null guarantee).

Pieces are "measure-disjoint," not literally set-disjoint: adjacent closed slabs `[tₖ,tₖ₊₁]` and
`[tₖ₊₁,tₖ₊₂]` share the single level set `{x|⟪u,x⟫=tₖ₊₁}`, which carries zero mass but is not
literally empty. This is the natural granularity for a measure-theoretic partition and lets every
piece reuse Step C's *closed*-slab connectedness directly (a half-open slab's connectedness would
need re-deriving Step C's argument on `Ico`/`Ioc` instead of `Icc`).

This leaf reduces `prop_2_2`'s discharge to the two remaining obligations already identified this
session: the "gated schedule" that steers each piece into place while parking the others
(`Leaves/DiscreteClustering.lean`'s docstring), and the combination glue (already banked there,
`measureFlow_W2_discrete_of_perPiece`, PR #91) — this leaf supplies the `Pₖ`'s those consume.

M3b/mid-level staging: assembly of the `prop_2_2` partition construction; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- Restricting a set to a full-measure set doesn't change its measure. -/
theorem measure_inter_eq_of_compl_null (μ0 : Measure (Eucl d)) (A B : Set (Eucl d))
    (hB : μ0 Bᶜ = 0) (hBmeas : MeasurableSet B) :
    μ0 (A ∩ B) = μ0 A := by
  have hsub : A \ B ⊆ Bᶜ := fun x hx => hx.2
  have hnull : μ0 (A \ B) = 0 := nonpos_iff_eq_zero.mp (hB ▸ measure_mono hsub)
  have heq := measure_sdiff_add_inter (μ := μ0) A hBmeas
  rw [hnull, zero_add] at heq
  exact heq

/-- **The mass of a slab, in terms of the two threshold measures.** `μ0(slab [a,b]) = F(b) - F(a)`,
using that the lower endpoint itself carries no mass (so `<` and `≤` at `a` agree). -/
theorem measure_slab_eq_sub (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    (u : Metric.sphere (0:Eucl d) 1) (hμ0S : μ0 (sphere d)ᶜ = 0)
    (a b : ℝ) (hab : a ≤ b)
    (hnull_a : μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) = a} = 0) (ma mb : ENNReal)
    (hma : μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) ≤ a} = ma)
    (hmb : μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) ≤ b} = mb) :
    μ0 {x : Eucl d | x ∈ sphere d ∧ a ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b} = mb - ma := by
  have hAeq : {x : Eucl d | x ∈ sphere d ∧ a ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b}
      = {x : Eucl d | a ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b} ∩ sphere d := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [hAeq]
  have hBmeas : MeasurableSet (sphere d) := by
    rw [MeasureToMeasure.sphere]
    exact Metric.isClosed_sphere.measurableSet
  rw [measure_inter_eq_of_compl_null μ0 _ (sphere d) hμ0S hBmeas]
  have hsub : {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) < a} ⊆ {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) ≤ b} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    linarith
  have hslab_eq : {x : Eucl d | a ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b}
      = {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) ≤ b} \ {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) < a} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_sdiff, not_lt]; tauto
  rw [hslab_eq, measure_sdiff hsub (measurableSet_lt (by fun_prop) measurable_const).nullMeasurableSet
    (measure_lt_top μ0 _).ne]
  have hlt_eq : {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) < a} = {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) ≤ a} \
      {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) = a} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_sdiff]; constructor
    · intro h; exact ⟨h.le, h.ne⟩
    · intro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 h2
  rw [hlt_eq, measure_sdiff_null hnull_a, hma, hmb]

/-- **Two slabs sharing a null boundary are measure-disjoint.** If slab `[a1,b1]` ends where slab
`[a2,b2]` begins (`b1 ≤ a2`) and the shared level `b1` carries no mass, their intersection is null:
any point in both slabs is squeezed to `⟪u,x⟫ = b1` exactly. -/
theorem measure_slab_inter_slab_eq_zero (μ0 : Measure (Eucl d))
    (u : Metric.sphere (0:Eucl d) 1)
    (a1 b1 a2 b2 : ℝ) (hshared : b1 ≤ a2)
    (hnull : μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) = b1} = 0) :
    μ0 ({x : Eucl d | x ∈ sphere d ∧ a1 ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b1} ∩
        {x : Eucl d | x ∈ sphere d ∧ a2 ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b2}) = 0 := by
  have hsub : ({x : Eucl d | x ∈ sphere d ∧ a1 ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b1} ∩
      {x : Eucl d | x ∈ sphere d ∧ a2 ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b2})
      ⊆ {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) = b1} := by
    intro x ⟨⟨_, _, hxb1⟩, ⟨_, hxa2, _⟩⟩
    simp only [Set.mem_setOf_eq]
    linarith
  exact nonpos_iff_eq_zero.mp (hnull ▸ measure_mono hsub)

/-- **Simultaneous threshold extraction over a whole index family.** Bundles Step B's per-target
threshold (`exists_threshold_eq`) over an entire strictly monotone family of cumulative targets via
`choose`; the resulting threshold function is itself monotone, since strict monotonicity of the
targets plus monotonicity of the underlying CDF pins down the order of their preimages. `μ0` need
only be finite (not a probability measure), and the targets bounded by `μ0`'s own total mass rather
than a fixed `1` -- letting this be reused with `μ0` restricted to a single Voronoi cell. -/
theorem exists_thresholds (μ0 : Measure (Eucl d)) [IsFiniteMeasure μ0] [NoAtoms μ0]
    (u : Metric.sphere (0:Eucl d) 1) (hμ0S : μ0 (sphere d)ᶜ = 0)
    (hatomless : ∀ c : ℝ, μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) = c} = 0)
    {N : ℕ} (m : Fin N → ENNReal) (hm1 : ∀ k, m k ≤ μ0 Set.univ) (hmmono : StrictMono m) :
    ∃ t : Fin N → ℝ, Monotone t ∧ (∀ k, -1 ≤ t k ∧ t k ≤ 1) ∧
      (∀ k, μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) ≤ t k} = m k) ∧
      (∀ k, μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) = t k} = 0) := by
  choose t ht using fun k => exists_threshold_eq μ0 u hμ0S hatomless (m k) (hm1 k)
  refine ⟨t, ?_, fun k => ⟨(ht k).1, (ht k).2.1⟩, fun k => (ht k).2.2.2, fun k => (ht k).2.2.1⟩
  intro j k hjk
  rcases eq_or_lt_of_le hjk with heq | hlt
  · rw [heq]
  · by_contra hcon
    push Not at hcon
    have hFmono : μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) ≤ t k}
        ≤ μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫:ℝ) ≤ t j} := by
      apply measure_mono
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      linarith [hcon.le]
    rw [(ht k).2.2.2, (ht j).2.2.2] at hFmono
    exact absurd hFmono (not_le.mpr (hmmono hlt))

/-- **The connected, prescribed-mass partition (Proposition 2.2's geometric core).** For `d ≥ 3` and
any strictly increasing family of cumulative mass targets `m : Fin (M+1) → ℝ≥0∞` running from `0` to
`1`, the sphere splits into `M` connected pieces `Pₖ`, each with EXACT mass `m(k+1) - m(k)`, pairwise
measure-disjoint. `m 0 = 0` is not needed by this proof directly (the mass formula is self-contained
per piece) but is kept as a hypothesis for statement fidelity: without it the `mₖ₊₁-mₖ` masses need
not sum to `1`, defeating the point of calling `m` a family of cumulative targets. -/
theorem exists_connected_mass_partition (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    [NoAtoms μ0] (hd : 3 ≤ d) (hμ0S : μ0 (sphere d)ᶜ = 0)
    {M : ℕ} (m : Fin (M+1) → ENNReal) (_hm0 : m 0 = 0) (hmlast : m (Fin.last M) = 1)
    (hmmono : StrictMono m) :
    ∃ P : Fin M → Set (Eucl d),
      (∀ k, IsConnected (P k)) ∧
      (∀ k, μ0 (P k) = m k.succ - m k.castSucc) ∧
      (∀ j k, j ≠ k → μ0 (P j ∩ P k) = 0) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨u, hatomless⟩ := exists_atomless_direction μ0
  have hunivone : μ0 Set.univ = 1 := measure_univ
  have hm1 : ∀ k : Fin (M+1), m k ≤ μ0 Set.univ := by
    intro k
    rw [hunivone]
    rcases eq_or_lt_of_le (Fin.le_last k) with heq | hlt
    · rw [heq, hmlast]
    · exact (hmmono hlt).le.trans_eq hmlast
  obtain ⟨t, htmono, htbdd, htmass, htnull⟩ := exists_thresholds μ0 u hμ0S hatomless m hm1 hmmono
  have hcs_le : ∀ k : Fin M, t k.castSucc ≤ t k.succ := fun k =>
    htmono (by rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
  refine ⟨fun k => {x : Eucl d | x ∈ sphere d ∧ t k.castSucc ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧
    (⟪(u:Eucl d), x⟫:ℝ) ≤ t k.succ}, ?_, ?_, ?_⟩
  · intro k
    exact isConnected_slab u hd (t k.castSucc) (t k.succ) (hcs_le k)
      (htbdd k.castSucc).1 (htbdd k.succ).2
  · intro k
    exact measure_slab_eq_sub μ0 u hμ0S (t k.castSucc) (t k.succ) (hcs_le k)
      (htnull k.castSucc) (m k.castSucc) (m k.succ) (htmass k.castSucc) (htmass k.succ)
  · intro j k hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · exact measure_slab_inter_slab_eq_zero μ0 u (t j.castSucc) (t j.succ) (t k.castSucc) (t k.succ)
        (htmono (by rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)) (htnull j.succ)
    · rw [Set.inter_comm]
      exact measure_slab_inter_slab_eq_zero μ0 u (t k.castSucc) (t k.succ) (t j.castSucc) (t j.succ)
        (htmono (by rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)) (htnull k.succ)

end MeasureToMeasure.Leaves
