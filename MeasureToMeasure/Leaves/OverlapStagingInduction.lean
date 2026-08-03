import MeasureToMeasure.Leaves.CellStagingInduction
import MeasureToMeasure.Leaves.UniversalFlowPointwise

/-!
# Leaves (lemma 3.3 campaign): overlap-tolerant staging, the single-label sweep step

The Phase-1 staging engine `staged_prefix_of_separated_caps` (CellStagingInduction.lean) forces
every later cell to be set-disjoint from every EARLIER gate ball (`hEavoid`), because its
invariant tracks each cell's mass at the measure level: a cell partially inside an earlier gate
would give a MIXED-support measure that neither conjunct of the per-step engine can handle. For
a connected spread-out support this is fatal: gate-separated cells cannot exhaust the support,
and thinning the gates does not help when the radial mass around a cap centre is strictly
spread (every annulus of positive width carries positive mass).

In the SINGLE-LABEL case (all tracked mass bound for one common target, exactly the shape of
the paper's Lemma 3.3 collapse) the gate separation can be dropped: when a later cap's collapse
ball overlaps mass already staged by an earlier cap, its pull simply SWEEPS that mass into its
own staging ball, which serves the same label. The mechanism that makes the bookkeeping close
is POINTWISE tracking through the schedule's universal `V = 0` transport map (the Dirac
upgrades of `UniversalFlowPointwise.lean`): pointwise, a cell straddling an earlier collapse
ball and the earlier gate's exterior needs no mixed-support decomposition, because each POINT
falls into exactly one regime of the per-step dichotomy.

This file's first leaf, `exists_staging_sweep_step`, is the per-cap primitive in that pointwise
language: one attention block of duration exactly `τ` whose universal map sends every sphere
point of the collapse ball into a prescribed target ball and literally fixes every sphere point
off the gate ball, together with the measure-level sweep clauses (support collapse for the cap
united with the earlier staged balls it wholly contains, the wholly-in-or-wholly-out capture
dichotomy for earlier staged balls, and exact fixing of every gate-null measure). It is the
metric-ball collapse step `exists_staging_collapse_step` upgraded pointwise via
`flow_map_mem_of_universal` / `flow_map_fixed_of_universal`.

The second leaf, `staged_prefix_overlapping_caps`, is the overlap-tolerant induction built on
it: caps fire in index order and the invariant carries, for every point of every cell, the
dichotomy "already staged in some ball `Metric.ball (c j) ρ`" or "still literally fixed, and
all of its cell indices lie in the future". The residual geometric obligation is strictly
weaker than `hEavoid`: a later cell may overlap earlier gates freely inside their COLLAPSE
balls (the sweep handles that mass), and must only avoid the earlier thin gate ANNULI
`ball (c j) (b j) \ closedBall (c j) (a j)`, the per-block dead zone that no finite-duration
gated pull can collapse.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Foundations MeasureToMeasure.Statements

variable {d : ℕ} [NeZero d]

/-- **Single-cap sweep step, pointwise and measure-level.** For a cap with on-sphere centre `c`,
collapse radius `a`, gate radius `b` (`0 < a < b ≤ 2`), a target ball `Metric.ball z r` around
any point `z` with `dist c z < r`, and finitely many earlier staged balls `B i` each either
wholly inside the collapse ball or wholly disjoint from the gate ball, one attention block `p`
of duration EXACTLY `τ` has a universal `V = 0` transport map `f` (measurable, sphere-to-sphere,
`attnMeasureFlow [p] ν = ν.map f` for every sphere probability measure `ν`) with:

* pointwise collapse: `f` sends every sphere point of `Metric.closedBall c a` into
  `Metric.ball z r`;
* pointwise fixing: `f` literally fixes every sphere point off the open gate ball
  `Metric.ball c b`;
* the sweep: every sphere probability measure carried by the collapse ball together with the
  wholly-contained earlier staged balls flows into `Metric.ball z r` (EXACT full mass);
* the capture dichotomy: each earlier staged ball's mass either lands in `Metric.ball z r` or
  is exactly fixed;
* every sphere probability measure with zero gate-ball mass is EXACTLY fixed.

Derived from `exists_staging_collapse_step` at staging radius `r - dist c z`, with the
pointwise clauses extracted by Dirac instantiation (`flow_map_mem_of_universal`,
`flow_map_fixed_of_universal`). -/
theorem exists_staging_sweep_step {c z : Eucl d} (hc : c ∈ sphere d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb2 : b ≤ 2)
    {r : ℝ} (hzr : dist c z < r)
    {M : ℕ} (B : Fin M → Set (Eucl d))
    (hB : ∀ i, B i ⊆ Metric.closedBall c a ∨ Disjoint (B i) (Metric.ball c b))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ p : AttnParams d, p.duration = τ ∧
      ∃ f : Eucl d → Eucl d, Measurable f ∧ Set.MapsTo f (sphere d) (sphere d) ∧
        (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          attnMeasureFlow [p] ν = ν.map f) ∧
        (∀ x ∈ sphere d, x ∈ Metric.closedBall c a → f x ∈ Metric.ball z r) ∧
        (∀ x ∈ sphere d, x ∉ Metric.ball c b → f x = x) ∧
        (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          supportedIn ν
            (Metric.closedBall c a ∪ ⋃ i ∈ {i : Fin M | B i ⊆ Metric.closedBall c a}, B i) →
          supportedIn (attnMeasureFlow [p] ν) (Metric.ball z r)) ∧
        (∀ i : Fin M, ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] →
          supportedIn ν (sphere d) → supportedIn ν (B i) →
          supportedIn (attnMeasureFlow [p] ν) (Metric.ball z r) ∨ attnMeasureFlow [p] ν = ν) ∧
        (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          ν (Metric.ball c b) = 0 → attnMeasureFlow [p] ν = ν) := by
  set ρ : ℝ := r - dist c z with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  obtain ⟨p, hpdur, hpcol, hpfix, hpfixF, f, hfm, hfto, hfmap⟩ :=
    exists_staging_collapse_step hc ha hab hb2 hτ hρ
  have hsub : Metric.ball c ρ ⊆ Metric.ball z r := by
    intro x hx
    rw [Metric.mem_ball] at hx ⊢
    have h1 := dist_triangle x c z
    rw [hρdef] at hx
    linarith
  refine ⟨p, hpdur, f, hfm, hfto, hfmap, ?_, ?_, ?_, ?_, hpfix⟩
  · -- pointwise collapse: Dirac instantiation of the support-collapse conjunct
    intro x hxs hxa
    exact hsub (flow_map_mem_of_universal hfmap hpcol hxs hxa)
  · -- pointwise fixing: Dirac instantiation of the avoid-set fixing conjunct
    intro x hxs hxb
    refine flow_map_fixed_of_universal hfmap hxs ?_
    exact hpfixF {x} (Set.disjoint_singleton_left.mpr hxb) (Measure.dirac x)
      (supportedIn_dirac hxs) (supportedIn_dirac rfl)
  · -- the sweep: the wholly-contained staged balls add nothing beyond the collapse ball
    intro ν _hprob hνs hνsup
    have hν' : supportedIn ν (Metric.closedBall c a) := by
      refine supportedIn_mono ?_ hνsup
      exact Set.union_subset Set.Subset.rfl (Set.iUnion₂_subset fun i hi => hi)
    exact supportedIn_mono hsub (hpcol ν hνs hν')
  · -- the capture dichotomy for each earlier staged ball
    intro i ν _hprob hνs hνB
    rcases hB i with hcap | hdis
    · exact Or.inl (supportedIn_mono hsub (hpcol ν hνs (supportedIn_mono hcap hνB)))
    · exact Or.inr (hpfixF (B i) hdis ν hνs hνB)

/-- **The overlap-tolerant staging induction (single label, no `hEavoid`).** Caps
`(c k, a k, b k)` fire in index order, one `exists_staging_sweep_step` block each, duration
exactly `L * τ` in total. Unlike `staged_prefix_of_separated_caps`, a later cell may OVERLAP
earlier gates: the geometric obligations are only

* `hE`: each cell sits in its own collapse ball;
* `hEann`: each cell avoids every EARLIER thin gate annulus
  `ball (c j) (b j) \ closedBall (c j) (a j)` (the per-block dead zone; overlap with the
  earlier collapse ball itself is allowed, and that is what a connected spread-out support
  needs);
* `hsep`: the staged-ball capture dichotomy, each pair of caps either close enough that the
  earlier staging ball is wholly swallowed by the later collapse ball with a `ρ`-margin, or far
  enough that it wholly clears the later gate ball (the radius tuning `TunedCapSystem`
  provides).

The proof tracks every cell point THROUGH the universal `V = 0` transport map, no
mixed-support decomposition: the invariant after `K` steps is the pointwise dichotomy "already
staged in some ball `Metric.ball (c j) ρ` with `j < K`" or "still literally fixed, and every
cell index of the point is `≥ K`". A staged point hops under `hsep` (swept into the firing
cap's own staging ball, or fixed clear of its gate); a still-fresh point is collapsed the first
time any collapse ball reaches it, at latest at its own cap, and `hEann` is exactly what keeps
it out of the dead annuli until then. The public conclusion: one schedule and ONE universal map
staging every sphere point of every cell into the union of the tiny staging balls, hence
carrying EVERY sphere probability measure supported in the cells into that union at exact full
mass, while every measure with zero mass on every gate ball is EXACTLY fixed, pointwise and
measure-level. -/
theorem staged_prefix_overlapping_caps {L : ℕ}
    (c : Fin L → Eucl d) (hc : ∀ k, c k ∈ sphere d)
    (a b : Fin L → ℝ) (ha : ∀ k, 0 < a k) (hab : ∀ k, a k < b k) (hb2 : ∀ k, b k ≤ 2)
    (E : Fin L → Set (Eucl d)) (hE : ∀ k, E k ⊆ Metric.closedBall (c k) (a k))
    (hEann : ∀ j k : Fin L, j < k →
      Disjoint (E k) (Metric.ball (c j) (b j) \ Metric.closedBall (c j) (a j)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsep : ∀ j k : Fin L, j < k →
      dist (c j) (c k) + ρ ≤ a k ∨ b k + ρ ≤ dist (c j) (c k))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = (L : ℝ) * τ ∧
      ∃ f : Eucl d → Eucl d, Measurable f ∧ Set.MapsTo f (sphere d) (sphere d) ∧
        (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          attnMeasureFlow θ ν = ν.map f) ∧
        (∀ x ∈ sphere d, x ∈ ⋃ k, E k → f x ∈ ⋃ j, Metric.ball (c j) ρ) ∧
        (∀ x ∈ sphere d, x ∉ ⋃ j, Metric.ball (c j) (b j) → f x = x) ∧
        (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          supportedIn ν (⋃ k, E k) →
          supportedIn (attnMeasureFlow θ ν) (⋃ j, Metric.ball (c j) ρ)) ∧
        (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          (∀ j, ν (Metric.ball (c j) (b j)) = 0) → attnMeasureFlow θ ν = ν) := by
  have key : ∀ K : ℕ, K ≤ L → ∃ θ : AttnSchedule d,
      AttnSchedule.durationSum θ = (K : ℝ) * τ ∧
      ∃ f : Eucl d → Eucl d, Measurable f ∧ Set.MapsTo f (sphere d) (sphere d) ∧
        (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          attnMeasureFlow θ ν = ν.map f) ∧
        (∀ x ∈ sphere d, (∃ m : Fin L, x ∈ E m) →
          (∃ j : Fin L, (j : ℕ) < K ∧ f x ∈ Metric.ball (c j) ρ) ∨
          (f x = x ∧ ∀ m : Fin L, x ∈ E m → K ≤ (m : ℕ))) ∧
        (∀ x ∈ sphere d, (∀ j : Fin L, (j : ℕ) < K → x ∉ Metric.ball (c j) (b j)) →
          f x = x) ∧
        (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          (∀ j : Fin L, (j : ℕ) < K → ν (Metric.ball (c j) (b j)) = 0) →
          attnMeasureFlow θ ν = ν) := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨[], by simp, id, measurable_id, Set.mapsTo_id _, ?_, ?_, ?_, ?_⟩
      · intro ν _ _
        exact (Measure.map_id).symm
      · intro x _ _
        exact Or.inr ⟨rfl, fun m _ => Nat.zero_le _⟩
      · intro x _ _
        rfl
      · intro ν _ _ _
        rfl
    | succ K ih =>
      intro hK1
      have hKL : K < L := hK1
      obtain ⟨θ, hθdur, f₀, hf₀m, hf₀to, hf₀map, hstage, hfixpt, hfixmeas⟩ :=
        ih (Nat.le_of_lt hKL)
      set kK : Fin L := ⟨K, hKL⟩ with hkKdef
      obtain ⟨p, hpdur, fp, hfpm, hfpto, hfpmap, hpcolpt, hpfixpt, _hpsweep, _hpdicho, hpfix⟩ :=
        exists_staging_sweep_step (c := c kK) (z := c kK) (hc kK) (ha kK) (hab kK) (hb2 kK)
          (r := ρ) (by simpa using hρ) (M := 0) (fun i => i.elim0) (fun i => i.elim0) hτ
      refine ⟨θ ++ [p], ?_, fp ∘ f₀, hfpm.comp hf₀m, hfpto.comp hf₀to,
        universal_map_append hf₀m hfpm hf₀map hfpmap, ?_, ?_, ?_⟩
      · rw [AttnSchedule.durationSum_append, hθdur]
        have hsing : AttnSchedule.durationSum [p] = p.duration := by
          simp [AttnSchedule.durationSum]
        rw [hsing, hpdur]
        push_cast
        ring
      · -- the staged-or-future invariant
        intro x hxs hxE
        have hfx_s : f₀ x ∈ sphere d := hf₀to hxs
        rcases hstage x hxs hxE with ⟨j, hjK, hjball⟩ | ⟨hfix, hmin⟩
        · -- already staged: capture dichotomy of cap K against the holding ball
          have hjkK : j < kK := by
            rw [Fin.lt_def]
            exact hjK
          rcases hsep j kK hjkK with hcap | havoid
          · -- swept into cap K's own staging ball
            left
            refine ⟨kK, Nat.lt_succ_self K, ?_⟩
            have hin : f₀ x ∈ Metric.closedBall (c kK) (a kK) := by
              rw [Metric.mem_closedBall]
              have h1 : dist (f₀ x) (c j) < ρ := Metric.mem_ball.mp hjball
              have h2 := dist_triangle (f₀ x) (c j) (c kK)
              linarith
            show fp (f₀ x) ∈ Metric.ball (c kK) ρ
            exact hpcolpt (f₀ x) hfx_s hin
          · -- fixed clear of cap K's gate
            left
            refine ⟨j, Nat.lt_succ_of_lt hjK, ?_⟩
            have hout : f₀ x ∉ Metric.ball (c kK) (b kK) := by
              rw [Metric.mem_ball, not_lt]
              have h1 : dist (f₀ x) (c j) < ρ := Metric.mem_ball.mp hjball
              have h2 := dist_triangle (c j) (f₀ x) (c kK)
              rw [dist_comm (c j) (f₀ x)] at h2
              linarith
            show fp (f₀ x) ∈ Metric.ball (c j) ρ
            rw [hpfixpt (f₀ x) hfx_s hout]
            exact hjball
        · -- still fresh: collapsed now, or fixed with all cell indices in the future
          by_cases hKcell : x ∈ E kK
          · left
            refine ⟨kK, Nat.lt_succ_self K, ?_⟩
            show fp (f₀ x) ∈ Metric.ball (c kK) ρ
            rw [hfix]
            exact hpcolpt x hxs (hE kK hKcell)
          · obtain ⟨m, hm⟩ := hxE
            have hmK : K ≤ (m : ℕ) := hmin m hm
            have hmne : (m : ℕ) ≠ K := by
              intro he
              exact hKcell (by rwa [show m = kK from Fin.ext he] at hm)
            have hkKm : kK < m := by
              rw [Fin.lt_def]
              show K < (m : ℕ)
              omega
            by_cases hxa : x ∈ Metric.closedBall (c kK) (a kK)
            · -- an early collapse ball reached the fresh point: swept ahead of its own cap
              left
              refine ⟨kK, Nat.lt_succ_self K, ?_⟩
              show fp (f₀ x) ∈ Metric.ball (c kK) ρ
              rw [hfix]
              exact hpcolpt x hxs hxa
            · -- `hEann` keeps the fresh point out of the dead annulus: it clears the gate
              right
              have hxb : x ∉ Metric.ball (c kK) (b kK) := by
                intro hxb
                exact (Set.disjoint_right.mp (hEann kK m hkKm) ⟨hxb, hxa⟩) hm
              refine ⟨?_, ?_⟩
              · show fp (f₀ x) = x
                rw [hfix]
                exact hpfixpt x hxs hxb
              · intro m' hm'
                have h1 : K ≤ (m' : ℕ) := hmin m' hm'
                have h2 : (m' : ℕ) ≠ K := by
                  intro he
                  exact hKcell (by rwa [show m' = kK from Fin.ext he] at hm')
                omega
      · -- pointwise gate fixing, one more gate absorbed
        intro x hxs hgates
        have h0 : f₀ x = x := hfixpt x hxs fun j hj => hgates j (Nat.lt_succ_of_lt hj)
        show fp (f₀ x) = x
        rw [h0]
        exact hpfixpt x hxs (hgates kK (Nat.lt_succ_self K))
      · -- measure-level gate fixing, one more gate absorbed
        intro ν _hprob hνs hνgates
        rw [attnMeasureFlow_append,
          hfixmeas ν hνs fun j hj => hνgates j (Nat.lt_succ_of_lt hj)]
        exact hpfix ν hνs (hνgates kK (Nat.lt_succ_self K))
  obtain ⟨θ, hθdur, f, hfm, hfto, hfmap, hstage, hfixpt, hfixmeas⟩ := key L le_rfl
  have hstage' : ∀ x ∈ sphere d, x ∈ ⋃ k, E k → f x ∈ ⋃ j, Metric.ball (c j) ρ := by
    intro x hxs hxE
    rw [Set.mem_iUnion] at hxE
    rcases hstage x hxs hxE with ⟨j, _, hj⟩ | ⟨_, hmin⟩
    · exact Set.mem_iUnion.mpr ⟨j, hj⟩
    · obtain ⟨m, hm⟩ := hxE
      exact absurd (hmin m hm) (Nat.not_le.mpr m.isLt)
  refine ⟨θ, hθdur, f, hfm, hfto, hfmap, hstage', ?_, ?_,
    fun ν _hprob hνs hg => hfixmeas ν hνs fun j _ => hg j⟩
  · intro x hxs hxgates
    exact hfixpt x hxs fun j _ hj => hxgates (Set.mem_iUnion.mpr ⟨j, hj⟩)
  · -- exact full-mass staging at the measure level, through the universal map
    intro ν _hprob hνs hνE
    rw [hfmap ν hνs]
    have hmeas : MeasurableSet (⋃ j, Metric.ball (c j) ρ) :=
      MeasurableSet.iUnion fun j => measurableSet_ball
    show (ν.map f) (⋃ j, Metric.ball (c j) ρ)ᶜ = 0
    rw [Measure.map_apply hfm hmeas.compl]
    refine measure_mono_null ?_ (measure_union_null hνs hνE)
    intro x hx
    rw [Set.mem_preimage, Set.mem_compl_iff] at hx
    by_cases hxs : x ∈ sphere d
    · by_cases hxE : x ∈ ⋃ k, E k
      · exact absurd (hstage' x hxs hxE) hx
      · exact Or.inr hxE
    · exact Or.inl hxs

end MeasureToMeasure.Leaves
