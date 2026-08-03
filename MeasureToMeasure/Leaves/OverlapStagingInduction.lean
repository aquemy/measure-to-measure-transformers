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

end MeasureToMeasure.Leaves
