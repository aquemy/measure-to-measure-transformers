import MeasureToMeasure.Leaves.GatedFlow
import MeasureToMeasure.Foundations.GeodesicConvex
import MeasureToMeasure.Statements.SupportedIn

/-!
# Leaf L3-collapse-1 (Lemma 3.4 Part 1): single-block collapse displacement bound

The App. B.3 Part 1 collapse concentrates a cap's mass onto the pole `ω = x*` with one self-centered
gated block. `gatedBlock_mapsTo_cap` (`Leaves/GatedFlow.lean`) is the *reach* half: the whole closed
sub-cap `{x ∈ 𝕊 | m ≤ ⟪x,ω⟫}` flows into the tighter cap `{y | b ≤ ⟪y,ω⟫}` under a single uniform
duration `T`, provided the rim budget `logOdds b ≤ logOdds m + 2·(m − cos R)·T` holds.

This leaf converts that inner-product reach into the **Euclidean displacement** bound the `W₂`
concentration integral consumes. On the unit sphere the two are the same fact through polarization:
`‖y − ω‖² = 2 − 2⟪y,ω⟫`, so `b ≤ ⟪y,ω⟫` gives `‖y − ω‖² ≤ 2·(1 − b)` with no analysis — the geodesic
flow's contraction toward the pole and the shrinking chord `‖y − ω‖` are two views of the monotone
increase of `⟪·,ω⟫` along the flow. Driving `b → 1` (via the rim budget, i.e. `T → ∞`) collapses the
displacement to `0`. The **squared** form is stated directly since the `W₂` bound
`Axioms.W2_map_le_L2` integrates `‖·‖²`, so the caller never pays a `Real.sqrt`.

The file's second half upgrades the pointwise bridge to the **measure level**:
`measureFlow_gatedBlock_supportedIn_ball` converts `gatedBlock_mapsTo_cap`'s `Set.MapsTo` into a
`supportedIn`-a-ball conclusion for every cap-supported sphere measure (null-preservation of the
pushforward `measureFlow = μ.map (flowMap · T)` plus the same polarization), and
`exists_gatedBlock_supportedIn_ball` packages the reach-budget bookkeeping into a plain existential
over the duration `T` for downstream consumers.
-/

namespace MeasureToMeasure

open MeasureTheory
open scoped RealInnerProductSpace
open MeasureToMeasure.Axioms MeasureToMeasure.Statements

variable {d : ℕ}

/-- **L3-collapse-1.** The self-centered gated block drives every point of the closed sub-cap
`{x ∈ 𝕊 | m ≤ ⟪x,ω⟫}` to within squared Euclidean distance `2·(1 − b)` of the pole `ω`, under the
single rim budget `logOdds b ≤ logOdds m + 2·(m − cos R)·T`. This is the Euclidean-displacement form
(via sphere polarization `‖y − ω‖² = 2 − 2⟪y,ω⟫`) of the reach statement `gatedBlock_mapsTo_cap`; it
supplies the pointwise integrand for the `W₂` collapse bound `Axioms.W2_map_le_L2`. -/
theorem normSq_flowMap_gatedBlock_sub_pole_le {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {m b : ℝ} (hmR : cosR < m) (hm1 : m < 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hreach : logOdds b ≤ logOdds m + 2 * (m - cosR) * T)
    {x : Eucl d} (hxs : x ∈ sphere d) (hxm : m ≤ (⟪x, ω⟫ : ℝ)) :
    ‖flowMap [gatedBlock hω hω hcosR hT] T x - ω‖ ^ 2 ≤ 2 * (1 - b) := by
  -- reduce the single-block flow to the block's own flow: `flowMap [b] T = b.blockFlow T`
  have hfm : flowMap [gatedBlock hω hω hcosR hT] T x
      = (gatedBlock hω hω hcosR hT).blockFlow T x := by
    rw [flowMap_cons, flowMap_nil]; rfl
  rw [hfm]
  set y := (gatedBlock hω hω hcosR hT).blockFlow T x with hy
  -- reach: the sub-cap maps into `{ b ≤ ⟪·,ω⟫ }`
  have hreachpt : b ≤ (⟪y, ω⟫ : ℝ) :=
    gatedBlock_mapsTo_cap hω hcosR hT hmR hm1 hb hreach ⟨hxs, hxm⟩
  -- sphere polarization: `‖y − ω‖² = 2 − 2⟪y,ω⟫` (both `y` and `ω` are unit vectors)
  have hys : y ∈ sphere d := (gatedBlock hω hω hcosR hT).blockFlow_mem_sphere hxs hT
  have hpol : ‖y - ω‖ ^ 2 = 2 - 2 * (⟪y, ω⟫ : ℝ) := by
    rw [norm_sub_sq_real, norm_eq_one_of_mem_sphere hys, hω]; ring
  rw [hpol]; linarith

/-!
## Measure-level collapse: `MapsTo` to `supportedIn`-a-ball

`gatedBlock_mapsTo_cap` is *pointwise*: every point of the closed sub-cap flows into the level-`b`
cap. The `measureFlow` of the single-block schedule is *definitionally* the pushforward
`μ.map (flowMap [gatedBlock …] T)`, so null-preservation of `Measure.map` transfers the pointwise
statement to the measure level: a measure carried by the sphere and by the sub-cap (the two
`supportedIn` hypotheses put full mass on `{x ∈ 𝕊 | m ≤ ⟪x,ω⟫}`) pushes forward to a measure whose
mass outside the target is zero. Polarization `‖y − ω‖² = 2 − 2⟪y,ω⟫` then converts the level-`b`
cap into the Euclidean ball `Metric.ball ω ε` as soon as `1 − ε²/2 < b`. No probability or
finiteness assumption is needed: the argument is pure null-set bookkeeping. The edge case `ε ≥ 2`
(the ball swallows the whole sphere) needs no special split: then `1 − ε²/2 ≤ −1 < b`, so the
threshold hypothesis is automatic.
-/

/-- **Measure-level cap collapse of the self-centered gated block.** If `μ` is carried by the
sphere and by the closed sub-cap `{x ∈ 𝕊 | m ≤ ⟪x,ω⟫}` (with `cosR < m < 1` strictly inside the
active region), then under the single rim budget `logOdds b ≤ logOdds m + 2·(m − cosR)·T` and the
threshold `1 − ε²/2 < b`, the flowed measure `measureFlow [gatedBlock hω hω hcosR hT] T μ` is
carried by the Euclidean ball `Metric.ball ω ε` around the pole. This is the `supportedIn` upgrade
of the pointwise `gatedBlock_mapsTo_cap`, via null-preservation of the pushforward and sphere
polarization. -/
theorem measureFlow_gatedBlock_supportedIn_ball {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {m b : ℝ} (hmR : cosR < m) (hm1 : m < 1)
    {ε : ℝ} (hε : 0 < ε) (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (hbε : 1 - ε ^ 2 / 2 < b)
    (hreach : logOdds b ≤ logOdds m + 2 * (m - cosR) * T)
    {μ : Measure (Eucl d)} (hμS : supportedIn μ (sphere d))
    (hμcap : supportedIn μ {x | m ≤ (⟪x, ω⟫ : ℝ)}) :
    supportedIn (measureFlow [gatedBlock hω hω hcosR hT] T μ) (Metric.ball ω ε) := by
  -- pointwise: the whole sub-cap lands inside the ball
  have hsub : (sphere d ∩ {x | m ≤ (⟪x, ω⟫ : ℝ)})
      ⊆ flowMap [gatedBlock hω hω hcosR hT] T ⁻¹' Metric.ball ω ε := by
    rintro x ⟨hxs, hxm⟩
    have hfm : flowMap [gatedBlock hω hω hcosR hT] T x
        = (gatedBlock hω hω hcosR hT).blockFlow T x := by
      rw [flowMap_cons, flowMap_nil]; rfl
    -- reach: the flowed point sits in the level-`b` cap
    have hreachpt : b ≤ (⟪(gatedBlock hω hω hcosR hT).blockFlow T x, ω⟫ : ℝ) :=
      gatedBlock_mapsTo_cap hω hcosR hT hmR hm1 hb hreach ⟨hxs, hxm⟩
    have hys : (gatedBlock hω hω hcosR hT).blockFlow T x ∈ sphere d :=
      (gatedBlock hω hω hcosR hT).blockFlow_mem_sphere hxs hT
    -- polarization: level-`b` cap into the `ε`-ball
    have hpol : ‖(gatedBlock hω hω hcosR hT).blockFlow T x - ω‖ ^ 2
        = 2 - 2 * (⟪(gatedBlock hω hω hcosR hT).blockFlow T x, ω⟫ : ℝ) := by
      rw [norm_sub_sq_real, norm_eq_one_of_mem_sphere hys, hω]; ring
    have hlt : ‖(gatedBlock hω hω hcosR hT).blockFlow T x - ω‖ ^ 2 < ε ^ 2 := by
      rw [hpol]; nlinarith
    have hnorm : ‖(gatedBlock hω hω hcosR hT).blockFlow T x - ω‖ < ε := by
      nlinarith [norm_nonneg ((gatedBlock hω hω hcosR hT).blockFlow T x - ω)]
    rw [Set.mem_preimage, hfm, Metric.mem_ball, dist_eq_norm]
    exact hnorm
  -- measure level: null-preservation of the pushforward
  show (measureFlow [gatedBlock hω hω hcosR hT] T μ) (Metric.ball ω ε)ᶜ = 0
  rw [measureFlow, Measure.map_apply (measurable_flowMap _ hT) measurableSet_ball.compl]
  refine measure_mono_null ?_ (measure_union_null hμS hμcap)
  rw [Set.preimage_compl, ← Set.compl_inter]
  exact Set.compl_subset_compl.mpr hsub

/-- **Existential form: some duration collapses the cap into any ball.** For every target radius
`ε > 0` there is a finite duration `T` whose self-centered gated block carries every measure
supported in the sphere and in the closed sub-cap `{x ∈ 𝕊 | m ≤ ⟪x,ω⟫}` into `Metric.ball ω ε`.
The reach-budget bookkeeping of `measureFlow_gatedBlock_supportedIn_ball` is discharged internally:
pick the cap level `b := max (1 − ε²/4) 0` (inside `Ioo (−1) 1` and above the `1 − ε²/2`
threshold), then `T := max 0 ((logOdds b − logOdds m) / (2·(m − cosR)))` satisfies the rim budget
since the gate constant `m − cosR` is strictly positive. -/
theorem exists_gatedBlock_supportedIn_ball {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR m : ℝ}
    (hcosR : -1 ≤ cosR) (hmR : cosR < m) (hm1 : m < 1) {ε : ℝ} (hε : 0 < ε)
    {μ : Measure (Eucl d)} (hμS : supportedIn μ (sphere d))
    (hμcap : supportedIn μ {x | m ≤ (⟪x, ω⟫ : ℝ)}) :
    ∃ (T : ℝ) (hT : 0 ≤ T),
      supportedIn (measureFlow [gatedBlock hω hω hcosR hT] T μ) (Metric.ball ω ε) := by
  -- cap level `b`: inside `Ioo (-1) 1` and above the polarization threshold `1 - ε²/2`
  set b : ℝ := max (1 - ε ^ 2 / 4) 0 with hbdef
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    · apply max_lt _ one_pos
      nlinarith
  have hbε : 1 - ε ^ 2 / 2 < b := by
    have h1 : 1 - ε ^ 2 / 2 < 1 - ε ^ 2 / 4 := by nlinarith
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  -- duration `T`: nonnegative and meeting the rim budget (the gate constant is positive)
  set T : ℝ := max 0 ((logOdds b - logOdds m) / (2 * (m - cosR))) with hTdef
  have hT : 0 ≤ T := le_max_left _ _
  have hpos : (0 : ℝ) < 2 * (m - cosR) := by linarith
  have hreach : logOdds b ≤ logOdds m + 2 * (m - cosR) * T := by
    have h1 : (logOdds b - logOdds m) / (2 * (m - cosR)) ≤ T := le_max_right _ _
    rw [div_le_iff₀ hpos] at h1
    nlinarith
  exact ⟨T, hT,
    measureFlow_gatedBlock_supportedIn_ball hω hcosR hT hmR hm1 hε hb hbε hreach hμS hμcap⟩

end MeasureToMeasure
