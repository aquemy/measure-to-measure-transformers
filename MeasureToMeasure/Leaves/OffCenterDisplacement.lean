import MeasureToMeasure.Leaves.OffCenterReach
import MeasureToMeasure.Foundations.GeodesicConvex

/-!
# Leaf (Lemma 3.4 Part 1, Path I): off-center collapse displacement bound

The non-self-centered analog of L3-collapse-1 (`normSq_flowMap_gatedBlock_sub_pole_le`). There the gate
direction and the pole coincide (`z = ω`); Path I gates on a fixed direction `z` and collapses to a
separate pole `ω`. The reach half is `gatedBlock_offCenter_reach` (barrier + logistic estimate): under
the rim budget it drives `⟪Φ_T x, ω⟫` up to any `b < 1`.

This leaf converts that inner-product reach into the **Euclidean displacement** the `W₂` concentration
integral consumes. As in the self-centered case the conversion is pure sphere polarization
`‖y − ω‖² = 2 − 2⟪y,ω⟫`, so `b ≤ ⟪y,ω⟫` gives `‖y − ω‖² ≤ 2(1 − b)` with no further analysis. The
**squared** form is stated directly because `Axioms.W2_map_le_L2` integrates `‖·‖²`.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Off-center collapse displacement.** With the pole `ω` strictly inside the gate sub-cap
(`cos R < m < ⟪z,ω⟫`, `0 ≤ cos R`), the gated block `gatedBlock hz hω` drives a starting point `x` of
the gate sub-cap `{m ≤ ⟪z,x⟫}` (with the pole-coordinate rim budget
`logOdds b ≤ logOdds ⟪x,ω⟫ + 2(m − cos R)T`) to within squared Euclidean distance `2(1 − b)` of the
pole `ω`. Non-self-centered analog of `normSq_flowMap_gatedBlock_sub_pole_le`, with the reach coming
from `gatedBlock_offCenter_reach`; sphere polarization `‖y − ω‖² = 2 − 2⟪y,ω⟫` does the rest. -/
theorem normSq_flowMap_gatedBlock_offCenter_sub_pole_le {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1)
    {cosR : ℝ} (hcosR : -1 ≤ cosR) (hcosR0 : 0 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {m b : ℝ}
    (hzω : m < (⟪z, ω⟫ : ℝ)) (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    {x : Eucl d} (hxs : x ∈ sphere d) (hne : x ≠ ω) (hne' : x ≠ -ω) (hxm : m ≤ (⟪z, x⟫ : ℝ))
    (hreach : logOdds b ≤ logOdds (⟪x, ω⟫ : ℝ) + 2 * (m - cosR) * T) :
    ‖flowMap [gatedBlock hz hω hcosR hT] T x - ω‖ ^ 2 ≤ 2 * (1 - b) := by
  -- reduce the single-block flow to the block's own flow: `flowMap [b] T = b.blockFlow T`
  have hfm : flowMap [gatedBlock hz hω hcosR hT] T x
      = (gatedBlock hz hω hcosR hT).blockFlow T x := by
    rw [flowMap_cons, flowMap_nil]; rfl
  rw [hfm]
  set y := (gatedBlock hz hω hcosR hT).blockFlow T x with hy
  -- reach: the starting point flows into `{ b ≤ ⟪·,ω⟫ }`
  have hreachpt : b ≤ (⟪y, ω⟫ : ℝ) :=
    gatedBlock_offCenter_reach hz hω hcosR hcosR0 hT hzω hb hxs hne hne' hxm hreach
  -- sphere polarization: `‖y − ω‖² = 2 − 2⟪y,ω⟫` (both `y` and `ω` are unit vectors)
  have hys : y ∈ sphere d := (gatedBlock hz hω hcosR hT).blockFlow_mem_sphere hxs hT
  have hpol : ‖y - ω‖ ^ 2 = 2 - 2 * (⟪y, ω⟫ : ℝ) := by
    rw [norm_sub_sq_real, norm_eq_one_of_mem_sphere hys, hω]; ring
  rw [hpol]; linarith

end MeasureToMeasure
