import MeasureToMeasure.Leaves.GatedFlow
import MeasureToMeasure.Foundations.GeodesicConvex

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
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

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

end MeasureToMeasure
