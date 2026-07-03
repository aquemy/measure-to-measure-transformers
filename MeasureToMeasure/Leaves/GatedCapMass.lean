import MeasureToMeasure.Leaves.GatedFlow
import MeasureToMeasure.Axioms.ContinuityEquation

/-!
# Mass retention of the self-centered gated flow (Lemma B.2, discharge step 4: the measure form)

`gatedBlock_mapsTo_cap` (`Leaves/GatedFlow.lean`) is a *point-set* statement: the self-centered gated
flow at one uniform time `T` carries a whole closed sub-cap into a smaller target cap. This file turns
that into a *mass* statement by composing it with the pushforward bridge
`Axioms.le_measureFlow_of_mapsTo` (the measure-theoretic half of eq. B.8):

    μ { x ∈ 𝕊 | m ≤ ⟪x,ω⟫ }  ≤  measureFlow [gatedBlock …] T μ { y | b ≤ ⟪y,ω⟫ }.

The gated block enters as a **one-block schedule** `[gatedBlock …] : Params d`, so `switches` is `1` --
matching the `switches θ ≤ 1` budget in `lemma_B_2`. The schedule's flow map reduces definitionally to
the single block's characteristic flow (`flowMap [b] t = b.blockFlow t`), so the point-set `MapsTo`
feeds the bridge directly.

This is the self-centered (`z = ω`) core of B.8. The full lemma_B_2 additionally needs eq. B.6
(`exists_closed_sublevel_mass_ge`, already built) to pass from the *open* source cap to the closed
sub-cap with a `(1-ε)` loss, plus the general-position (`z ≠ ω`) gate confinement; those are the
remaining pieces of the two-cap assembly.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace
open Set MeasureTheory

variable {d : ℕ}

/-- The half-space cap `{ y | b ≤ ⟪y,ω⟫ }` is measurable: it is the preimage of `[b, ∞)` under the
continuous linear functional `y ↦ ⟪y,ω⟫`. -/
theorem measurableSet_inner_ge (ω : Eucl d) (b : ℝ) :
    MeasurableSet {y : Eucl d | b ≤ (⟪y, ω⟫ : ℝ)} :=
  measurableSet_le measurable_const (by fun_prop)

/-- A single gated block is a one-switch schedule, and its schedule flow map is the block's own
characteristic flow (`flowMap [b] t = b.blockFlow t`, definitionally). -/
theorem flowMap_singleton_gatedBlock {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ} (hcosR : -1 ≤ cosR)
    {T : ℝ} (hT : 0 ≤ T) :
    flowMap [gatedBlock hω hω hcosR hT] T = (gatedBlock hω hω hcosR hT).blockFlow T := rfl

/-- **Mass retention of the self-centered gated flow (eq. B.8, self-centered case).** For `z = ω`, the
one-block schedule `θ = [gatedBlock …]` (so `switches θ = 1`) transports at least the full mass of the
closed sub-cap `{ x ∈ 𝕊 | m ≤ ⟪x,ω⟫ }` into the target cap `{ y | b ≤ ⟪y,ω⟫ }`, under the same rim
budget `logOdds b ≤ logOdds m + 2·(m - cos R)·T` and active-region condition `cos R < m < 1` that make
`gatedBlock_mapsTo_cap` fire. This composes the point-set reaching (`gatedBlock_mapsTo_cap`) with the
pushforward-monotonicity bridge (`Axioms.le_measureFlow_of_mapsTo`): every point of the source cap
flows into the target, so the target's transported mass is at least the source's original mass. It is
the self-centered core of B.8; the `(1-ε)` open-cap version follows by prefixing eq. B.6
(`exists_closed_sublevel_mass_ge`). -/
theorem gatedBlock_measureFlow_cap_retention {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {m b : ℝ} (hmR : cosR < m) (hm1 : m < 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (hreach : logOdds b ≤ logOdds m + 2 * (m - cosR) * T)
    (μ : Measure (Eucl d)) :
    μ {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)}
      ≤ Axioms.measureFlow [gatedBlock hω hω hcosR hT] T μ {y | b ≤ (⟪y, ω⟫ : ℝ)} := by
  have hmaps : Set.MapsTo (flowMap [gatedBlock hω hω hcosR hT] T)
      {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)} {y | b ≤ (⟪y, ω⟫ : ℝ)} := by
    rw [flowMap_singleton_gatedBlock]
    exact gatedBlock_mapsTo_cap hω hcosR hT hmR hm1 hb hreach
  exact Axioms.le_measureFlow_of_mapsTo [gatedBlock hω hω hcosR hT] hT μ
    (measurableSet_inner_ge ω b) hmaps

end MeasureToMeasure
