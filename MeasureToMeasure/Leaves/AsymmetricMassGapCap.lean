import MeasureToMeasure.Foundations.Sphere
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# A pushed-forward measure's support puts positive mass in any cap containing its image (phase4)

A standalone continuity fact, independent of the paper's own gates: if `x0` lies in the support of
`μ` and `Φ` is continuous, then `Φ x0` cannot be missed by the pushed-forward measure `μ.map Φ` on
any open spherical cap `{cos R < ⟪z, ·⟫}` containing it. This is the generic engine behind the
`IsMeanFieldFlow` continuity fields (`Foundations/Attention.lean`'s `lipschitz`/`sphere_bijOn`
carry exactly this Lipschitz/continuity content for the flow map `Φ t`), stated here with only bare
continuity and measurability hypotheses so it applies uniformly to every time slice.

**Proof idea.** The cap is an open half-space intersected with nothing else (a strict inequality
sublevel set of the continuous linear functional `⟪z, ·⟫`), hence open. Continuity of `Φ` pulls this
back to an open neighborhood of `x0` (since `hmem` puts `Φ x0`, hence `x0`, inside the pulled-back
cap). Membership of `x0` in `μ.support` means every open neighborhood of `x0` carries positive
`μ`-mass (`Measure.mem_support_iff_forall`), so the pulled-back cap does. `Measure.map_apply`
transports this positive mass across the pushforward to the cap itself.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Cap positivity under pushforward.** If `x0` is in the support of `μ` and `Φ` is continuous and
measurable, then `Φ x0` lying strictly inside a spherical cap `{cos R < ⟪z, ·⟫}` forces the
pushed-forward measure `μ.map Φ` to give that cap positive mass. -/
theorem cap_pos_mass_of_mem_support {μ : Measure (Eucl d)} {Φ : Eucl d → Eucl d}
    (hΦcont : Continuous Φ) (hΦmeas : Measurable Φ) {x0 : Eucl d} (hx0 : x0 ∈ μ.support)
    {z : Eucl d} {cosR : ℝ} (hmem : cosR < (⟪z, Φ x0⟫ : ℝ)) :
    0 < (μ.map Φ) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} := by
  set cap : Set (Eucl d) := {x | cosR < (⟪z, x⟫ : ℝ)} with hcapdef
  have hcapopen : IsOpen cap := by
    have hcont : Continuous (fun x : Eucl d => (⟪z, x⟫ : ℝ)) := continuous_const.inner continuous_id
    simpa [hcapdef] using isOpen_lt continuous_const hcont
  have hpreopen : IsOpen (Φ ⁻¹' cap) := hcapopen.preimage hΦcont
  have hx0mem : x0 ∈ Φ ⁻¹' cap := by simpa [hcapdef] using hmem
  have hnhds : Φ ⁻¹' cap ∈ nhds x0 := hpreopen.mem_nhds hx0mem
  have hpos : 0 < μ (Φ ⁻¹' cap) := (Measure.mem_support_iff_forall x0).mp hx0 _ hnhds
  rw [Measure.map_apply hΦmeas hcapopen.measurableSet]
  exact hpos

end MeasureToMeasure.Leaves
