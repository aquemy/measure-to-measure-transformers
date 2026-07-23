import MeasureToMeasure.Foundations.Sphere
import MeasureToMeasure.Leaves.SharedBoundaryPointNondegenerate
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

open MeasureTheory MeasureToMeasure.Statements MeasureToMeasure.Foundations
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

/-!
## The whole-cap consequence of the single-point divergence (`phase4_asymmetric_massgap_cap`, G3)

Appendix B.3 (arXiv:2411.04551v3), p.36, Proof of Lemma 3.4 Part 2, proves that the trajectories
from the shared non-degenerate boundary point (`exists_shared_boundary_point_nondegenerate`, PR
#276) diverge by a genuine positive margin at some `τ0 ∈ (0,T]`
(`exists_Tstar_margin_pos`, PR #277: `0 < ‖Φμ τ0 x0 - Φν τ0 x0‖`). The paper's own next step (eq.
(B.16)) upgrades this SINGLE-POINT fact to a WHOLE-CAP one: an open ball `B` misses one flowed
support entirely while meeting the other. As printed, verbatim:

> `𝐵 ∩ supp 𝜈(𝑇*) ̸= ∅,   𝐵 ∩ supp 𝜇(𝑇*) = ∅`                                              (B.16)

**Label-swap correction.** As printed, (B.16) contradicts the SAME PAGE's immediately preceding
sentence: "Consequently for `𝑇*` small enough, we have `supp 𝜈(𝑇*) ⊂ supp 𝜇(𝑇*)` as well as
`supp 𝜇(𝑇*) ̸= supp 𝜈(𝑇*)`" (p.36) -- a PROPER inclusion of `supp ν(T*)` inside `supp μ(T*)`. If
`supp ν(T*) ⊆ supp μ(T*)`, no open ball can meet `supp ν(T*)` while missing `supp μ(T*)` entirely:
any point witnessing `B ∩ supp ν(T*) ≠ ∅` is itself a point of `supp μ(T*)` too, forcing
`B ∩ supp μ(T*) ≠ ∅`, contradicting the printed second clause. So (B.16) as printed is inconsistent
with the sentence that derives it. Swapping the `μ`/`ν` labels resolves this exactly: the corrected
reading is `B ∩ supp μ(T*) ≠ ∅`, `B ∩ supp ν(T*) = ∅` -- precisely what the proper inclusion
licenses (pick `B` around a point of `supp μ(T*) \ supp ν(T*)`, nonempty since the inclusion is
proper). Three independent re-derivations from the paper's own surrounding argument agree on this
correction (recorded during this campaign's paper-fidelity pass); the axiom below states the
corrected (swapped) form directly, phrased at the level of the pushed-forward MEASURE rather than
raw topological supports (`(ν0.map (Φν τ0)) cap = 0` is the measure-theoretic reading of
`B ∩ supp ν(T*) = ∅` for `B` an open cap: `Measure.subset_compl_support_of_isOpen` runs this exact
support-to-measure translation elsewhere in this file's sibling `Regression.Refuted` lemma).

**Why this is an axiom, not a theorem.** `cap_pos_mass_of_mem_support` above already supplies the
"positive-mass-for-μ" half unconditionally: any cap containing the μ-flowed image of a support
point gets positive `μ`-pushforward mass, by bare continuity, no dynamics needed. The missing,
genuinely dynamical half is that the SAME cap is `ν`-null: this needs control over where EVERY
OTHER point of `ν0`'s support ends up under `Φν`, not just the single distinguished point `x0`. The
paper asserts this whole-cap consequence follows from the single-point margin "by continuity" (the
sentence immediately preceding (B.16)) but gives no further constructive argument for why the
ENTIRE cap, not just the divergence point, stays `ν`-clear. Mathlib has no machinery connecting a
single-point ODE-trajectory divergence to a whole-neighborhood measure-null statement for a general
(non-explicit) mean-field flow, so this residual step is recorded here as an axiom rather than
derived. It reuses the exact `x0`/`τ0` SHAPE already constructed by
`exists_shared_boundary_point_nondegenerate` / `exists_Tstar_margin_pos` (same non-degenerate
boundary point, same margin time window) instead of re-existentially-quantifying them; `hsupp`
matches the paper's own Part 2 scoping verbatim (its construction of (B.16) runs specifically under
"if (B.15) [`supp μ0 ≠ supp ν0`] is not satisfied", i.e. under `supp μ0 = supp ν0`).

**Degenerate-instantiation attack (scratch, before admission).** `μ0 := ν0` is structurally
excluded by `hcol`/`hνnz`/`hγ1` alone (`b = γ1 • b` with `γ1 ≠ 1` forces `b = 0`), independent of
any measure-theoretic content; checked directly over an abstract module. `d = 1` makes
`[NoAtoms μ0]` together with `supportedIn μ0 (sphere 1)` and `[IsProbabilityMeasure μ0]` jointly
UNSATISFIABLE (`sphere 1` is the two-point set `{1,-1}`, hence `μ0`-null under `NoAtoms`, yet must
carry full `μ0`-mass); checked directly (`Set.Finite.measure_zero` on the two-point preimage).
`d = 0` is excluded outright by `[NeZero d]`. Zero/infinite measure do not arise: `μ0`/`ν0` are
fixed at total mass `1` by `[IsProbabilityMeasure ·]`. Off-sphere points cannot arise either: the
existential witness `x0` is required to lie in `μ0.support ⊆ sphere d` (`hμs` plus closedness of
the sphere). None of these attacks produces a compiling `False`; no refutation found.

**Model adequacy.** The formal class this axiom quantifies over (sphere-supported, atomless-`μ0`
probability measures evolving under `IsMeanFieldFlow`/`pAlign`, the same `V = I_d` barycenter-
alignment block used by every sibling leaf in this campaign) is exactly the class the paper's own
Part 2 proof operates in: the `τ0`-window construction, the colinear-barycenter hypothesis
`hcol`/`hγ1`, and the shared-support hypothesis `hsupp` all mirror the paper's stated setup with no
narrowing or widening beyond the label-swap correction. What the formal class CANNOT express is the
paper's own missing argument step: a first-order (`O(τ)`) trajectory-separation estimate at one
point does not, by any machinery current in this repository or in Mathlib, propagate to a whole-
neighborhood non-vacuity/nullity statement for a measure-dependent (mean-field) flow; that gap is
exactly what admitting this as an axiom, rather than forcing a proof, records honestly.
-/

/-- **Corrected (B.16): a whole cap around the μ-flowed boundary point is `ν`-null.** Building on
the shared non-degenerate boundary point and positive divergence margin
(`exists_shared_boundary_point_nondegenerate` / `exists_Tstar_margin_pos`), there is a spherical cap
of angular radius `arccos cosR < π/3` centered at `Φμ τ0 x0` that the `ν0`-pushforward at the SAME
time `τ0` entirely misses. See the module docstring above for the source anchor (Appendix B.3, eq.
(B.16), p.36), the label-swap correction, and the degenerate-instantiation attack. -/
axiom exists_cap_nu_mass_zero_at_shared_boundary {d : ℕ} [NeZero d] {μ0 ν0 : Measure (Eucl d)}
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure ν0] [NoAtoms μ0]
    (hμs : supportedIn μ0 (sphere d)) (hνs : supportedIn ν0 (sphere d))
    (hsupp : μ0.support = ν0.support)
    (hμint : Integrable (fun x : Eucl d => x) μ0) (hνint : Integrable (fun x : Eucl d => x) ν0)
    {γ1 : ℝ} (hγ1 : γ1 ∈ Set.Ioo (0:ℝ) 1)
    (hcol : barycenter μ0 = γ1 • barycenter ν0) (hνnz : barycenter ν0 ≠ 0)
    {T : ℝ} (hT : 0 < T)
    {Φμ Φν : ℝ → Eucl d → Eucl d}
    (hΦμ : IsMeanFieldFlow (pAlign T hT.le) μ0 Φμ) (hΦν : IsMeanFieldFlow (pAlign T hT.le) ν0 Φν) :
    ∃ x0 : Eucl d, x0 ∈ μ0.support ∧ ∃ τ0 ∈ Set.Ioc (0:ℝ) T, ∃ cosR ∈ Set.Ioo (1/2 : ℝ) 1,
      (ν0.map (Φν τ0)) {x : Eucl d | cosR < (⟪Φμ τ0 x0, x⟫ : ℝ)} = 0

/-! ## The literal target: an asymmetric mass-gap cap (`phase4_asymmetric_massgap_cap`, G4)

Combines `cap_pos_mass_of_mem_support` (positivity, applied at the μ-flowed boundary point itself,
where it holds trivially since `⟪z, z⟫ = ‖z‖² = 1 > cosR`) with
`exists_cap_nu_mass_zero_at_shared_boundary` (the ν-nullity of that same cap) to produce, at a single
witnessed time and cap, a mass split that is strictly positive for `μ0` and exactly zero for `ν0`. -/

/-- **An asymmetric mass-gap cap.** There is a time `Tstar ∈ (0, T]` and a spherical cap of angular
radius `arccos cosR < π/3` centered at some `z ∈ 𝕊^{d-1}` that the `μ0`-pushforward at `Tstar` gives
positive mass, while the `ν0`-pushforward at the SAME `Tstar` gives exactly zero mass. This is the
literal target of the `phase4_asymmetric_massgap_cap` sub-campaign, feeding the caller's `hmassne`
via `ne_of_gt`. -/
theorem exists_asymmetric_massgap_cap {d : ℕ} [NeZero d] {μ0 ν0 : Measure (Eucl d)}
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure ν0] [NoAtoms μ0]
    (hμs : supportedIn μ0 (sphere d)) (hνs : supportedIn ν0 (sphere d))
    (hsupp : μ0.support = ν0.support)
    (hμint : Integrable (fun x : Eucl d => x) μ0) (hνint : Integrable (fun x : Eucl d => x) ν0)
    {γ1 : ℝ} (hγ1 : γ1 ∈ Set.Ioo (0:ℝ) 1)
    (hcol : barycenter μ0 = γ1 • barycenter ν0) (hνnz : barycenter ν0 ≠ 0)
    {T : ℝ} (hT : 0 < T)
    {Φμ Φν : ℝ → Eucl d → Eucl d}
    (hΦμ : IsMeanFieldFlow (pAlign T hT.le) μ0 Φμ) (hΦν : IsMeanFieldFlow (pAlign T hT.le) ν0 Φν) :
    ∃ Tstar ∈ Set.Ioc (0:ℝ) T, ∃ z ∈ sphere d, ∃ cosR ∈ Set.Ioo (1/2:ℝ) 1,
      0 < (μ0.map (Φμ Tstar)) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} ∧
      (ν0.map (Φν Tstar)) {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} = 0 := by
  obtain ⟨x0, hx0, τ0, hτ0, cosR, hcosR, hνzero⟩ :=
    exists_cap_nu_mass_zero_at_shared_boundary hμs hνs hsupp hμint hνint hγ1 hcol hνnz hT hΦμ hΦν
  have hτ0Icc : τ0 ∈ Set.Icc (0:ℝ) (pAlign (d := d) T hT.le).duration := by
    rw [pAlign_duration]; exact ⟨hτ0.1.le, hτ0.2⟩
  have hx0sphere : x0 ∈ sphere d :=
    Measure.support_subset_of_isClosed Metric.isClosed_sphere (mem_ae_iff.mpr hμs) hx0
  have hzsphere : Φμ τ0 x0 ∈ sphere d :=
    (hΦμ.sphere_bijOn τ0 hτ0Icc).mapsTo hx0sphere
  refine ⟨τ0, hτ0, Φμ τ0 x0, hzsphere, cosR, hcosR, ?_, hνzero⟩
  obtain ⟨L, hL⟩ := hΦμ.lipschitz
  have hcont : Continuous (Φμ τ0) := (hL τ0 hτ0Icc).continuous
  have hmeas : Measurable (Φμ τ0) := hΦμ.measurable τ0 hτ0Icc
  have hmem : cosR < (⟪Φμ τ0 x0, Φμ τ0 x0⟫ : ℝ) := by
    rw [inner_self_eq_one_of_mem_sphere hzsphere]
    exact hcosR.2
  exact cap_pos_mass_of_mem_support hcont hmeas hx0 hmem

end MeasureToMeasure.Leaves
