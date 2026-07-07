import MeasureToMeasure.Leaves.GatedFlow
import MeasureToMeasure.Leaves.GatedPark

/-!
# Leaf (Lemma 3.4 Part 1, Path I): the non-self-centered gated reach

`gatedBlock_reach` (`Leaves/GatedFlow.lean`) drives the sphere point `x` toward the pole `ω`, but only
in the **self-centered** case `z = ω` (gate direction = pole): there `u = ⟪Φ_t x, ω⟫` increases
monotonically, so the gate `g(t) = (u - cos R)₊` stays above its start `⟪x,ω⟫ - cos R`.

The App. B.3 Part 1 separation needs the **non-self-centered** block: gate on a fixed cap
`{⟪z,·⟫ > cos R}` (where two measures differ) and collapse toward a *separate* pole `ω = x*` chosen by
the pigeonhole. Here `v = ⟪z, Φ_t x⟫` is no longer monotone, so keeping the gate active needs a
**barrier**: `d/dt v = g·(⟪z,ω⟫ − ⟪Φ,ω⟫·v)`, and whenever `v ≤ m` this is `≥ 0` — if `v ≤ cos R` the
gate is off so `v' = 0`, and if `cos R < v ≤ m` then `⟪z,ω⟫ − ⟪Φ,ω⟫·v ≥ ⟪z,ω⟫ − v ≥ ⟪z,ω⟫ − m > 0`
(taking `⟪z,ω⟫ > m`, `⟪Φ,ω⟫ ≤ 1`, `v ≥ 0`). So from `⟪z,x⟫ ≥ m`, `v` cannot decrease through `m`, i.e.
`v ≥ m` on `[0,T]`. That gives the uniform gate bound `g ≥ m − cos R`, and the *same*
`logistic_flow_reach` engine then drives `⟪Φ_T x, ω⟫` up to any `b < 1`.
-/

namespace MeasureToMeasure

open Set
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **The gate-coordinate ODE (non-self-centered).** Along the gated flow, the gate coordinate
`v(t) = ⟪z, Φ_t x⟫` evolves as `v'(t) = gateFactor(Φ_t x)·(⟪z,ω⟫ − ⟪Φ_t x, ω⟫·⟪z, Φ_t x⟫)`. The
derivative of `⟪z, ·⟫` (not the pole `ω`) along the flow whose drift points toward `ω`. -/
theorem hasDerivAt_inner_gate_gatedFlow {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {x : Eucl d} {t : ℝ} :
    HasDerivAt (fun s => (⟪z, (gatedBlock hz hω hcosR hT).blockFlow s x⟫ : ℝ))
      (gateFactor z cosR ((gatedBlock hz hω hcosR hT).blockFlow t x)
        * ((⟪z, ω⟫ : ℝ) - ⟪(gatedBlock hz hω hcosR hT).blockFlow t x, ω⟫
            * ⟪z, (gatedBlock hz hω hcosR hT).blockFlow t x⟫)) t := by
  set B := gatedBlock hz hω hcosR hT with hB
  have hcurve : HasDerivAt (B.blockCurve x) (B.field (B.blockCurve x t)) t :=
    B.blockCurve_isIntegralCurve x t
  have hconst : HasDerivAt (fun _ : ℝ => z) (0 : Eucl d) t := hasDerivAt_const t z
  have h := hconst.inner ℝ hcurve
  have hval : (⟪z, B.field (B.blockCurve x t)⟫ : ℝ) + ⟪(0 : Eucl d), B.blockCurve x t⟫
      = gateFactor z cosR (B.blockFlow t x)
        * ((⟪z, ω⟫ : ℝ) - ⟪B.blockFlow t x, ω⟫ * ⟪z, B.blockFlow t x⟫) := by
    show (⟪z, gatedField z ω cosR (B.blockCurve x t)⟫ : ℝ) + ⟪(0 : Eucl d), B.blockCurve x t⟫ = _
    rw [inner_zero_left, add_zero, gatedField, real_inner_smul_right, tangentialProjector_apply,
      inner_sub_right, real_inner_smul_right]
    rfl
  rw [hval] at h
  exact h

/-- **The gate barrier (non-self-centered).** If the pole `ω` sits strictly inside the closed sub-cap
`{⟪z,·⟫ ≥ m}` (`m < ⟪z,ω⟫`, `cos R < m`, `0 ≤ cos R`) and `x` starts in it (`m ≤ ⟪z,x⟫`), the flow
never leaves it: `m ≤ ⟪z, Φ_t x⟫` for all `t ∈ [0,T]`. Because `v = ⟪z,Φ⟫` has `v' ≥ 0` wherever
`v ≤ m` (gate off below `cos R`; and `⟪z,ω⟫ − ⟪Φ,ω⟫·v ≥ ⟪z,ω⟫ − m > 0` on `(cos R, m]`), so at the
last time `v` equals `m` its derivative is `> 0` — `v` cannot descend below `m`. This is what keeps
the gate active for the collapse toward the separate pole `ω`. -/
theorem inner_gate_gatedFlow_ge {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) (hcosR0 : 0 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {m : ℝ}
    (hzω : m < (⟪z, ω⟫ : ℝ))
    {x : Eucl d} (hxs : x ∈ sphere d) (hne : x ≠ ω) (hne' : x ≠ -ω) (hxm : m ≤ (⟪z, x⟫ : ℝ)) :
    ∀ t ∈ Icc (0 : ℝ) T, m ≤ (⟪z, (gatedBlock hz hω hcosR hT).blockFlow t x⟫ : ℝ) := by
  set B := gatedBlock hz hω hcosR hT with hB
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  set v : ℝ → ℝ := fun t => (⟪z, B.blockFlow t x⟫ : ℝ) with hv
  have hderiv : ∀ t, HasDerivAt v
      (gateFactor z cosR (B.blockFlow t x) * ((⟪z, ω⟫ : ℝ) - ⟪B.blockFlow t x, ω⟫ * v t)) t :=
    fun t => hasDerivAt_inner_gate_gatedFlow hz hω hcosR hT (x := x) (t := t)
  have hcont : Continuous v := continuous_iff_continuousAt.mpr (fun t => (hderiv t).continuousAt)
  -- `v' ≥ 0` wherever `v ≤ m` (for `t ≥ 0`)
  have hnonneg : ∀ t, 0 ≤ t → v t ≤ m →
      0 ≤ gateFactor z cosR (B.blockFlow t x) * ((⟪z, ω⟫ : ℝ) - ⟪B.blockFlow t x, ω⟫ * v t) := by
    intro t ht0 hvm
    rcases le_total (v t) cosR with hle | hge
    · have hle' : (⟪z, B.blockFlow t x⟫ : ℝ) ≤ cosR := hle
      rw [gateFactor_eq_zero_of_inner_le hle', zero_mul]
    · have hflowsph : B.blockFlow t x ∈ sphere d := B.blockFlow_mem_sphere hxs ht0
      have hu1 : (⟪B.blockFlow t x, ω⟫ : ℝ) ≤ 1 :=
        (inner_gatedFlow_mem_Ioo hωs cosR B rfl hxs hne hne' ht0).2.le
      have hv0 : (0 : ℝ) ≤ v t := le_trans hcosR0 hge
      refine mul_nonneg (gateFactor_nonneg z cosR _) ?_
      nlinarith [hu1, hv0, hvm, hzω, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (⟪B.blockFlow t x, ω⟫ : ℝ)) hv0]
  -- barrier by contradiction
  intro t₁ ht₁
  by_contra hcon
  rw [not_le] at hcon
  set S := {s : ℝ | s ∈ Icc 0 t₁ ∧ m ≤ v s} with hSdef
  have hv0m : m ≤ v 0 := by rw [hv]; simpa [B.blockFlow_zero] using hxm
  have hSne : S.Nonempty := ⟨0, ⟨le_rfl, ht₁.1⟩, hv0m⟩
  have hSbdd : BddAbove S := ⟨t₁, fun s hs => hs.1.2⟩
  have hScl : IsClosed S := by
    have hSeq : S = Icc 0 t₁ ∩ v ⁻¹' Ici m := by
      ext s; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
    rw [hSeq]; exact isClosed_Icc.inter (isClosed_Ici.preimage hcont)
  set s := sSup S with hsdef
  have hsS : s ∈ S := hScl.csSup_mem hSne hSbdd
  have hs_le : s ≤ t₁ := csSup_le hSne (fun w hw => hw.1.2)
  have hs_lt : s < t₁ :=
    lt_of_le_of_ne hs_le (fun heq => absurd (heq ▸ hsS.2) (not_le.mpr hcon))
  have hs0 : 0 ≤ s := hsS.1.1
  -- `v s = m`: `≥ m` from `s ∈ S`; `≤ m` since `v > m` just above `s` would enlarge `S`
  have hvs_le : v s ≤ m := by
    by_contra hgt
    rw [not_le] at hgt
    have hev : ∀ᶠ w in nhdsWithin s (Ioi s), m < v w :=
      (hcont.continuousAt.eventually (lt_mem_nhds hgt)).filter_mono nhdsWithin_le_nhds
    have hev2 : ∀ᶠ w in nhdsWithin s (Ioi s), w < t₁ :=
      (gt_mem_nhds hs_lt).filter_mono nhdsWithin_le_nhds
    obtain ⟨w, ⟨hwv, hwlt⟩, hws⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
    have hwsl : s < w := hws
    have hwS : w ∈ S := ⟨⟨le_trans hs0 hwsl.le, hwlt.le⟩, hwv.le⟩
    exact absurd (le_csSup hSbdd hwS) (not_le.mpr hwsl)
  -- `v ≤ m` on `[s, t₁]`
  have hvle : ∀ w ∈ Icc s t₁, v w ≤ m := by
    intro w hw
    rcases eq_or_lt_of_le hw.1 with h | h
    · rw [← h]; exact hvs_le
    · by_contra hvw
      rw [not_le] at hvw
      exact absurd (le_csSup hSbdd ⟨⟨le_trans hs0 hw.1, hw.2⟩, hvw.le⟩) (not_le.mpr h)
  -- `v` is monotone on `[s, t₁]`, so `m ≤ v s ≤ v t₁`, contradicting `v t₁ < m`
  have hmono : MonotoneOn v (Icc s t₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc s t₁) hcont.continuousOn
      (fun w _ => (hderiv w).differentiableAt.differentiableWithinAt) (fun w hw => ?_)
    rw [interior_Icc] at hw
    rw [(hderiv w).deriv]
    exact hnonneg w (le_trans hs0 hw.1.le) (hvle w ⟨hw.1.le, hw.2.le⟩)
  have hle := hmono (left_mem_Icc.mpr hs_le) (right_mem_Icc.mpr hs_le) hs_le
  linarith [hsS.2, hle]

/-- **Non-self-centered gated reach.** With the pole `ω` strictly inside the closed sub-cap
`{⟪z,·⟫ ≥ m}` (`cos R < m < ⟪z,ω⟫`, `0 ≤ cos R`), the gate stays active along the whole flow (barrier
`inner_gate_gatedFlow_ge`), so the *same* logistic reaching estimate as the self-centered case drives
`⟪Φ_T x, ω⟫` up to any `b < 1` under the rim budget `logOdds b ≤ logOdds ⟪x,ω⟫ + 2(m − cos R)T`. This
is `gatedBlock_reach` with the gate lower bound coming from the barrier instead of self-centering. -/
theorem gatedBlock_offCenter_reach {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) (hcosR0 : 0 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {m b : ℝ}
    (hzω : m < (⟪z, ω⟫ : ℝ))
    (hb : b ∈ Ioo (-1 : ℝ) 1) {x : Eucl d} (hxs : x ∈ sphere d) (hne : x ≠ ω) (hne' : x ≠ -ω)
    (hxm : m ≤ (⟪z, x⟫ : ℝ))
    (hreach : logOdds b ≤ logOdds (⟪x, ω⟫ : ℝ) + 2 * (m - cosR) * T) :
    b ≤ (⟪(gatedBlock hz hω hcosR hT).blockFlow T x, ω⟫ : ℝ) := by
  set B := gatedBlock hz hω hcosR hT with hB
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  have hbar := inner_gate_gatedFlow_ge hz hω hcosR hcosR0 hT hzω hxs hne hne' hxm
  refine logistic_flow_reach hT (u := fun s => (⟪B.blockFlow s x, ω⟫ : ℝ))
    (g := fun s => gateFactor z cosR (B.blockFlow s x)) (c₀ := m - cosR) ?_ ?_ ?_ hb ?_
  · exact fun t ht => gatedBlock_hasDerivAt_inner hz hω hcosR hT hxs ht.1
  · exact fun t ht => inner_gatedFlow_mem_Ioo hωs cosR B rfl hxs hne hne' ht.1
  · intro t ht
    have hv := hbar t ht
    have hflowsph : B.blockFlow t x ∈ sphere d := B.blockFlow_mem_sphere hxs ht.1
    rw [gateFactor_eq_reluGate_of_mem_sphere cosR hflowsph, reluGate]
    calc m - cosR ≤ (⟪z, B.blockFlow t x⟫ : ℝ) - cosR := by linarith
      _ ≤ max 0 ((⟪z, B.blockFlow t x⟫ : ℝ) - cosR) := le_max_right _ _
  · simpa only [B.blockFlow_zero] using hreach

end MeasureToMeasure
