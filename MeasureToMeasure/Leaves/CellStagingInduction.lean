import MeasureToMeasure.Leaves.AsymmetricCapCollapse

/-!
# Leaves (lemma 5.4 campaign, G6): Phase-1 staging, cap by cap

Phase 1 of the `lemma_5_4` discharge collapses each cover-cap's carried mass into a tiny staging
ball at its own pole while fixing all off-cap mass. The quantitative engine already exists:
`exists_collapse_block_support_close` (exact duration, universal over carried measures, off-cap
fixing). What it speaks is INNER-PRODUCT cap language (`{x | m ≤ ⟪z, x⟫}` collapse zone,
`{x | cosR < ⟪z, x⟫}` gate), while the G4 cap-cover system (`disjoint_compacts_cap_cover`)
delivers METRIC balls around on-sphere centres. This file's first leaf,
`exists_staging_collapse_step`, is the dictionary: for a centre `c ∈ 𝕊^{d-1}` and radii
`0 < a < b ≤ 2` it restates the engine as

* collapse: every sphere probability measure carried by `Metric.closedBall c a` flows into
  `Metric.ball c ρ` in duration exactly `τ`;
* gate fixing: every sphere probability measure with zero mass on `Metric.ball c b` is fixed;
* avoid-set fixing: every sphere probability measure supported in a set disjoint from
  `Metric.ball c b` is fixed (the closed-avoid-set form the staging induction threads).

The translation is the on-sphere polarization identity `‖x - c‖² = 2 - 2⟪c, x⟫` for unit `x`,
`c`: the closed ball of radius `a` traces the closed sub-cap at level `m = 1 - a²/2`, the open
ball of radius `b` traces the open gate cap at level `cosR = 1 - b²/2`, and `0 < a < b ≤ 2`
is exactly `-1 ≤ cosR < m < 1`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **`supportedIn` is monotone in the carrier.** Mass confined to `S ⊆ T` is confined to `T`.
Tiny glue used throughout the staging induction. -/
theorem supportedIn_mono {μ : Measure (Eucl d)} {S T : Set (Eucl d)}
    (hST : S ⊆ T) (h : supportedIn μ S) : supportedIn μ T :=
  measure_mono_null (Set.compl_subset_compl.mpr hST) h

variable [NeZero d]

/-- **Single staging step, in the metric-ball language of the cap-cover system.** For an on-sphere
centre `c` and radii `0 < a < b ≤ 2`, one attention block `p` of duration EXACTLY `τ` collapses
every sphere probability measure carried by the closed ball `Metric.closedBall c a` into the
staging ball `Metric.ball c ρ`, fixes EXACTLY every sphere probability measure with zero mass on
the open gate ball `Metric.ball c b`, and in particular fixes every sphere probability measure
supported in a set disjoint from the gate ball. Ball-to-cap dictionary over
`exists_collapse_block_support_close` via the polarization identity `‖x - c‖² = 2 - 2⟪c, x⟫` on
the sphere; the collapse level is `m = 1 - a²/2`, the gate level `cosR = 1 - b²/2`. -/
theorem exists_staging_collapse_step {c : Eucl d} (hc : c ∈ sphere d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb2 : b ≤ 2)
    {τ : ℝ} (hτ : 0 < τ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ p : AttnParams d, p.duration = τ ∧
      (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        supportedIn ν (Metric.closedBall c a) →
        supportedIn (attnMeasureFlow [p] ν) (Metric.ball c ρ)) ∧
      (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        ν (Metric.ball c b) = 0 → attnMeasureFlow [p] ν = ν) ∧
      (∀ F : Set (Eucl d), Disjoint F (Metric.ball c b) →
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        supportedIn ν F → attnMeasureFlow [p] ν = ν) := by
  have hcn : ‖c‖ = 1 := by
    rw [sphere, Metric.mem_sphere, dist_zero_right] at hc
    exact hc
  set cosR : ℝ := 1 - b ^ 2 / 2 with hcosRdef
  set m : ℝ := 1 - a ^ 2 / 2 with hmdef
  have hcosR : (-1 : ℝ) ≤ cosR := by rw [hcosRdef]; nlinarith
  have hm : cosR < m := by rw [hcosRdef, hmdef]; nlinarith
  have hm1 : m < 1 := by rw [hmdef]; nlinarith
  obtain ⟨p, hpdur, hpcol, hpfix, _hpS⟩ :=
    exists_collapse_block_support_close (z := c) hcn hcosR hm hm1 hτ hρ
  -- on-sphere ball/cap dictionary, both directions
  have hcap_of_ball : ∀ x : Eucl d, x ∈ sphere d → x ∈ Metric.closedBall c a →
      m ≤ (⟪c, x⟫ : ℝ) := by
    intro x hx hxa
    have hxn : ‖x‖ = 1 := by
      rw [sphere, Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    have hd : ‖x - c‖ ≤ a := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hxa
      exact hxa
    have hsq : ‖x - c‖ ^ 2 = 2 - 2 * (⟪c, x⟫ : ℝ) := by
      rw [norm_sub_sq_real, hxn, hcn, real_inner_comm]
      ring
    have h2 : ‖x - c‖ ^ 2 ≤ a ^ 2 := by
      have := norm_nonneg (x - c)
      nlinarith
    rw [hmdef]
    nlinarith
  have hball_of_cap : ∀ x : Eucl d, x ∈ sphere d → cosR < (⟪c, x⟫ : ℝ) →
      x ∈ Metric.ball c b := by
    intro x hx hxc
    have hxn : ‖x‖ = 1 := by
      rw [sphere, Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    have hsq : ‖x - c‖ ^ 2 = 2 - 2 * (⟪c, x⟫ : ℝ) := by
      rw [norm_sub_sq_real, hxn, hcn, real_inner_comm]
      ring
    rw [Metric.mem_ball, dist_eq_norm]
    rw [hcosRdef] at hxc
    nlinarith [norm_nonneg (x - c), sq_nonneg (‖x - c‖ - b)]
  -- fixing in the zero-gate-mass form
  have hfix' : ∀ ν : Measure (Eucl d), IsProbabilityMeasure ν → supportedIn ν (sphere d) →
      ν (Metric.ball c b) = 0 → attnMeasureFlow [p] ν = ν := by
    intro ν _hprob hνs hνb
    have hcapnull : ν {x : Eucl d | cosR < (⟪c, x⟫ : ℝ)} = 0 := by
      have hsub : {x : Eucl d | cosR < (⟪c, x⟫ : ℝ)} ⊆ (sphere d)ᶜ ∪ Metric.ball c b := by
        intro x hx
        by_cases hxs : x ∈ sphere d
        · exact Set.mem_union_right _ (hball_of_cap x hxs hx)
        · exact Set.mem_union_left _ hxs
      exact measure_mono_null hsub (measure_union_null hνs hνb)
    exact hpfix ν hνs hcapnull
  refine ⟨p, hpdur, ?_, fun ν hprob => hfix' ν hprob, ?_⟩
  · -- collapse: closed-ball support is closed-sub-cap support
    intro ν _hprob hνs hνa
    have hsub : supportedIn ν {x : Eucl d | m ≤ (⟪c, x⟫ : ℝ)} := by
      have hcsub : {x : Eucl d | m ≤ (⟪c, x⟫ : ℝ)}ᶜ ⊆ (sphere d)ᶜ ∪ (Metric.closedBall c a)ᶜ := by
        intro x hx
        by_cases hxs : x ∈ sphere d
        · exact Set.mem_union_right _ fun hxa => hx (hcap_of_ball x hxs hxa)
        · exact Set.mem_union_left _ hxs
      exact measure_mono_null hcsub (measure_union_null hνs hνa)
    exact hpcol ν hνs hsub
  · -- avoid-set fixing: support disjoint from the gate ball means zero gate mass
    intro F hF ν hprob hνs hνF
    have hνb : ν (Metric.ball c b) = 0 :=
      measure_mono_null (fun x hx => Set.disjoint_right.mp hF hx) hνF
    exact hfix' ν hprob hνs hνb

end MeasureToMeasure.Leaves
