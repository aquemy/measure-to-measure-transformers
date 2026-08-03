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

The second leaf, `staged_prefix_of_separated_caps`, is the Phase-1 engine itself: caps are
processed in index order, one staging step each, and the MERGE-TOLERANT invariant replaces
per-cap bystander separation. Each processed cell's mass occupies a SINGLE staging ball at any
time (initially its own cap's, hopping only to same-piece sibling balls under the `hsep`
dichotomy), so every step handles every tracked unit through exactly one conjunct of the staging
step and no mixed-support decomposition is ever needed. The public conclusion forgets the
tracked index into the same-label staging-ball union, which is what a downstream Phase 2
consumes; off-gate mass is fixed EXACTLY, and the total duration is exactly `L * τ`.
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
        supportedIn ν F → attnMeasureFlow [p] ν = ν) ∧
      ∃ f : Eucl d → Eucl d, Measurable f ∧ Set.MapsTo f (sphere d) (sphere d) ∧
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          attnMeasureFlow [p] ν = ν.map f := by
  have hcn : ‖c‖ = 1 := by
    rw [sphere, Metric.mem_sphere, dist_zero_right] at hc
    exact hc
  set cosR : ℝ := 1 - b ^ 2 / 2 with hcosRdef
  set m : ℝ := 1 - a ^ 2 / 2 with hmdef
  have hcosR : (-1 : ℝ) ≤ cosR := by rw [hcosRdef]; nlinarith
  have hm : cosR < m := by rw [hcosRdef, hmdef]; nlinarith
  have hm1 : m < 1 := by rw [hmdef]; nlinarith
  obtain ⟨p, hpdur, hpcol, hpfix, _hpS, hpmap⟩ :=
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
  refine ⟨p, hpdur, ?_, fun ν hprob => hfix' ν hprob, ?_, hpmap⟩
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

/-- **The merge-tolerant staging induction: every cell's mass lands in its piece's staging-ball
union, off-cap mass exactly fixed, total duration exactly `L * τ`.** Caps are processed in index
order, one `exists_staging_collapse_step` block each. The carried data per cap `k`: an on-sphere
centre `c k`, collapse radius `a k`, gate radius `b k`, a piece label `lab k`, and a cell `E k`
inside the collapse ball that misses every EARLIER gate (`hEavoid`), so cell mass is literally
fixed until its own cap fires. The separation dichotomy `hsep` is the merge tolerance: each
earlier staging ball is, with a `ρ`-margin, either wholly inside a later cap's collapse ball AND
of the same piece (same-piece capture: the mass hops to the sibling's staging ball, which shares
the piece's eventual target) or wholly off the later cap's gate ball (fixed). Staged mass
therefore always occupies a SINGLE staging ball, so every step handles it by exactly one conjunct
of the staging step, and no mixed-support decomposition is ever needed: this is the invariant
that replaces per-cap bystander separation.

The induction carries, for each processed cell, the index of the staging ball currently holding
its mass (same label, monotone under hops), plus the accumulated-gate fixing clause; the public
conclusion forgets the index into the same-label union, which is what Phase 2 consumes. -/
theorem staged_prefix_of_separated_caps {ι : Type*} {L : ℕ}
    (c : Fin L → Eucl d) (hc : ∀ k, c k ∈ sphere d) (lab : Fin L → ι)
    (a b : Fin L → ℝ) (ha : ∀ k, 0 < a k) (hab : ∀ k, a k < b k) (hb2 : ∀ k, b k ≤ 2)
    (E : Fin L → Set (Eucl d)) (hE : ∀ k, E k ⊆ Metric.closedBall (c k) (a k))
    (hEavoid : ∀ j k : Fin L, j < k → Disjoint (E k) (Metric.ball (c j) (b j)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsep : ∀ j k : Fin L, j < k →
      (lab j = lab k ∧ dist (c j) (c k) + ρ ≤ a k) ∨ b k + ρ ≤ dist (c j) (c k))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = (L : ℝ) * τ ∧
      (∀ k : Fin L, ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] →
        supportedIn ν (sphere d) → supportedIn ν (E k) →
        supportedIn (attnMeasureFlow θ ν)
          (⋃ j ∈ {j : Fin L | lab j = lab k}, Metric.ball (c j) ρ)) ∧
      (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        (∀ j : Fin L, ν (Metric.ball (c j) (b j)) = 0) → attnMeasureFlow θ ν = ν) ∧
      ∃ f : Eucl d → Eucl d, Measurable f ∧ Set.MapsTo f (sphere d) (sphere d) ∧
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          attnMeasureFlow θ ν = ν.map f := by
  have key : ∀ K : ℕ, K ≤ L → ∃ θ : AttnSchedule d,
      AttnSchedule.durationSum θ = (K : ℝ) * τ ∧
      (∀ k : Fin L, (k : ℕ) < K → ∃ j : Fin L, (j : ℕ) < K ∧ lab j = lab k ∧
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] →
          supportedIn ν (sphere d) → supportedIn ν (E k) →
          supportedIn (attnMeasureFlow θ ν) (Metric.ball (c j) ρ)) ∧
      (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        (∀ j : Fin L, (j : ℕ) < K → ν (Metric.ball (c j) (b j)) = 0) →
        attnMeasureFlow θ ν = ν) ∧
      ∃ f : Eucl d → Eucl d, Measurable f ∧ Set.MapsTo f (sphere d) (sphere d) ∧
        ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
          attnMeasureFlow θ ν = ν.map f := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨[], by simp, ?_, ?_, id, measurable_id, Set.mapsTo_id _, ?_⟩
      · intro k hk
        exact absurd hk (Nat.not_lt_zero _)
      · intro ν _ _ _
        rfl
      · intro ν _ _
        exact (Measure.map_id).symm
    | succ K ih =>
      intro hK1
      have hKL : K < L := hK1
      obtain ⟨θ, hθdur, hP1, hP2, f₀, hf₀m, hf₀to, hf₀map⟩ := ih (Nat.le_of_lt hKL)
      set kK : Fin L := ⟨K, hKL⟩ with hkKdef
      have hkKval : (kK : ℕ) = K := rfl
      obtain ⟨p, hpdur, hpcol, hpfix, hpfixF, fp, hfpm, hfpto, hfpmap⟩ :=
        exists_staging_collapse_step (hc kK) (ha kK) (hab kK) (hb2 kK) hτ hρ
      refine ⟨θ ++ [p], ?_, ?_, ?_, fp ∘ f₀, hfpm.comp hf₀m, hfpto.comp hf₀to, ?_⟩
      · rw [AttnSchedule.durationSum_append, hθdur]
        have hsing : AttnSchedule.durationSum [p] = p.duration := by
          simp [AttnSchedule.durationSum]
        rw [hsing, hpdur]
        push_cast
        ring
      · -- the staging invariant
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkK | hkK
        · -- previously staged mass: dichotomy of cap K against its current staging ball
          obtain ⟨j, hjK, hjlab, hjcol⟩ := hP1 k hkK
          have hjkK : j < kK := by
            rw [Fin.lt_def, hkKval]
            exact hjK
          rcases hsep j kK hjkK with ⟨hlabjk, hdist⟩ | hdist
          · -- same-piece capture: the whole staging ball sits inside cap K's collapse ball
            refine ⟨kK, by rw [hkKval]; exact Nat.lt_succ_self K, by rw [← hlabjk]; exact hjlab,
              ?_⟩
            intro ν _hprob hνs hνE
            haveI : IsProbabilityMeasure (attnMeasureFlow θ ν) :=
              isProbabilityMeasure_attnMeasureFlow θ ν hνs
            have hν's : supportedIn (attnMeasureFlow θ ν) (sphere d) :=
              attnMeasureFlow_supportedIn_sphere θ ν hνs
            have hballsup : supportedIn (attnMeasureFlow θ ν) (Metric.ball (c j) ρ) :=
              hjcol ν hνs hνE
            have hclosed : supportedIn (attnMeasureFlow θ ν)
                (Metric.closedBall (c kK) (a kK)) := by
              refine supportedIn_mono (fun x hx => ?_) hballsup
              rw [Metric.mem_ball] at hx
              rw [Metric.mem_closedBall]
              have htri := dist_triangle x (c j) (c kK)
              linarith
            rw [attnMeasureFlow_append]
            exact hpcol (attnMeasureFlow θ ν) hν's hclosed
          · -- avoidance: the staging ball misses cap K's gate, so its mass is fixed
            refine ⟨j, Nat.lt_succ_of_lt hjK, hjlab, ?_⟩
            intro ν _hprob hνs hνE
            haveI : IsProbabilityMeasure (attnMeasureFlow θ ν) :=
              isProbabilityMeasure_attnMeasureFlow θ ν hνs
            have hν's : supportedIn (attnMeasureFlow θ ν) (sphere d) :=
              attnMeasureFlow_supportedIn_sphere θ ν hνs
            have hballsup : supportedIn (attnMeasureFlow θ ν) (Metric.ball (c j) ρ) :=
              hjcol ν hνs hνE
            have hdisj : Disjoint (Metric.ball (c j) ρ) (Metric.ball (c kK) (b kK)) := by
              rw [Set.disjoint_left]
              intro x hxj hxK
              rw [Metric.mem_ball] at hxj hxK
              have htri := dist_triangle (c j) x (c kK)
              rw [dist_comm (c j) x] at htri
              linarith
            rw [attnMeasureFlow_append,
              hpfixF (Metric.ball (c j) ρ) hdisj (attnMeasureFlow θ ν) hν's hballsup]
            exact hballsup
        · -- the fresh cell: literally fixed so far, then collapsed by cap K's own step
          have hkeq : k = kK := Fin.ext (by rw [hkK, hkKval])
          refine ⟨kK, by rw [hkKval]; exact Nat.lt_succ_self K, by rw [hkeq], ?_⟩
          intro ν _hprob hνs hνE
          have hgates : ∀ j : Fin L, (j : ℕ) < K → ν (Metric.ball (c j) (b j)) = 0 := by
            intro j hj
            have hjk : j < k := by
              rw [Fin.lt_def, hkK]
              exact hj
            exact measure_mono_null
              (fun x hx => Set.disjoint_right.mp (hEavoid j k hjk) hx) hνE
          have hfixed : attnMeasureFlow θ ν = ν := hP2 ν hνs hgates
          have hclosed : supportedIn ν (Metric.closedBall (c kK) (a kK)) := by
            rw [← hkeq]
            exact supportedIn_mono (hE k) hνE
          rw [attnMeasureFlow_append, hfixed]
          exact hpcol ν hνs hclosed
      · -- gate fixing, one more gate absorbed
        intro ν _hprob hνs hνgates
        rw [attnMeasureFlow_append, hP2 ν hνs (fun j hj => hνgates j (Nat.lt_succ_of_lt hj))]
        exact hpfix ν hνs (hνgates kK (by rw [hkKval]; exact Nat.lt_succ_self K))
      · -- the universal transport map composes through the appended block
        intro ν _hprob hνs
        haveI : IsProbabilityMeasure (attnMeasureFlow θ ν) :=
          isProbabilityMeasure_attnMeasureFlow θ ν hνs
        have hν's : supportedIn (attnMeasureFlow θ ν) (sphere d) :=
          attnMeasureFlow_supportedIn_sphere θ ν hνs
        rw [attnMeasureFlow_append, hfpmap (attnMeasureFlow θ ν) hν's, hf₀map ν hνs,
          Measure.map_map hfpm hf₀m]
  obtain ⟨θ, hθdur, hP1, hP2, f, hfm, hfto, hfmap⟩ := key L le_rfl
  refine ⟨θ, hθdur, ?_, fun ν _hprob hνs hg => hP2 ν hνs fun j _ => hg j,
    f, hfm, hfto, hfmap⟩
  intro k ν _hprob hνs hνE
  obtain ⟨j, _hjL, hjlab, hjcol⟩ := hP1 k k.isLt
  refine supportedIn_mono ?_ (hjcol ν hνs hνE)
  exact Set.subset_biUnion_of_mem (u := fun j => Metric.ball (c j) ρ) hjlab

end MeasureToMeasure.Leaves
