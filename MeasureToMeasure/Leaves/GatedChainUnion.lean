import MeasureToMeasure.Leaves.GatedBallLocalized
import MeasureToMeasure.Axioms.Dynamics

/-!
# Union-tracking ball-chain retention (lemma_B_1, union form, review finding F16)

`lemma_B_1` (`Statements/MidLevel.lean:534`) proves ball-chain retention on `μ ℬ₀` (the mass that
starts in the FIRST ball, funneled forward), not the paper's own `μ (⋃ₖ ℬₖ)` (App. B, Lemma B.1):
its docstring documents why -- the single-ball step `lemma_B_2` (`gated_twoCap_retention`) drops two
clauses the paper's union bound needs: the localization clause "the flow is the identity on
`S^{d-1} ∖ ℬ₀`", and the `|k - k'| ≥ 2 ⟹ disjoint` hypothesis on the chain.

This leaf supplies both. `gated_twoCap_retention_localized` (`Leaves/GatedBallLocalized.lean`,
union-form step 1) already carries the localization clause, faithfully reproducing the paper's own
Lemma B.2 construction (gate centered at the ball's own center, not the overlap point). Adding the
consecutive-overlap chain's `|k - k'| ≥ 2` disjointness hypothesis (`hdisj` below, stated as
`j + 2 ≤ k → Disjoint`, the one-sided form -- `Disjoint` is symmetric, so this covers both orders)
is enough to run a genuine union-tracking induction.

**The induction** (`gated_chainUnion_retention`): unlike the paper's own BACKWARD induction (App. B
p.32, "we proceed by backward induction... `μ(T,ℬ_K) = μ(T,ℬ_K∖ℬ_{K-1}) + μ(T,ℬ_K∩ℬ_{K-1})`"), this
is a FORWARD induction matching the existing `lemma_B_1`'s own structure, with invariant
`(1-ε)^k · μ₀(⋃_{j≤k} ℬⱼ) ≤ μ(t_k, ℬ_k)` PLUS a third conjunct carried alongside it, `flowMap θ T`
is the identity outside `⋃_{j≤k} ℬⱼ` -- the paper's own second Lemma B.1 conclusion, tracked
throughout rather than proved only at the end, because the inductive step needs exactly this fact
about the PREVIOUS step's schedule.

The inductive step splits `ℬ_{k+1} = (ℬ_{k+1} ∩ ℬ_k) ∪ (ℬ_{k+1} ∖ ℬ_k)`: the first piece is
transported by leg `k+1`'s `gated_twoCap_retention_localized` (giving the `(1-ε)^{k+1}` factor via
the IH); the second piece needs `μ(t_k, ℬ_{k+1} ∖ ℬ_k) = μ₀(ℬ_{k+1} ∖ ℬ_k)` EXACTLY. This follows
because `ℬ_{k+1} ∖ ℬ_k` is disjoint from every earlier ball `ℬ_0, …, ℬ_{k-1}` (from `hdisj`, since
`j + 2 ≤ k + 1` for `j ≤ k - 1`) as well as from `ℬ_k` itself (by construction), hence disjoint from
the WHOLE union `⋃_{j≤k} ℬⱼ` -- exactly the set the IH's third conjunct says is fixed pointwise by
`θ`, and leg `k+1`'s own localization clause says is fixed pointwise by `ψ` too (it's disjoint from
`ψ`'s source ball `ℬ_k`). Two applications of `measureFlow_eq_of_flowMap_eqOn` (the pointwise-fixed
+ injective ⟹ pushforward preserves mass exactly fact, built from `Axioms.flowMap_bijective`'s
injectivity and `Set.preimage_image_eq`) give the exact equality; subadditivity plus the ready-made
Mathlib successor-split `Set.biUnion_le_succ` close the induction. The paper's own stated exponent
`(1-ε)^K` (uniform, not a tighter per-piece discount) survives exactly as in the paper.

M3b/mid-level staging: union-form step 2 of strengthening `lemma_B_1` towards `prop_2_2`'s Step 3
(disjoint-ball packing chained to a shared target); see `lemma-b1-b2-union-form-campaign` project
notes. Repeated-chain composition (several disjoint starting balls into one shared target) is the
next step, not yet built.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped ENNReal
open MeasureToMeasure

variable {d : ℕ}

/-- **Pushforward preserves mass exactly on a pointwise-fixed set.** If `flowMap θ T` fixes every
point of `S`, the pushforward measure of `S` equals the original measure of `S` -- not just `≥`, as
the general contraction bound would give, but exact equality, since `flowMap θ T` is injective
(`Axioms.flowMap_bijective`). The route: `f ⁻¹' S = f ⁻¹' (f '' S) = S` (the first step folds `S`
back through its own fixed image, the second is injectivity), then `Measure.map_apply`. -/
theorem measureFlow_eq_of_flowMap_eqOn (θ : Params d) {T : ℝ} (hT : 0 ≤ T) (μ : Measure (Eucl d))
    {S : Set (Eucl d)} (hSmeas : MeasurableSet S) (hfix : ∀ x ∈ S, flowMap θ T x = x) :
    (Axioms.measureFlow θ T μ) S = μ S := by
  have heqon : Set.EqOn (flowMap θ T) id S := hfix
  have himg : (flowMap θ T) '' S = S := heqon.image_eq_self
  have hpre : (flowMap θ T) ⁻¹' S = S := by
    nth_rewrite 1 [← himg]
    exact Set.preimage_image_eq S (flowMap_bijective θ T).injective
  show μ.map (flowMap θ T) S = μ S
  rw [MeasureTheory.Measure.map_apply (measurable_flowMap θ hT) hSmeas, hpre]

/-- **Union-tracking ball-chain retention (`lemma_B_1`, union form).** For a chain of consecutively
overlapping geodesic balls `ℬ_k = B(z_k, R_k)` with the paper's `|k - k'| ≥ 2 ⟹ disjoint` hypothesis
(`hdisj`), `K` switches retain a `(1-ε)^K` fraction of the mass in the WHOLE union `⋃_{j≤K} ℬⱼ`
(not just `ℬ₀`) into the last ball `ℬ_K`, and the flow is exactly the identity outside that union.
Both conjuncts are exactly the paper's own Lemma B.1 conclusion (App. B). -/
theorem gated_chainUnion_retention (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (K : ℕ) (z : ℕ → Eucl d) (hz : ∀ k, z k ∈ sphere d) (R : ℕ → ℝ)
    (hR : ∀ k, R k ∈ Set.Ioo 0 (Real.pi / 2))
    (hchain : ∀ k, (geodesicBall (z k) (R k) ∩ geodesicBall (z (k + 1)) (R (k + 1))).Nonempty)
    (hdisj : ∀ j k, j + 2 ≤ k → Disjoint (geodesicBall (z j) (R j)) (geodesicBall (z k) (R k))) :
    ∃ θ : Params d, switches θ ≤ K ∧
      (1 - ENNReal.ofReal ε) ^ K * μ (⋃ j ≤ K, geodesicBall (z j) (R j)) ≤
        (Axioms.measureFlow θ T μ) (geodesicBall (z K) (R K)) ∧
      ∀ x, x ∈ sphere d → x ∉ ⋃ j ≤ K, geodesicBall (z j) (R j) → flowMap θ T x = x := by
  set c : ℝ≥0∞ := 1 - ENNReal.ofReal ε with hc
  induction K with
  | zero =>
    have hU0 : (⋃ j ≤ 0, geodesicBall (z j) (R j)) = geodesicBall (z 0) (R 0) := by
      ext x; simp
    refine ⟨Axioms.idParams d, ?_, ?_, ?_⟩
    · simp [Axioms.switches_id]
    · rw [hU0]; simp [Axioms.measureFlow_id]
    · intro x hxs hxout
      simp [Axioms.flowMap_id]
  | succ k ih =>
    obtain ⟨θ, hsw, hmass, hfix⟩ := ih
    haveI := Axioms.isProbabilityMeasure_measureFlow θ T μ
    obtain ⟨ψ, hψsw, hψmass, hψfix⟩ :=
      gated_twoCap_retention_localized (Axioms.measureFlow θ T μ) T ε hT hε (z k) (z (k + 1))
        (hz k) (hz (k + 1)) (R k) (R (k + 1)) (hR k) (hR (k + 1)) (hchain k)
    have hBmeas : ∀ j, MeasurableSet (geodesicBall (z j) (R j)) := fun j =>
      measurableSet_geodesicBall (z j) (R j)
    have hUmeas : MeasurableSet (⋃ j ≤ k, geodesicBall (z j) (R j)) :=
      MeasurableSet.biUnion (Set.finite_Iic k).countable (fun j _ => hBmeas j)
    have hdiffmeas : MeasurableSet (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) :=
      (hBmeas (k + 1)).diff (hBmeas k)
    have hintermeas : MeasurableSet
        (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) :=
      (hBmeas (k + 1)).inter (hBmeas k)
    -- the new ball minus the previous one is disjoint from the whole prior union
    have hnotinU : geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k) ⊆
        (⋃ j ≤ k, geodesicBall (z j) (R j))ᶜ := by
      intro x hx hxU
      simp only [Set.mem_iUnion] at hxU
      obtain ⟨j, hjk, hxj⟩ := hxU
      rcases lt_or_eq_of_le hjk with hlt | heq
      · exact (hdisj j (k + 1) (by omega)).ne_of_mem hxj hx.1 rfl
      · exact hx.2 (heq ▸ hxj)
    have hunion_eq : (⋃ j ≤ k, geodesicBall (z j) (R j)) ∪
        (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) =
        ⋃ j ≤ k + 1, geodesicBall (z j) (R j) := by
      rw [Set.biUnion_le_succ]
      ext x
      simp only [Set.mem_union, Set.mem_sdiff]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · by_cases hk : x ∈ geodesicBall (z k) (R k)
          · exact Or.inl (by simpa [Set.mem_iUnion] using ⟨k, le_refl k, hk⟩)
          · exact Or.inr ⟨h, hk⟩
    refine ⟨Axioms.comp θ ψ, (Axioms.switches_comp θ ψ).trans (Nat.add_le_add hsw hψsw), ?_, ?_⟩
    · rw [Axioms.measureFlow_comp]
      have hstepB : c ^ (k + 1) * μ (⋃ j ≤ k, geodesicBall (z j) (R j)) ≤
          Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) := by
        calc c ^ (k + 1) * μ (⋃ j ≤ k, geodesicBall (z j) (R j))
            = c * (c ^ k * μ (⋃ j ≤ k, geodesicBall (z j) (R j))) := by
              rw [pow_succ', mul_assoc]
          _ ≤ c * (Axioms.measureFlow θ T μ) (geodesicBall (z k) (R k)) := by gcongr
          _ ≤ Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
                (geodesicBall (z k) (R k) ∩ geodesicBall (z (k + 1)) (R (k + 1))) := hψmass
          _ = Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
                (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) := by
              rw [Set.inter_comm]
      have hstepC : c ^ (k + 1) *
          μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) ≤
          Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
        have heq1 : Axioms.measureFlow θ T μ
            (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))
            = μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
          apply measureFlow_eq_of_flowMap_eqOn θ hT.le μ hdiffmeas
          intro x hx
          exact hfix x hx.1.1 (hnotinU hx)
        have heq2 : Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))
            = Axioms.measureFlow θ T μ
              (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
          apply measureFlow_eq_of_flowMap_eqOn ψ hT.le (Axioms.measureFlow θ T μ) hdiffmeas
          intro x hx
          exact hψfix x hx.1.1 hx.2
        rw [heq2, heq1]
        calc c ^ (k + 1) * μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))
            ≤ 1 * μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
              gcongr
              exact pow_le_one₀ zero_le (by rw [hc]; exact tsub_le_self)
          _ = μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
              rw [one_mul]
      have hsum : Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) +
          Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) =
          Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ) (geodesicBall (z (k + 1)) (R (k + 1))) := by
        rw [← measure_union Set.disjoint_sdiff_inter.symm hdiffmeas, Set.union_comm,
          Set.sdiff_union_inter]
      calc c ^ (k + 1) * μ (⋃ j ≤ k + 1, geodesicBall (z j) (R j))
          = c ^ (k + 1) * μ ((⋃ j ≤ k, geodesicBall (z j) (R j)) ∪
              (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))) := by
            rw [hunion_eq]
        _ ≤ c ^ (k + 1) * (μ (⋃ j ≤ k, geodesicBall (z j) (R j)) +
              μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))) := by
            gcongr
            exact measure_union_le _ _
        _ = c ^ (k + 1) * μ (⋃ j ≤ k, geodesicBall (z j) (R j)) +
              c ^ (k + 1) * μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
            rw [mul_add]
        _ ≤ Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
              (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) +
            Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
              (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) :=
            add_le_add hstepB hstepC
        _ = Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ) (geodesicBall (z (k + 1)) (R (k + 1))) :=
            hsum
    · intro x hxs hxout
      rw [Axioms.flowMap_comp]
      simp only [Function.comp_apply]
      rw [← hunion_eq] at hxout
      have hxU : x ∉ ⋃ j ≤ k, geodesicBall (z j) (R j) := fun h => hxout (Or.inl h)
      have hxdiff : x ∉ geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k) :=
        fun h => hxout (Or.inr h)
      have hxfixθ : flowMap θ T x = x := hfix x hxs hxU
      rw [hxfixθ]
      by_cases hxBk : x ∈ geodesicBall (z k) (R k)
      · exact absurd (by simpa [Set.mem_iUnion] using ⟨k, le_refl k, hxBk⟩) hxU
      · exact hψfix x hxs hxBk

/-- **Union-tracking ball-chain retention, BOUNDED-hypothesis variant.** Identical conclusion to
`gated_chainUnion_retention`, but `hchain`/`hdisj` are only required up to the target index `K`
(`hchain : ∀ k < K, …`, `hdisj : ∀ j k, j + 2 ≤ k → k ≤ K → …`) rather than for all of `ℕ`. This is
exactly what the induction below actually consumes -- re-reading the unbounded theorem's own proof
shows it only ever invokes `hchain`/`hdisj` at indices bounded by the current inductive step, never
beyond it, so the unbounded `∀ k : ℕ` form is an unnecessary over-generalization.

The bounded form matters because the unbounded one is literally unsatisfiable by any infinite chain
on the (compact) sphere: `hdisj`'s pairwise-separation clause for every index-gap-`≥2` pair, held
unboundedly over `k : ℕ`, would force infinitely many pairwise `≥2R`-separated points on a compact
space, which is impossible (a basic packing fact). A FINITE arc discretization -- the actual use
case for chaining within a Voronoi cell -- only ever needs finitely many indices, so this bounded
variant is the one that composes with that construction. See `GeodesicArcChain.lean`'s module
docstring for where this was discovered. -/
theorem gated_chainUnion_retention_bounded (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (K : ℕ) (z : ℕ → Eucl d) (hz : ∀ k, z k ∈ sphere d) (R : ℕ → ℝ)
    (hR : ∀ k, R k ∈ Set.Ioo 0 (Real.pi / 2))
    (hchain : ∀ k < K, (geodesicBall (z k) (R k) ∩ geodesicBall (z (k + 1)) (R (k + 1))).Nonempty)
    (hdisj : ∀ j k, j + 2 ≤ k → k ≤ K →
      Disjoint (geodesicBall (z j) (R j)) (geodesicBall (z k) (R k))) :
    ∃ θ : Params d, switches θ ≤ K ∧
      (1 - ENNReal.ofReal ε) ^ K * μ (⋃ j ≤ K, geodesicBall (z j) (R j)) ≤
        (Axioms.measureFlow θ T μ) (geodesicBall (z K) (R K)) ∧
      ∀ x, x ∈ sphere d → x ∉ ⋃ j ≤ K, geodesicBall (z j) (R j) → flowMap θ T x = x := by
  set c : ℝ≥0∞ := 1 - ENNReal.ofReal ε with hc
  induction K with
  | zero =>
    have hU0 : (⋃ j ≤ 0, geodesicBall (z j) (R j)) = geodesicBall (z 0) (R 0) := by
      ext x; simp
    refine ⟨Axioms.idParams d, ?_, ?_, ?_⟩
    · simp [Axioms.switches_id]
    · rw [hU0]; simp [Axioms.measureFlow_id]
    · intro x hxs hxout
      simp [Axioms.flowMap_id]
  | succ k ih =>
    obtain ⟨θ, hsw, hmass, hfix⟩ :=
      ih (fun k' hk' => hchain k' (by omega)) (fun j k' hjk' hkk' => hdisj j k' hjk' (by omega))
    haveI := Axioms.isProbabilityMeasure_measureFlow θ T μ
    obtain ⟨ψ, hψsw, hψmass, hψfix⟩ :=
      gated_twoCap_retention_localized (Axioms.measureFlow θ T μ) T ε hT hε (z k) (z (k + 1))
        (hz k) (hz (k + 1)) (R k) (R (k + 1)) (hR k) (hR (k + 1)) (hchain k (by omega))
    have hBmeas : ∀ j, MeasurableSet (geodesicBall (z j) (R j)) := fun j =>
      measurableSet_geodesicBall (z j) (R j)
    have hUmeas : MeasurableSet (⋃ j ≤ k, geodesicBall (z j) (R j)) :=
      MeasurableSet.biUnion (Set.finite_Iic k).countable (fun j _ => hBmeas j)
    have hdiffmeas : MeasurableSet (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) :=
      (hBmeas (k + 1)).diff (hBmeas k)
    have hintermeas : MeasurableSet
        (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) :=
      (hBmeas (k + 1)).inter (hBmeas k)
    -- the new ball minus the previous one is disjoint from the whole prior union
    have hnotinU : geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k) ⊆
        (⋃ j ≤ k, geodesicBall (z j) (R j))ᶜ := by
      intro x hx hxU
      simp only [Set.mem_iUnion] at hxU
      obtain ⟨j, hjk, hxj⟩ := hxU
      rcases lt_or_eq_of_le hjk with hlt | heq
      · exact (hdisj j (k + 1) (by omega) (by omega)).ne_of_mem hxj hx.1 rfl
      · exact hx.2 (heq ▸ hxj)
    have hunion_eq : (⋃ j ≤ k, geodesicBall (z j) (R j)) ∪
        (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) =
        ⋃ j ≤ k + 1, geodesicBall (z j) (R j) := by
      rw [Set.biUnion_le_succ]
      ext x
      simp only [Set.mem_union, Set.mem_sdiff]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · by_cases hk : x ∈ geodesicBall (z k) (R k)
          · exact Or.inl (by simpa [Set.mem_iUnion] using ⟨k, le_refl k, hk⟩)
          · exact Or.inr ⟨h, hk⟩
    refine ⟨Axioms.comp θ ψ, (Axioms.switches_comp θ ψ).trans (Nat.add_le_add hsw hψsw), ?_, ?_⟩
    · rw [Axioms.measureFlow_comp]
      have hstepB : c ^ (k + 1) * μ (⋃ j ≤ k, geodesicBall (z j) (R j)) ≤
          Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) := by
        calc c ^ (k + 1) * μ (⋃ j ≤ k, geodesicBall (z j) (R j))
            = c * (c ^ k * μ (⋃ j ≤ k, geodesicBall (z j) (R j))) := by
              rw [pow_succ', mul_assoc]
          _ ≤ c * (Axioms.measureFlow θ T μ) (geodesicBall (z k) (R k)) := by gcongr
          _ ≤ Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
                (geodesicBall (z k) (R k) ∩ geodesicBall (z (k + 1)) (R (k + 1))) := hψmass
          _ = Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
                (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) := by
              rw [Set.inter_comm]
      have hstepC : c ^ (k + 1) *
          μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) ≤
          Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
        have heq1 : Axioms.measureFlow θ T μ
            (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))
            = μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
          apply measureFlow_eq_of_flowMap_eqOn θ hT.le μ hdiffmeas
          intro x hx
          exact hfix x hx.1.1 (hnotinU hx)
        have heq2 : Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))
            = Axioms.measureFlow θ T μ
              (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
          apply measureFlow_eq_of_flowMap_eqOn ψ hT.le (Axioms.measureFlow θ T μ) hdiffmeas
          intro x hx
          exact hψfix x hx.1.1 hx.2
        rw [heq2, heq1]
        calc c ^ (k + 1) * μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))
            ≤ 1 * μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
              gcongr
              exact pow_le_one₀ zero_le (by rw [hc]; exact tsub_le_self)
          _ = μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
              rw [one_mul]
      have hsum : Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) +
          Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
            (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) =
          Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ) (geodesicBall (z (k + 1)) (R (k + 1))) := by
        rw [← measure_union Set.disjoint_sdiff_inter.symm hdiffmeas, Set.union_comm,
          Set.sdiff_union_inter]
      calc c ^ (k + 1) * μ (⋃ j ≤ k + 1, geodesicBall (z j) (R j))
          = c ^ (k + 1) * μ ((⋃ j ≤ k, geodesicBall (z j) (R j)) ∪
              (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))) := by
            rw [hunion_eq]
        _ ≤ c ^ (k + 1) * (μ (⋃ j ≤ k, geodesicBall (z j) (R j)) +
              μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k))) := by
            gcongr
            exact measure_union_le _ _
        _ = c ^ (k + 1) * μ (⋃ j ≤ k, geodesicBall (z j) (R j)) +
              c ^ (k + 1) * μ (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) := by
            rw [mul_add]
        _ ≤ Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
              (geodesicBall (z (k + 1)) (R (k + 1)) ∩ geodesicBall (z k) (R k)) +
            Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)
              (geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k)) :=
            add_le_add hstepB hstepC
        _ = Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ) (geodesicBall (z (k + 1)) (R (k + 1))) :=
            hsum
    · intro x hxs hxout
      rw [Axioms.flowMap_comp]
      simp only [Function.comp_apply]
      rw [← hunion_eq] at hxout
      have hxU : x ∉ ⋃ j ≤ k, geodesicBall (z j) (R j) := fun h => hxout (Or.inl h)
      have hxdiff : x ∉ geodesicBall (z (k + 1)) (R (k + 1)) \ geodesicBall (z k) (R k) :=
        fun h => hxout (Or.inr h)
      have hxfixθ : flowMap θ T x = x := hfix x hxs hxU
      rw [hxfixθ]
      by_cases hxBk : x ∈ geodesicBall (z k) (R k)
      · exact absurd (by simpa [Set.mem_iUnion] using ⟨k, le_refl k, hxBk⟩) hxU
      · exact hψfix x hxs hxBk

end MeasureToMeasure.Leaves
