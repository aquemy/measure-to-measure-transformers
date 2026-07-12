import MeasureToMeasure.Leaves.GatedChainUnion

/-!
# Several disjoint linear chains, composed simultaneously (union-form step 3d)

`gated_star_retention` (`Leaves/GatedStarRetention.lean`) handles `N` pairwise-disjoint SINGLE
balls each individually overlapping a shared target -- a "star" of depth-1 arms. The paper's
Section 2 Step 3 mass-sweep needs the full version: each arm may itself be a LINEAR CHAIN of
several overlapping balls (per `gated_chainUnion_retention`), only the arm's own LAST ball actually
touching the shared target. This leaf builds the piece in between: composing `N` such chains
("arms") into ONE schedule that simultaneously retains EVERY arm's own chain-union mass into that
arm's own last ball -- the genuinely new step (not just routine assembly, confirmed by a dedicated
design pass before writing any of this) needed before that schedule can be composed with
`gated_star_retention` itself.

**The induction.** Mirrors `gated_chainUnion_retention`'s own shape one level up: arms instead of
legs. The invariant carries THREE things across `n` processed arms: the switch budget, a
`∀ i ≤ n, ...` LIST of per-arm retention guarantees (not a single running total, since each arm
keeps its own guarantee independently), and the identity-outside-the-whole-forest-union fact
(needed exactly as `gated_chainUnion_retention`'s own third conjunct is, to know arm `n+1`'s
mass hasn't been touched by the first `n` arms' schedule before its own chain runs).

The inductive step re-invokes `gated_chainUnion_retention` FRESH for arm `n+1`, on the ALREADY-
EVOLVED measure (rather than trying to reuse a schedule proven against the original `μ`) -- its
own hypotheses don't depend on which measure it's applied to. Two things must survive the new arm's
run: arm `n+1`'s own union must be UNTOUCHED before its chain runs (via the forest's own identity-
outside fact, using GLOBAL cross-arm disjointness `hdisjAcross`), and every EARLIER arm's already-
retained last ball must be UNTOUCHED by the new leg (via the new leg's own identity-outside-its-
own-source fact, again using `hdisjAcross`). Unlike `gated_star_retention`, no shared-target
double-counting arises here: arm targets (each arm's own last ball) are distinct and mutually
disjoint, so this is simpler in that one respect despite tracking a growing LIST of guarantees
rather than a single sum.

**`hchain`/`hdisjWithin` are bounded per-arm by `L i`** (`∀ i k, k < L i → …` /
`∀ i j k, j+2≤k → k≤L i → …`), not unbounded over all `k : ℕ` -- an unbounded form would be
unsatisfiable by any finite-length arm construction (pairwise-`≥2R`-separated points on the compact
sphere must be finite, the same obstruction `gated_chainUnion_retention_bounded`
(`GatedChainUnion.lean`) was built to fix). This theorem's own proof calls
`gated_chainUnion_retention_bounded` per-arm directly (not the older unbounded
`gated_chainUnion_retention`), so the bounded form here is not just a defensive restatement -- it
is what the proof actually needs and produces.

M3b/mid-level staging: union-form step 3d; composed with `gated_star_retention` in
`gated_forest_to_target_retention` (`GatedForestToTarget.lean`).
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped ENNReal
open MeasureToMeasure

variable {d : ℕ}

/-- **`N+1` linear chains ("arms"), pairwise disjoint from each other**, compose into ONE schedule
that simultaneously retains EVERY arm's own chain-union mass into that arm's own last ball. Each
arm may internally overlap per its own chain structure (`hchain`/`hdisjWithin`, bounded per-arm by
`L i` -- see the module docstring); `hdisjAcross` is the NEW hypothesis, requiring every ball of
every arm to be disjoint from every ball of every OTHER arm. -/
theorem gated_chainForest_retention (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (N : ℕ) (L : ℕ → ℕ) (z : ℕ → ℕ → Eucl d) (R : ℕ → ℕ → ℝ)
    (hz : ∀ i j, z i j ∈ sphere d) (hR : ∀ i j, R i j ∈ Set.Ioo 0 (Real.pi / 2))
    (hchain : ∀ i k, k < L i →
      (geodesicBall (z i k) (R i k) ∩ geodesicBall (z i (k + 1)) (R i (k + 1))).Nonempty)
    (hdisjWithin : ∀ i j k, j + 2 ≤ k → k ≤ L i →
      Disjoint (geodesicBall (z i j) (R i j)) (geodesicBall (z i k) (R i k)))
    (hdisjAcross : ∀ i i' j j', i ≠ i' →
      Disjoint (geodesicBall (z i j) (R i j)) (geodesicBall (z i' j') (R i' j'))) :
    ∃ θ : Params d, switches θ ≤ ∑ i ∈ Finset.Iic N, L i ∧
      (∀ i ≤ N, (1 - ENNReal.ofReal ε) ^ (L i) * μ (⋃ j ≤ L i, geodesicBall (z i j) (R i j)) ≤
        (Axioms.measureFlow θ T μ) (geodesicBall (z i (L i)) (R i (L i)))) ∧
      ∀ x, x ∈ sphere d → x ∉ ⋃ i ≤ N, ⋃ j ≤ L i, geodesicBall (z i j) (R i j) →
        flowMap θ T x = x := by
  induction N with
  | zero =>
    obtain ⟨θ, hsw, hmass, hfix⟩ :=
      gated_chainUnion_retention_bounded μ T ε hT hε (L 0) (z 0) (hz 0) (R 0) (hR 0) (hchain 0)
        (hdisjWithin 0)
    have hU0 : (⋃ i ≤ 0, ⋃ j ≤ L i, geodesicBall (z i j) (R i j)) =
        (⋃ j ≤ L 0, geodesicBall (z 0 j) (R 0 j)) := by
      ext x; simp
    refine ⟨θ, ?_, ?_, ?_⟩
    · rw [← Nat.range_succ_eq_Iic, Finset.sum_range_one]; exact hsw
    · intro i hi
      interval_cases i
      exact hmass
    · rw [hU0]; exact hfix
  | succ n ih =>
    obtain ⟨θ, hsw, hmass, hfix⟩ := ih
    haveI := Axioms.isProbabilityMeasure_measureFlow θ T μ
    set Fn := ⋃ i ≤ n, ⋃ j ≤ L i, geodesicBall (z i j) (R i j) with hFndef
    set Anp1 := ⋃ j ≤ L (n + 1), geodesicBall (z (n + 1) j) (R (n + 1) j) with hAnp1def
    have hAnp1meas : MeasurableSet Anp1 :=
      MeasurableSet.biUnion (Set.finite_Iic _).countable (fun j _ => measurableSet_geodesicBall _ _)
    have hFnmeas : MeasurableSet Fn :=
      MeasurableSet.biUnion (Set.finite_Iic _).countable (fun i _ =>
        MeasurableSet.biUnion (Set.finite_Iic _).countable (fun j _ => measurableSet_geodesicBall _ _))
    have hdisjFA : Disjoint Anp1 Fn := by
      rw [hAnp1def, hFndef, Set.disjoint_left]
      rintro x hx hx'
      simp only [Set.mem_iUnion] at hx hx'
      obtain ⟨j, -, hxj⟩ := hx
      obtain ⟨i, hin, j', -, hxj'⟩ := hx'
      exact (hdisjAcross (n + 1) i j j' (by omega)).ne_of_mem hxj hxj' rfl
    obtain ⟨ψ, hψsw, hψmass, hψfix⟩ :=
      gated_chainUnion_retention_bounded (Axioms.measureFlow θ T μ) T ε hT hε (L (n + 1)) (z (n + 1))
        (hz (n + 1)) (R (n + 1)) (hR (n + 1)) (hchain (n + 1)) (hdisjWithin (n + 1))
    have hAeq : (Axioms.measureFlow θ T μ) Anp1 = μ Anp1 := by
      apply measureFlow_eq_of_flowMap_eqOn θ hT.le μ hAnp1meas
      intro x hx
      have hxs : x ∈ sphere d := by
        rw [hAnp1def] at hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨j, -, hxj⟩ := hx
        exact hxj.1
      exact hfix x hxs (Set.disjoint_left.mp hdisjFA hx)
    have hballdisj : ∀ i ≤ n, Disjoint (geodesicBall (z i (L i)) (R i (L i))) Anp1 := by
      intro i hin
      rw [hAnp1def, Set.disjoint_right]
      rintro x hx hx'
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, -, hxj⟩ := hx
      exact (hdisjAcross i (n + 1) (L i) j (by omega)).ne_of_mem hx' hxj rfl
    have hsumsucc : ∑ i ∈ Finset.Iic (n + 1), L i = (∑ i ∈ Finset.Iic n, L i) + L (n + 1) := by
      rw [← Nat.range_succ_eq_Iic, Finset.sum_range_succ, Nat.range_succ_eq_Iic]
    refine ⟨Axioms.comp θ ψ, ?_, ?_, ?_⟩
    · rw [hsumsucc]
      exact (Axioms.switches_comp θ ψ).trans (Nat.add_le_add hsw hψsw)
    · intro i hi
      rw [Axioms.measureFlow_comp]
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · have hile : i ≤ n := by omega
        have hprev := hmass i hile
        have hpres : (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ))
            (geodesicBall (z i (L i)) (R i (L i))) =
            (Axioms.measureFlow θ T μ) (geodesicBall (z i (L i)) (R i (L i))) := by
          apply measureFlow_eq_of_flowMap_eqOn ψ hT.le (Axioms.measureFlow θ T μ)
            (measurableSet_geodesicBall _ _)
          intro x hx
          exact hψfix x hx.1 (Set.disjoint_left.mp (hballdisj i hile) hx)
        rw [hpres]; exact hprev
      · have hieq : i = n + 1 := by omega
        subst hieq
        have hψmass' := hψmass
        rw [hAeq] at hψmass'
        exact hψmass'
    · intro x hxs hxout
      rw [Axioms.flowMap_comp]
      simp only [Function.comp_apply]
      have hunion_eq : (⋃ i ≤ n + 1, ⋃ j ≤ L i, geodesicBall (z i j) (R i j)) = Fn ∪ Anp1 := by
        rw [hFndef, hAnp1def, Set.biUnion_le_succ]
      rw [hunion_eq] at hxout
      have hxFn : x ∉ Fn := fun h => hxout (Or.inl h)
      have hxAnp1 : x ∉ Anp1 := fun h => hxout (Or.inr h)
      rw [hfix x hxs hxFn]
      exact hψfix x hxs hxAnp1

end MeasureToMeasure.Leaves
