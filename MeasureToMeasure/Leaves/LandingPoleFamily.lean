import MeasureToMeasure.Leaves.MergeTolerantRelocation

/-!
# A full family of pairwise-disjoint landing poles (lemma 5.4, G8 Phase-2 instantiation)

`exists_landing_pole_avoiding` places ONE fresh landing pole near a target, dodging any finite
pairwise-disjoint family of small closed balls. The Phase-2 relocation needs a WHOLE family: one
pole per relocated ball (targets may repeat), each near its own target, with all landing balls
pairwise disjoint AND disjoint from every source ball. This file runs the single-pole placement
sequentially, one pole per step, the avoided family growing by the freshly placed landing ball
each time (`Function.update` carries the partial family through the induction; each new radius
is shrunk below `δl / 16` so it stays admissible for every later placement).
-/

set_option autoImplicit false

namespace MeasureToMeasure.Leaves

open MeasureTheory Set

variable {d : ℕ}

/-- **A pairwise-disjoint landing-pole family.** One on-sphere pole `z' k` with radius `r' k`
per index, each closed landing ball inside `Metric.ball (ztarget k) (δl / 2)`, all landing balls
pairwise disjoint and disjoint from every source ball `closedBall (src k) σr`. Sequential
placement via `exists_landing_pole_avoiding`. -/
theorem exists_landing_pole_family (hd : 2 ≤ d) {L : ℕ} (ztarget : Fin L → Eucl d)
    (hzt : ∀ k, ztarget k ∈ sphere d) {δl : ℝ} (hδl : 0 < δl) (hδl4 : δl ≤ 4)
    (src : Fin L → Eucl d) {σr : ℝ} (hσr : 0 < σr) (hσrδ : σr < δl / 8)
    (hsrcdisj : ∀ j k : Fin L, j ≠ k →
      Disjoint (Metric.closedBall (src j) σr) (Metric.closedBall (src k) σr)) :
    ∃ (z' : Fin L → Eucl d) (r' : Fin L → ℝ),
      (∀ k, z' k ∈ sphere d) ∧ (∀ k, 0 < r' k) ∧ (∀ k, r' k < δl / 8) ∧
      (∀ k, Metric.closedBall (z' k) (r' k) ⊆ Metric.ball (ztarget k) (δl / 2)) ∧
      (∀ j k : Fin L, j ≠ k →
        Disjoint (Metric.closedBall (z' j) (r' j)) (Metric.closedBall (z' k) (r' k))) ∧
      (∀ j k : Fin L,
        Disjoint (Metric.closedBall (z' j) (r' j)) (Metric.closedBall (src k) σr)) := by
  classical
  have key : ∀ Kn : ℕ, Kn ≤ L → ∃ (z' : Fin L → Eucl d) (r' : Fin L → ℝ),
      (∀ k : Fin L, (k : ℕ) < Kn → z' k ∈ sphere d ∧ 0 < r' k ∧ r' k < δl / 8 ∧
        Metric.closedBall (z' k) (r' k) ⊆ Metric.ball (ztarget k) (δl / 2) ∧
        ∀ j : Fin L, Disjoint (Metric.closedBall (z' k) (r' k))
          (Metric.closedBall (src j) σr)) ∧
      (∀ j k : Fin L, (j : ℕ) < Kn → (k : ℕ) < Kn → j ≠ k →
        Disjoint (Metric.closedBall (z' j) (r' j)) (Metric.closedBall (z' k) (r' k))) := by
    intro Kn
    induction Kn with
    | zero =>
      intro _
      exact ⟨src, fun _ => 1, fun k hk => absurd hk (Nat.not_lt_zero _),
        fun j k hj _ _ => absurd hj (Nat.not_lt_zero _)⟩
    | succ Kn ih =>
      intro hK1
      have hKL : Kn < L := hK1
      obtain ⟨z', r', hprops, hpair⟩ := ih (Nat.le_of_lt hKL)
      set kK : Fin L := ⟨Kn, hKL⟩ with hkKdef
      -- the avoided family: all source balls plus the already placed landing balls
      set p : Fin (L + Kn) → Eucl d := fun i =>
        Sum.elim src (fun b : Fin Kn => z' ⟨b, lt_trans b.isLt hKL⟩)
          (finSumFinEquiv.symm i) with hpdef
      set rr : Fin (L + Kn) → ℝ := fun i =>
        Sum.elim (fun _ => σr) (fun b : Fin Kn => r' ⟨b, lt_trans b.isLt hKL⟩)
          (finSumFinEquiv.symm i) with hrrdef
      have hplace : ∀ b : Fin Kn, ((⟨b, lt_trans b.isLt hKL⟩ : Fin L) : ℕ) < Kn := fun b =>
        b.isLt
      have hrrsmall : ∀ i, rr i < δl / 8 := by
        intro i
        rcases hcase : finSumFinEquiv.symm i with a | b
        · simp only [hrrdef, hcase, Sum.elim_inl]
          exact hσrδ
        · simp only [hrrdef, hcase, Sum.elim_inr]
          exact (hprops _ (hplace b)).2.2.1
      have hrrdisj : ∀ i j : Fin (L + Kn), i ≠ j →
          Disjoint (Metric.closedBall (p i) (rr i)) (Metric.closedBall (p j) (rr j)) := by
        intro i j hij
        have hne : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j := fun h =>
          hij (finSumFinEquiv.symm.injective h)
        rcases hci : finSumFinEquiv.symm i with a₁ | b₁ <;>
          rcases hcj : finSumFinEquiv.symm j with a₂ | b₂ <;>
          simp only [hpdef, hrrdef, hci, hcj, Sum.elim_inl, Sum.elim_inr] <;>
          rw [hci, hcj] at hne
        · exact hsrcdisj a₁ a₂ (fun h => hne (h ▸ rfl))
        · exact ((hprops _ (hplace b₂)).2.2.2.2 a₁).symm
        · exact (hprops _ (hplace b₁)).2.2.2.2 a₂
        · refine hpair _ _ (hplace b₁) (hplace b₂) ?_
          intro h
          apply hne
          have hb : b₁ = b₂ := by
            have := congrArg (fun x : Fin L => (x : ℕ)) h
            exact Fin.ext this
          rw [hb]
      obtain ⟨znew, rnew, hznew_s, hrnew_pos, hznew_sub, hznew_avoid⟩ :=
        exists_landing_pole_avoiding hd (hzt kK) hδl hδl4 p rr hrrsmall hrrdisj
      set rfin : ℝ := min rnew (δl / 16) with hrfindef
      have hrfin_pos : 0 < rfin := lt_min hrnew_pos (by positivity)
      have hrfin_lt : rfin < δl / 8 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hrfin_sub : Metric.closedBall znew rfin ⊆ Metric.closedBall znew rnew :=
        Metric.closedBall_subset_closedBall (min_le_left _ _)
      refine ⟨Function.update z' kK znew, Function.update r' kK rfin, ?_, ?_⟩
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkK | hkK
        · have hkne : k ≠ kK := fun h => by
            rw [h] at hkK
            exact absurd hkK (lt_irrefl _)
          rw [Function.update_of_ne hkne, Function.update_of_ne hkne]
          exact hprops k hkK
        · have hkeq : k = kK := Fin.ext hkK
          subst hkeq
          rw [Function.update_self, Function.update_self]
          refine ⟨hznew_s, hrfin_pos, hrfin_lt,
            subset_trans hrfin_sub hznew_sub, ?_⟩
          intro j
          have hav := hznew_avoid (finSumFinEquiv (Sum.inl j))
          simp only [hpdef, hrrdef, Equiv.symm_apply_apply, Sum.elim_inl] at hav
          exact Set.disjoint_of_subset_left hrfin_sub hav
      · intro j k hj hk hjk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjK | hjK <;>
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkK | hkK
        · have hjne : j ≠ kK := fun h => by rw [h] at hjK; exact absurd hjK (lt_irrefl _)
          have hkne : k ≠ kK := fun h => by rw [h] at hkK; exact absurd hkK (lt_irrefl _)
          rw [Function.update_of_ne hjne, Function.update_of_ne hjne,
            Function.update_of_ne hkne, Function.update_of_ne hkne]
          exact hpair j k hjK hkK hjk
        · -- `k` is the fresh pole, `j` an old one
          have hkeq : k = kK := Fin.ext hkK
          have hjne : j ≠ kK := fun h => hjk (h.trans hkeq.symm)
          rw [hkeq, Function.update_of_ne hjne, Function.update_of_ne hjne,
            Function.update_self, Function.update_self]
          have hav := hznew_avoid (finSumFinEquiv (Sum.inr ⟨(j : ℕ), hjK⟩))
          simp only [hpdef, hrrdef, Equiv.symm_apply_apply, Sum.elim_inr, Fin.eta] at hav
          exact (Set.disjoint_of_subset_left hrfin_sub hav).symm
        · -- `j` is the fresh pole, `k` an old one
          have hjeq : j = kK := Fin.ext hjK
          have hkne : k ≠ kK := fun h => hjk (hjeq.trans h.symm)
          rw [hjeq, Function.update_of_ne hkne, Function.update_of_ne hkne,
            Function.update_self, Function.update_self]
          have hav := hznew_avoid (finSumFinEquiv (Sum.inr ⟨(k : ℕ), hkK⟩))
          simp only [hpdef, hrrdef, Equiv.symm_apply_apply, Sum.elim_inr, Fin.eta] at hav
          exact Set.disjoint_of_subset_left hrfin_sub hav
        · exact absurd (hjK.trans hkK.symm) (fun h => hjk (Fin.ext h))
  obtain ⟨z', r', hprops, hpair⟩ := key L le_rfl
  exact ⟨z', r', fun k => (hprops k k.isLt).1, fun k => (hprops k k.isLt).2.1,
    fun k => (hprops k k.isLt).2.2.1, fun k => (hprops k k.isLt).2.2.2.1,
    fun j k hjk => hpair j k j.isLt k.isLt hjk,
    fun j k => (hprops j j.isLt).2.2.2.2 k⟩

end MeasureToMeasure.Leaves
