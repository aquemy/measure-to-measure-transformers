import MeasureToMeasure.Foundations.SphereCover

/-!
# Measurable finite rounding map on the sphere (M3b existence, leaf S3b-iv-round)

The cell-rounding map of the `weak ⇒ W₁` crux (leaf S3b, toward `exists_meanFieldFlow`). From the
finite `μ`-null-frontier ball cover (`exists_finite_null_frontier_ball_cover`), we build a measurable
selection `s : Eucl d → Fin M` into finitely many cells, together with representatives `g : Fin M →
Eucl d` on the sphere, so that the rounding `y ↦ g (s y)` moves each sphere point by `< 2ε` and every
cell `s ⁻¹' {i}` has `μ`-null frontier.

* `exists_finite_rounding` — for a sphere-supported probability `μ` and `ε > 0`, a finite `M`, a
  measurable `s : Eucl d → Fin M`, and `g : Fin M → Eucl d` with `g i ∈ sphere d`,
  `dist y (g (s y)) < 2ε` for `y ∈ sphere d`, and `μ (frontier (s ⁻¹' {i})) = 0` for every `i`.

The finite index `Fin M` is what the crux needs: `tv_map_le` reduces `TV(r_#μₙ, r_#μ)` for the
`Eucl d`-valued rounding `r = g ∘ s` to `TV(s_#μₙ, s_#μ)` on `Fin M`, where the discrete bound applies,
and the `μ`-null cell frontiers feed portmanteau (`μₙ(s⁻¹{i}) → μ(s⁻¹{i})`).

Construction: order the cover centres as `Fin M`; `s y` = least index `i` with `y ∈ Bᵢ` (measurable via
the finite membership pattern `y ↦ (i ↦ y ∈ Bᵢ) : Eucl d → (Fin M → Bool)`), `g i` = a sphere point of
`Bᵢ`. `s` is **locally constant off `⋃ᵢ frontier Bᵢ`** (the membership pattern is locally constant
there), so every cell frontier lands in that `μ`-null set.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Metric Set Filter Topology

namespace MeasureToMeasure

variable {d : ℕ}

/-- **Existence of a measurable finite ε-rounding of the sphere with `μ`-null cell frontiers.** The
rounding is `y ↦ g (s y)` for a measurable selection `s : Eucl d → Fin M` and sphere representatives
`g : Fin M → Eucl d`; each cell `s ⁻¹' {i}` has `μ`-null frontier. -/
theorem exists_finite_rounding (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hμ : μ (sphere d)ᶜ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : ℕ) (s : Eucl d → Fin M) (g : Fin M → Eucl d), Measurable s ∧
      (∀ i, g i ∈ sphere d) ∧
      (∀ y ∈ sphere d, dist y (g (s y)) < 2 * ε) ∧
      (∀ i, μ (frontier (s ⁻¹' {i})) = 0) := by
  classical
  obtain ⟨e₀, he₀⟩ : (sphere d).Nonempty := by
    rcases Set.eq_empty_or_nonempty (sphere d) with hempty | hne
    · exfalso
      have huniv : (sphere d)ᶜ = Set.univ := by rw [hempty, Set.compl_empty]
      have h0 : μ Set.univ = 0 := by rw [← huniv]; exact hμ
      rw [measure_univ] at h0
      exact one_ne_zero h0
    · exact hne
  obtain ⟨F, rr, _hrr_pos, hrr_lt, hrr_front, hcover⟩ :=
    exists_finite_null_frontier_ball_cover μ hε
  -- `F` is nonempty (it covers the nonempty sphere).
  have hFne : F.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    subst hempty
    simpa using hcover he₀
  -- Index the centres by `Fin M`.
  set M := Fintype.card ↥F with hMdef
  have hMpos : 0 < M := by
    rw [hMdef, Fintype.card_pos_iff]
    exact ⟨⟨hFne.choose, hFne.choose_spec⟩⟩
  set enum : Fin M → ↥F := ⇑(Fintype.equivFin ↥F).symm with henum
  set c : Fin M → Eucl d := fun i => (enum i : Eucl d) with hc
  set B : Fin M → Set (Eucl d) := fun i => Metric.ball (c i) (rr (c i)) with hB
  have hBmeas : ∀ i, MeasurableSet (B i) := fun i => Metric.isOpen_ball.measurableSet
  -- The cover, re-indexed: every sphere point lies in some `B i`.
  have hcov' : ∀ y ∈ sphere d, ∃ i, y ∈ B i := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hcover hy)
    refine ⟨Fintype.equivFin ↥F ⟨x, hx⟩, ?_⟩
    have hcx : c (Fintype.equivFin ↥F ⟨x, hx⟩) = x := by
      rw [hc]; simp [henum]
    rw [hB]; simp only; rw [hcx]; exact hyx
  -- Selection: least index whose ball contains `y`, via the finite membership pattern.
  set φ : (Fin M → Bool) → Fin M := fun t =>
    if h : (Finset.univ.filter (fun i => t i = true)).Nonempty then
      (Finset.univ.filter (fun i => t i = true)).min' h else ⟨0, hMpos⟩ with hφdef
  set sel : Eucl d → Fin M := fun y => φ (fun i => decide (y ∈ B i)) with hseldef
  set rep : Fin M → Eucl d := fun i =>
    if h : (B i ∩ sphere d).Nonempty then h.choose else e₀ with hrepdef
  -- `rep i` always lands on the sphere.
  have hrep_sphere : ∀ i, rep i ∈ sphere d := by
    intro i; rw [hrepdef]; dsimp only; split
    · rename_i h; exact h.choose_spec.2
    · exact he₀
  -- Measurability of `sel = φ ∘ pattern`.
  have hpat : Measurable (fun y => (fun i => decide (y ∈ B i)) : Eucl d → (Fin M → Bool)) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    refine measurable_to_countable' (fun b => ?_)
    cases b with
    | false =>
      have : (fun y => decide (y ∈ B i)) ⁻¹' {false} = (B i)ᶜ := by
        ext y; simp
      rw [this]; exact (hBmeas i).compl
    | true =>
      have : (fun y => decide (y ∈ B i)) ⁻¹' {true} = B i := by
        ext y; simp
      rw [this]; exact hBmeas i
  have hsel : Measurable sel := (measurable_of_countable φ).comp hpat
  -- `y ∈ B (sel y)` whenever some ball contains `y`.
  have hsel_mem : ∀ y, (∃ i, y ∈ B i) → y ∈ B (sel y) := by
    rintro y ⟨i, hi⟩
    have hne : (Finset.univ.filter (fun j => decide (y ∈ B j) = true)).Nonempty :=
      ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, by simp [hi]⟩⟩
    have hsy : sel y = (Finset.univ.filter (fun j => decide (y ∈ B j) = true)).min' hne := by
      rw [hseldef]; simp only [hφdef]; rw [dif_pos hne]
    rw [hsy]
    have hmem := (Finset.univ.filter (fun j => decide (y ∈ B j) = true)).min'_mem hne
    rw [Finset.mem_filter] at hmem
    exact of_decide_eq_true hmem.2
  refine ⟨M, sel, rep, hsel, hrep_sphere, ?_, ?_⟩
  · -- Displacement `< 2ε`.
    intro y hy
    have hyB : y ∈ B (sel y) := hsel_mem y (hcov' y hy)
    have hrepB : rep (sel y) ∈ B (sel y) := by
      have hns : (B (sel y) ∩ sphere d).Nonempty := ⟨y, hyB, hy⟩
      rw [hrepdef]; dsimp only; rw [dif_pos hns]; exact hns.choose_spec.1
    have h1 : dist y (c (sel y)) < rr (c (sel y)) := Metric.mem_ball.1 hyB
    have h2 : dist (rep (sel y)) (c (sel y)) < rr (c (sel y)) := Metric.mem_ball.1 hrepB
    have hlt : rr (c (sel y)) < ε := hrr_lt (c (sel y))
    calc dist y (rep (sel y))
        ≤ dist y (c (sel y)) + dist (c (sel y)) (rep (sel y)) := dist_triangle _ _ _
      _ = dist y (c (sel y)) + dist (rep (sel y)) (c (sel y)) := by rw [dist_comm (c (sel y))]
      _ < 2 * ε := by linarith
  · -- Cell frontiers are `μ`-null: `sel` is locally constant off `⋃ᵢ frontier (B i)`.
    have hloc : ∀ y₀ : Eucl d, (∀ i, y₀ ∉ frontier (B i)) → ∀ᶠ y in 𝓝 y₀, sel y = sel y₀ := by
      intro y₀ hy₀
      set W : Fin M → Set (Eucl d) := fun i => if y₀ ∈ B i then B i else (closure (B i))ᶜ with hWdef
      have hWopen : ∀ i, IsOpen (W i) := by
        intro i; rw [hWdef]; dsimp only; split
        · exact Metric.isOpen_ball
        · exact isOpen_compl_iff.2 isClosed_closure
      have hy₀W : ∀ i, y₀ ∈ W i := by
        intro i; rw [hWdef]; dsimp only; split
        · assumption
        · rename_i hni
          intro hcl
          exact hy₀ i (by rw [frontier, (Metric.isOpen_ball).interior_eq]; exact ⟨hcl, hni⟩)
      set V := ⋂ i, W i with hVdef
      have hVopen : IsOpen V := isOpen_iInter_of_finite hWopen
      have hy₀V : y₀ ∈ V := Set.mem_iInter.2 hy₀W
      have hpatV : ∀ y ∈ V, ∀ i, (y ∈ B i ↔ y₀ ∈ B i) := by
        intro y hyV i
        have hyWi : y ∈ W i := Set.mem_iInter.1 hyV i
        rw [hWdef] at hyWi; dsimp only at hyWi
        constructor
        · intro hyB
          by_contra hn
          rw [if_neg hn] at hyWi
          exact hyWi (subset_closure hyB)
        · intro hy₀B
          rw [if_pos hy₀B] at hyWi
          exact hyWi
      have hselV : ∀ y ∈ V, sel y = sel y₀ := by
        intro y hyV
        have hpe : (fun i => decide (y ∈ B i)) = (fun i => decide (y₀ ∈ B i)) := by
          funext i; rw [decide_eq_decide]; exact hpatV y hyV i
        rw [hseldef]; dsimp only; rw [hpe]
      exact Filter.eventually_of_mem (hVopen.mem_nhds hy₀V) hselV
    -- Every cell frontier is contained in the null set `⋃ᵢ frontier (B i)`.
    have hfront_sub : ∀ i, frontier (sel ⁻¹' {i}) ⊆ ⋃ j, frontier (B j) := by
      intro i y₀ hy₀f
      by_contra hn
      simp only [Set.mem_iUnion, not_exists] at hn
      have hev := hloc y₀ hn
      rcases eq_or_ne (sel y₀) i with hz | hz
      · have hnhds : sel ⁻¹' {i} ∈ 𝓝 y₀ := by
          filter_upwards [hev] with y hy
          rw [Set.mem_preimage, Set.mem_singleton_iff, hy, hz]
        exact hy₀f.2 (mem_interior_iff_mem_nhds.2 hnhds)
      · have hnhds : (sel ⁻¹' {i})ᶜ ∈ 𝓝 y₀ := by
          filter_upwards [hev] with y hy
          rw [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hy]
          exact hz
        rw [← frontier_compl] at hy₀f
        exact hy₀f.2 (mem_interior_iff_mem_nhds.2 hnhds)
    intro i
    exact measure_mono_null (hfront_sub i) (measure_iUnion_null (fun j => hrr_front (c j)))

end MeasureToMeasure
