import MeasureToMeasure.Leaves.RotateFamilyToOrthant
import MeasureToMeasure.Leaves.ShrinkDisjointBystanders
import MeasureToMeasure.Leaves.OrthantBoundaryGap
import MeasureToMeasure.Leaves.GeodesicHullConvex

/-!
# `exists_disentangling_balls`'s strong induction: the prefix invariant and its base case

`exists_disentangling_balls` (`Statements/MainResults.lean`) is discharged by a strong induction on
`N` over the Section 3.3 machinery (Lemmas 3.2-3.4): members are placed into pairwise-disjoint balls
one at a time. This file gives the induction's SCAFFOLDING: the invariant predicate describing
"the first `k` members already placed" state (`DisentangledPrefix`), and its trivial base case
(`disentangledPrefix_base`, `k = 0`), obtained by applying the already-banked whole-family orthant
rotation (`exists_rotate_family_to_orthant`, `RotateFamilyToOrthant.lean`) exactly once -- the
induction's starting point, before the strong induction on `N` proper begins.

## Design note: no raw-identity "bystander" clause

A natural first attempt states, for unplaced members `i ≥ k`, `attnMeasureFlow θ (μ₀ i) = μ₀ i`
("untouched" read as literal fixed-pointedness against the ORIGINAL family). This is
UNSATISFIABLE at the base case: `k = 0` makes EVERY member an "unplaced bystander" by that reading,
while `exists_rotate_family_to_orthant`'s schedule genuinely MOVES every member (it is exactly the
`durationSum = T > 0` whole-family rotation into the orthant, not the identity). Literal
`attnMeasureFlow θ (μ₀ i) = μ₀ i` for all `i` would force `μ₀ i` to already be orthant-supported,
which the base case's hypotheses (sphere support only) do not give.

`DisentangledPrefix` instead captures "unplaced" the way the induction actually needs it: every
member (placed or not) carries the SAME schedule's sphere-and-orthant invariant (the first clause,
universal in `i`); placed members (`i < k`) are additionally pinned into their own pairwise-disjoint
ball with an invertible on-sphere flow map. Being unplaced means carrying no ball/inverse commitment
yet, not being literally unmoved by the flow -- exactly what the base case (a pure rotation, no
member yet localized to a ball) produces. `exists_disentangling_balls`'s own target conclusion has
no "bystander" clause either (there are none left once `k = N`), confirming this is purely an
internal bookkeeping device for the induction, not part of the paper-facing statement.

M3b/mid-level staging: consumed when `exists_disentangling_balls`'s full induction is assembled; see
`Statements/MainResults.lean` and the `exists-disentangling-balls-campaign` project notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open MeasureToMeasure.Foundations (isProbabilityMeasure_attnMeasureFlow
  attnMeasureFlow_supportedIn_sphere attnMeasureFlow_exists_map attnMeasureFlow_append)
open scoped RealInnerProductSpace

/-- **The induction's prefix invariant.** `DisentangledPrefix d N k μ₀ θ α r` holds when a single
schedule `θ`, applied to every member of the family `μ₀`, keeps everyone sphere-and-orthant
supported, and additionally localizes the first `k` members (`i < k`, indexed into `α`/`r` via
`⟨i, hik⟩`) into pairwise-disjoint balls `Metric.ball (α ⟨i,hik⟩) (r ⟨i,hik⟩)`, each realized by a
measurable flow map with a measurable on-sphere inverse (the paper's Lipschitz-invertible `φ^t`,
eq. (B.2)) -- matching `exists_disentangling_balls`'s own per-member conclusion clause. Members
`i ≥ k` carry no ball commitment yet (see the module docstring for why a literal
"unchanged from `μ₀ i`" clause is dropped). -/
def DisentangledPrefix (d N k : ℕ) (μ₀ : Fin N → Measure (Eucl d)) (θ : AttnSchedule d)
    (α : Fin k → Eucl d) (r : Fin k → ℝ) : Prop :=
  (∀ i : Fin N, supportedIn (attnMeasureFlow θ (μ₀ i)) (sphere d)) ∧
  (∀ i : Fin N, supportedIn (attnMeasureFlow θ (μ₀ i)) (orthant d)) ∧
  (∀ i : Fin N, ∀ hik : (i : ℕ) < k,
    supportedIn (attnMeasureFlow θ (μ₀ i)) (Metric.ball (α ⟨i, hik⟩) (r ⟨i, hik⟩))) ∧
  Pairwise (fun a b : Fin k => Disjoint (Metric.ball (α a) (r a)) (Metric.ball (α b) (r b))) ∧
  (∀ i : Fin N, ∀ _hik : (i : ℕ) < k, ∃ Φ Φinv : Eucl d → Eucl d,
    Measurable Φ ∧ Measurable Φinv ∧ attnMeasureFlow θ (μ₀ i) = (μ₀ i).map Φ ∧
    ∀ x ∈ sphere d, Φinv (Φ x) = x)

/-- **The induction's base case (`k = 0`).** Before any member has been placed into a ball, one
call to `exists_rotate_family_to_orthant` (with horizon `T / 2`, since its two-phase schedule spans
`durationSum = 2 * T'` for horizon `T'`) gives a schedule of EXACT total duration `T` establishing
`DisentangledPrefix d N 0` with empty ball data (`Fin.elim0`) -- the induction's starting point. -/
theorem disentangledPrefix_base (hd : 2 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d))
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hmiss : SharedMissingDirection μ₀) (T : ℝ) (hT : 0 < T) :
    ∃ θ : AttnSchedule d, DisentangledPrefix d N 0 μ₀ θ Fin.elim0 Fin.elim0 ∧
      AttnSchedule.durationSum θ = T := by
  haveI : NeZero d := ⟨by omega⟩
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  obtain ⟨θ, _hsw, hdur, hall⟩ := exists_rotate_family_to_orthant μ₀ hμ hd hμs hmiss (T / 2) hT2
  refine ⟨θ, ⟨fun i => (hall i).1, fun i => (hall i).2.1, ?_, ?_, ?_⟩, ?_⟩
  · intro i hik
    exact absurd hik (Nat.not_lt_zero _)
  · intro a b _
    exact a.elim0
  · intro i hik
    exact absurd hik (Nat.not_lt_zero _)
  · rw [hdur]; ring

/-- **G2: the non-colinear insertion step.** Given `DisentangledPrefix` at `k` and a new member
`k` whose (post-`θ`) barycenter direction is not colinear with any already-placed member's, one
more schedule chunk `θ'` (of any prescribed duration `T`) extends the invariant to `k + 1`, shrinking
the new member into a fresh ball disjoint from every already-placed ball.

Reuses leaf 2 (`ShrinkDisjointBystanders.lean`) via a self-pairing trick: the companion `ν₀` fed to
`lemma_3_3` (invoked here directly, not through the `exists_shrink_disjoint_from_bystanders` wrapper
-- see below) IS the new member itself (`ν₀ := μ₀' j`), so `hνcol` is the trivial `c = 1` witness.

**Deviations from the original planning sketch** (per the group note: the merged `DisentangledPrefix`
differs from the sketch, read directly instead of trusting its literal text):

* `hnoncol` is stated over the WHOLE family `Fin N` (not just "new vs. already-placed"). `lemma_3_3`'s
  `hnoncol` hypothesis is a blanket `Pairwise` over whatever family is passed to it; passing the
  restricted `Fin k` prefix would only fix the `k` already-placed members (leaving `DisentangledPrefix`'s
  own clauses 1/2, which are universal over ALL of `Fin N`, unprovable for not-yet-placed members `i > k`
  after `θ'` runs). Passing the FULL family at once makes `lemma_3_3`'s bystander-fixing clause
  (`∀ i, i ≠ j → ...`) cover placed and not-yet-placed members alike, in one call. This is a genuine
  strengthening beyond the sketch, carried as the induction's own standing invariant (matching leaf 2's
  own `hsep` precedent: "NOT supplied here, established when the induction itself is assembled").
* `hμs` (ORIGINAL, pre-`θ`, sphere support) is added: `DisentangledPrefix` only tracks POST-`θ` sphere
  support, but `isProbabilityMeasure_attnMeasureFlow` / `attnMeasureFlow_exists_map` need the PRE-flow
  fact to promote clauses 1 and 5 to the extended schedule `θ ++ θ'`. This is the same standing "data"
  hypothesis `theorem_1_1`/`theorem_1_2` already carry for the whole family.
* The target ball radius `ε` is NOT caller-supplied (dropping the sketch's `ε, hε` parameters): it is
  derived here as `min ε₁ ε₀`, where `ε₁` comes from leaf 2's OWN `exists_ball_disjoint_of_dist_pos`
  (disjointness from every already-placed ball, using a `hsep` hypothesis in leaf 2's own style) and
  `ε₀` comes from `orthant d` being OPEN (`isOpen_orthant`) around the new member's barycenter
  direction (itself in the orthant by `barycenter_mem_orthant`, since orthant support forces a
  strictly positive barycenter). `lemma_3_3` is called directly (not the
  `exists_shrink_disjoint_from_bystanders` wrapper) with this `ε` as the target shrink radius, since the
  wrapper picks its OWN `ε` from `ε₁` alone and does not know about the orthant constraint; the two
  constraints combine via `min` only because DISJOINTNESS (unlike ball-containment) is monotone under
  shrinking the ball, so both survive at the smaller radius `ε := min ε₁ ε₀`.
* Clauses 1 (sphere) and 5 (invertible map) of the extended invariant are established directly and
  UNCONDITIONALLY for `θ ++ θ'` via the general `attnMeasureFlow_supportedIn_sphere` /
  `attnMeasureFlow_exists_map` lemmas (true for ANY schedule on a sphere-supported probability input),
  not through `lemma_3_3`'s bystander-fixing clause at all. -/
theorem disentangle_insert_noncolinear {d N k : ℕ} (hk : k < N)
    (μ₀ : Fin N → Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (θ : AttnSchedule d) (α : Fin k → Eucl d) (r : Fin k → ℝ)
    (hinv : DisentangledPrefix d N k μ₀ θ α r)
    (hnoncol : Pairwise (fun i j : Fin N => ∀ c : ℝ,
        barycenter (attnMeasureFlow θ (μ₀ i)) ≠ c • barycenter (attnMeasureFlow θ (μ₀ j))))
    (hsep : ∀ i : Fin k, r i < dist
        (‖barycenter (attnMeasureFlow θ (μ₀ ⟨k, hk⟩))‖⁻¹ •
          barycenter (attnMeasureFlow θ (μ₀ ⟨k, hk⟩)))
        (α i))
    (T : ℝ) (hT : 0 < T) :
    ∃ θ' : AttnSchedule d, AttnSchedule.durationSum θ' = T ∧
      ∃ (ω : Eucl d) (ε : ℝ), 0 < ε ∧
        DisentangledPrefix d N (k + 1) μ₀ (θ ++ θ') (Fin.snoc α ω) (Fin.snoc r ε) := by
  obtain ⟨hsph, horth, hball, hballdisj, -⟩ := hinv
  set j : Fin N := ⟨k, hk⟩ with hjdef
  set μ₀' : Fin N → Measure (Eucl d) := fun i => attnMeasureFlow θ (μ₀ i) with hμ₀'def
  have hμ' : ∀ i, IsProbabilityMeasure (μ₀' i) :=
    fun i => haveI := hμ i; isProbabilityMeasure_attnMeasureFlow θ (μ₀ i) (hμs i)
  haveI := hμ' j
  set ω : Eucl d := ‖barycenter (μ₀' j)‖⁻¹ • barycenter (μ₀' j) with hωdef
  -- `ω` is (strictly) in the open orthant: it is a positive multiple of an orthant barycenter.
  have hbint : Integrable (fun x : Eucl d => x) (μ₀' j) := integrable_id_of_sphere_support (hsph j)
  have hbmem : barycenter (μ₀' j) ∈ orthant d := barycenter_mem_orthant (hsph j) hbint (horth j)
  have hbpos : 0 < ‖barycenter (μ₀' j)‖ := norm_barycenter_pos_of_orthant (hsph j) hbint (horth j)
  have hωmem : ω ∈ orthant d := by
    intro i
    have hinvpos : (0 : ℝ) < ‖barycenter (μ₀' j)‖⁻¹ := inv_pos.mpr hbpos
    simpa [hωdef] using mul_pos hinvpos (hbmem i)
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.isOpen_iff.mp isOpen_orthant ω hωmem
  -- `ε₁`: disjointness slack against every already-placed ball (`Option (Fin k)` handles `k = 0`).
  obtain ⟨ε₁, hε₁pos, hε₁disj⟩ := exists_ball_disjoint_of_dist_pos
    (fun o : Option (Fin k) => o.elim (0 : Eucl d) α) (fun o : Option (Fin k) => o.elim (-1 : ℝ) r)
    ω (by
      rintro (_ | i)
      · simp only [Option.elim, dist_zero_right]
        linarith [norm_nonneg ω]
      · exact hsep i)
  set ε : ℝ := min ε₁ ε₀ with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos hε₀pos
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hεε₀ : ε ≤ ε₀ := min_le_right _ _
  -- Shrink member `j` (self-paired with itself as its own colinear companion) via `lemma_3_3`
  -- directly, at the self-chosen radius `ε` honoring both constraints at once.
  obtain ⟨θ', hdur, hshrinkν, hshrinkμ, hfix⟩ :=
    lemma_3_3 j μ₀' (μ₀' j) hμ' T ε hT hεpos hsph horth (hsph j) (horth j) hnoncol
      ⟨1, (one_smul ℝ _).symm⟩
  refine ⟨θ', hdur, ω, ε, hεpos, ?_, ?_, ?_, ?_, ?_⟩
  · -- Clause 1 (sphere support): general fact, holds for any schedule on any sphere-supported
    -- probability member of the family, regardless of placement.
    intro i
    rw [attnMeasureFlow_append]
    exact attnMeasureFlow_supportedIn_sphere θ' (attnMeasureFlow θ (μ₀ i))
      (haveI := hμ' i; hsph i)
  · -- Clause 2 (orthant support): already-placed/not-yet-placed members are fixed by `θ'`
    -- (`hfix`); the freshly shrunk member sits inside `ball ω ε ⊆ ball ω ε₀ ⊆ orthant d`.
    intro i
    rw [attnMeasureFlow_append]
    by_cases hij : i = j
    · subst hij
      have hballorth : Metric.ball ω ε ⊆ orthant d :=
        (Metric.ball_subset_ball hεε₀).trans hε₀sub
      exact measure_mono_null (Set.compl_subset_compl.mpr hballorth) hshrinkμ
    · rw [hfix i hij]
      exact horth i
  · -- Clause 3 (ball placement of every placed member, now `i < k + 1`).
    intro i hik
    rw [attnMeasureFlow_append]
    rcases Fin.eq_castSucc_or_eq_last (⟨i, hik⟩ : Fin (k + 1)) with ⟨i', hi'⟩ | hi'
    · have hval : (i : ℕ) = (i' : ℕ) := by
        have h := congrArg Fin.val hi'; simpa using h
      have hik' : (i : ℕ) < k := hval ▸ i'.isLt
      have hii' : i' = (⟨i, hik'⟩ : Fin k) := Fin.ext hval.symm
      have hfixi : i ≠ j := by
        intro h
        have hikk : (i : ℕ) = k := by rw [h, hjdef]
        omega
      rw [hfix i hfixi, hi', hii']
      simp only [Fin.snoc_castSucc]
      exact hball i hik'
    · have hival : (i : ℕ) = k := by
        have := congrArg Fin.val hi'; simpa using this
      have hieqj : i = j := by
        apply Fin.ext; simp [hjdef, hival]
      rw [hi', hieqj]
      simp only [Fin.snoc_last]
      exact hshrinkν
  · -- Clause 4 (pairwise disjoint balls, extended to `k + 1`).
    intro a b hab
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha'⟩ | ha'
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb'⟩ | hb'
      · rw [ha', hb'] at hab ⊢
        simp only [Fin.snoc_castSucc]
        exact hballdisj (by simpa using (Fin.castSucc_injective k).ne_iff.mp hab)
      · rw [ha', hb']
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact (Disjoint.mono_left (Metric.ball_subset_ball hεε₁) (hε₁disj (some a'))).symm
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb'⟩ | hb'
      · rw [ha', hb']
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact Disjoint.mono_left (Metric.ball_subset_ball hεε₁) (hε₁disj (some b'))
      · exfalso; apply hab; rw [ha', hb']
  · -- Clause 5 (invertible on-sphere flow map): general fact for any schedule on the ORIGINAL
    -- sphere-supported probability member (does not need `hfix` or `lemma_3_3` at all).
    intro i hik
    haveI := hμ i
    obtain ⟨Φ, Φinv, hΦm, -, hΦinvm, hΦeq, -, hΦinv⟩ :=
      attnMeasureFlow_exists_map (θ ++ θ') (μ₀ i) (hμs i)
    exact ⟨Φ, Φinv, hΦm, hΦinvm, hΦeq, hΦinv⟩

end MeasureToMeasure.Leaves
