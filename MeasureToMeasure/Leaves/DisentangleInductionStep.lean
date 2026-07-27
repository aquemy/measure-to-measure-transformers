import MeasureToMeasure.Leaves.RotateFamilyToOrthant
import MeasureToMeasure.Leaves.ShrinkDisjointBystanders
import MeasureToMeasure.Leaves.OrthantBoundaryGap
import MeasureToMeasure.Leaves.GeodesicHullConvex
import MeasureToMeasure.Leaves.OrthantSphereAvoiding
import MeasureToMeasure.Leaves.GenRestNearBall

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

/-- **A scalar-multiple relation flips direction, given one side is nonzero.** If `w` is never a
scalar multiple of `v` (for any real `c`) and `v ≠ 0`, then `v` is never a scalar multiple of `w`
either: were `v = c • w`, `c = 0` would force `v = 0` (excluded), and `c ≠ 0` would give
`w = c⁻¹ • v`, contradicting the hypothesis at `c⁻¹`. Used below to read the ORIGINAL family's
non-colinearity with the poisoned-Dirac slot off `exists_dirac_avoiding_measure`'s one-directional
avoidance guarantee. -/
theorem ne_smul_flip_of_ne_zero {v w : Eucl d} (hv : v ≠ 0) (h : ∀ c : ℝ, w ≠ c • v) :
    ∀ c : ℝ, v ≠ c • w := by
  intro c hvw
  rcases eq_or_ne c 0 with hc0 | hc0
  · rw [hc0, zero_smul] at hvw; exact hv hvw
  · exact h c⁻¹ (by rw [hvw, smul_smul, inv_mul_cancel₀ hc0, one_smul])

/-- **G6/Phase-1 assembly: the colinear-pair shrink, poisoned-family trick.** Given a family `μ₀`
whose ONLY colinearity failure is the pair `(j, k)` (`hnoncol` covers every pair not touching `k`;
`hcol` records the `(j, k)` colinearity itself, the very premise of this branch), one schedule
chunk `θ'` of any prescribed duration `T`:

* confines BOTH `j` and `k` into a single shared ball around `j`'s barycenter direction, chosen
  disjoint from every ball in a caller-supplied bystander family `β, r` (the already-placed balls),
  and
* leaves literally EVERY other family member (`i ≠ j`, `i ≠ k`) fixed pointwise.

**The construction.** `lemma_3_3`'s own `hnoncol` hypothesis is a blanket `Pairwise` over the WHOLE
family it is fed, so it cannot be called on `μ₀` directly (the very premise here is that `(j, k)`
violates it). The fix: substitute `exists_dirac_avoiding_measure`'s witness `ρ` -- chosen to avoid
every scalar multiple of every `μ₀ i`'s barycenter, `i : Fin N` -- at slot `k` only
(`Function.update μ₀ k ρ`), and call `lemma_3_3` on this POISONED family with acted index `j`
(untouched by the substitution, since `j ≠ k`) and companion `ν₀ := μ₀ k` (the REAL, unpoisoned
member). The poisoned family satisfies `lemma_3_3`'s `hnoncol`: pairs avoiding `k` come from the
hypothesis directly, pairs touching `k` come from `ρ`'s avoidance property (flipped via
`ne_smul_flip_of_ne_zero` when `k` is on the right). The colinearity hypothesis `lemma_3_3` needs
between the companion and the acted index (`hνcol`) is exactly `hcol`, unpoisoned, since `j ≠ k`
leaves slot `j` untouched by the substitution. The resulting schedule's bystander-fixing clause
(`∀ i, i ≠ j → attnMeasureFlow θ (μ₀'' i) = μ₀'' i`) reads off the REAL family's own bystander
fact for every `i ≠ j, i ≠ k` (poisoning only touches slot `k`, which is excluded); slot `k`'s own
fate is instead read off `lemma_3_3`'s shrinking conclusion on the companion `ν₀ = μ₀ k` directly,
so the poisoned slot's own (fictional, uninformative) fixed-point fact is simply discarded.

**Why the caller-supplied radius cap `εmax`.** The confinement radius is chosen existentially here
(`exists_ball_disjoint_of_dist_pos` only knows about the bystander balls), and ball-SUPPORT is not
monotone under shrinking, so a caller cannot narrow the ball after the fact: the cap has to be
pushed into this phase. It is: the returned `ε` additionally satisfies `ε ≤ εmax` for any
caller-supplied `0 < εmax`, because DISJOINTNESS (unlike support) IS monotone under
`Metric.ball_subset_ball`, so every conclusion survives at the smaller radius `min ε εmax`. This
is the same `min` idiom `disentangle_insert_noncolinear` uses above.

The cap exists so the eventual assembly can force the confinement ball INSIDE the open orthant.
There `εmax` is instantiated from `Metric.isOpen_iff.mp isOpen_orthant ω̂ hω̂mem`, where
`ω̂ := ‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)` is in the OPEN orthant (`barycenter_mem_orthant`
plus `norm_barycenter_pos_of_orthant`, both `OrthantBoundaryGap.lean`, both already used above);
the resulting `U := Metric.ball ω̂ ε` then satisfies `U ⊆ orthant d`, which is exactly the `U ⊆ S`
antecedent that the region-generic forward-invariance conjunct of Phase 2 / Phase 3
(`barycenter_ne_of_massGapCollapse_meanField`,
`barycenter_nonColinear_of_massGapCollapse_meanField`) needs in order to yield orthant preservation
for the unplaced bystanders. Without the cap those conjuncts are kernel-clean but inapplicable. -/
theorem exists_shrink_colinear_pair_disjoint_from_bystanders (hd : 2 ≤ d) {N : ℕ}
    (j k : Fin N) (hjk : j ≠ k) (μ₀ : Fin N → Measure (Eucl d))
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) (T : ℝ) (hT : 0 < T)
    (εmax : ℝ) (hεmax : 0 < εmax)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hμo : ∀ i, supportedIn (μ₀ i) (orthant d))
    (hnoncol : Pairwise (fun i i' : Fin N =>
        i ≠ k → i' ≠ k → ∀ c : ℝ, barycenter (μ₀ i) ≠ c • barycenter (μ₀ i')))
    (hcol : ∃ c : ℝ, barycenter (μ₀ k) = c • barycenter (μ₀ j))
    {ι : Type*} [Fintype ι] [Nonempty ι] (β : ι → Eucl d) (r : ι → ℝ)
    (hsep : ∀ i, r i < dist (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) (β i)) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      (∃ ε > 0, ε ≤ εmax ∧
        supportedIn (attnMeasureFlow θ (μ₀ j))
          (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε) ∧
        supportedIn (attnMeasureFlow θ (μ₀ k))
          (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε) ∧
        ∀ i, Disjoint (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε)
          (Metric.ball (β i) (r i))) ∧
      ∀ i, i ≠ j → i ≠ k → attnMeasureFlow θ (μ₀ i) = μ₀ i := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨ε₁, hε₁pos, hdisj₁⟩ :=
    exists_ball_disjoint_of_dist_pos β r (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) hsep
  -- Honor the caller's cap: shrink to `min ε₁ εmax`. Disjointness survives (it is monotone under
  -- `Metric.ball_subset_ball`), and the shrink radius is only ever fed FORWARD into `lemma_3_3`.
  set ε : ℝ := min ε₁ εmax with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos hεmax
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hdisj : ∀ i, Disjoint (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε)
      (Metric.ball (β i) (r i)) :=
    fun i => Disjoint.mono_left (Metric.ball_subset_ball hεε₁) (hdisj₁ i)
  obtain ⟨ρ, hρprob, hρs, hρo, hρavoid⟩ :=
    exists_dirac_avoiding_measure hd (fun i : Fin N => barycenter (μ₀ i))
  classical
  set μ₀' : Fin N → Measure (Eucl d) := Function.update μ₀ k ρ with hμ₀'def
  have hjk' : μ₀' j = μ₀ j := Function.update_of_ne hjk ρ μ₀
  have hμ' : ∀ i, IsProbabilityMeasure (μ₀' i) := by
    intro i
    by_cases hik : i = k
    · rw [hμ₀'def, hik, Function.update_self]; exact hρprob
    · rw [hμ₀'def, Function.update_of_ne hik]; exact hμ i
  have hμs' : ∀ i, supportedIn (μ₀' i) (sphere d) := by
    intro i
    by_cases hik : i = k
    · rw [hμ₀'def, hik, Function.update_self]; exact hρs
    · rw [hμ₀'def, Function.update_of_ne hik]; exact hμs i
  have hμo' : ∀ i, supportedIn (μ₀' i) (orthant d) := by
    intro i
    by_cases hik : i = k
    · rw [hμ₀'def, hik, Function.update_self]; exact hρo
    · rw [hμ₀'def, Function.update_of_ne hik]; exact hμo i
  have hbarynz : ∀ i : Fin N, barycenter (μ₀ i) ≠ 0 := by
    intro i
    haveI := hμ i
    exact norm_pos_iff.mp (norm_barycenter_pos_of_orthant (hμs i)
      (integrable_id_of_sphere_support (hμs i)) (hμo i))
  have hnoncol' : Pairwise (fun i i' : Fin N => ∀ c : ℝ,
      barycenter (μ₀' i) ≠ c • barycenter (μ₀' i')) := by
    intro i i' hii'
    by_cases hik : i = k
    · by_cases hi'k : i' = k
      · exact absurd (hik.trans hi'k.symm) hii'
      · rw [hμ₀'def, hik, Function.update_self, Function.update_of_ne hi'k]
        exact hρavoid i'
    · by_cases hi'k : i' = k
      · rw [hμ₀'def, hi'k, Function.update_self, Function.update_of_ne hik]
        exact ne_smul_flip_of_ne_zero (hbarynz i) (hρavoid i)
      · rw [hμ₀'def, Function.update_of_ne hik, Function.update_of_ne hi'k]
        exact hnoncol hii' hik hi'k
  have hcol' : ∃ c : ℝ, barycenter (μ₀ k) = c • barycenter (μ₀' j) := by
    rw [hjk']; exact hcol
  haveI := hμ k
  obtain ⟨θ, hdur, hshrinkν, hshrinkμ, hfix⟩ :=
    lemma_3_3 j μ₀' (μ₀ k) hμ' T ε hT hεpos hμs' hμo' (hμs k) (hμo k) hnoncol' hcol'
  rw [hjk'] at hshrinkμ hshrinkν
  refine ⟨θ, hdur, ⟨ε, hεpos, min_le_right _ _, hshrinkμ, hshrinkν, hdisj⟩, ?_⟩
  · intro i hij hik
    have := hfix i hij
    rwa [hμ₀'def, Function.update_of_ne hik] at this

/-- **G6: the colinear insertion step.** Given `DisentangledPrefix` at `k` and a new member `k`
whose (post-`θ`) barycenter direction IS colinear with some other member `j`'s, one more schedule
chunk `θ'` (of any prescribed duration `T`) extends the invariant to `k + 1`: member `k` lands in a
fresh ball disjoint from every already-placed ball and inside the open orthant, and the colinear
partner `j` lands in that same ball (recorded as a separate conjunct, see the limitation note
below). The sibling of `disentangle_insert_noncolinear` above, for the branch where that theorem's
blanket `hnoncol` fails.

**`j` must be a NOT-YET-PLACED member (`hjun : k < j`), and this is FORCED, not a convenience.**
Suppose instead `j < k`, so `j` already owns a ball `B_j = ball (α j) (r j)`. The extended invariant
demands BOTH (clause 3 at `j`) that `j`'s flowed measure still sit inside `B_j` AND (clause 4) that
member `k`'s new ball be disjoint from `B_j`. Every route through `lemma_3_3` available here acts on
the colinear PAIR at once: it drives `j` and `k` into one shared ball around `j`'s own barycenter
direction. Whatever ball member `k` is finally given is therefore centred at a direction read off a
measure living in that shared ball, hence meets `B_j` exactly when the shared ball does, so clause 3
at `j` and clause 4 at `(j, k)` cannot both hold. The unplaced-partner restriction is what makes the
branch consistent at all: unplaced members carry no ball commitment (module docstring), so nothing
is violated by parking `j` alongside `k`.

**Why one phase and not four.** The campaign's planned chain was Phase 1 (colinear-pair shrink,
`exists_shrink_colinear_pair_disjoint_from_bystanders` above) -> Phase 2
(`lemma_3_4_part1_meanField`, barycenters made unequal) -> Phase 3
(`exists_phase3_of_genRestNearBall`, barycenters made fully non-colinear) -> Phase 4 (self-paired
`lemma_3_3` repackaging of member `k` alone). With `j` unplaced -- which the paragraph above shows
is the only consistent reading -- Phase 1 ALREADY discharges all five clauses of the extended
invariant: clauses 1 and 5 are the schedule-generic `attnMeasureFlow_supportedIn_sphere` /
`attnMeasureFlow_exists_map` facts (as in the non-colinear sibling), clause 2 follows from Phase 1's
radius cap (PR #293) instantiated at the orthant slack `ε₀` of
`Metric.isOpen_iff.mp isOpen_orthant ω hωmem`, which puts the confinement ball inside `orthant d`,
together with Phase 1's unconditional bystander-fixing clause for every `i ∉ {j, k}`, and clauses 3
and 4 are Phase 1's own confinement and bystander-disjointness conclusions. Phases 2-4 are therefore
not invoked, and in particular this theorem carries NO `GenRestNearBall` gate: it is unconditional,
unlike `exists_phase3_of_genRestNearBall`.

**Limitation, stated plainly.** What this step does NOT do is BREAK the colinearity: `j` and `k`
leave it sharing one ball and (for all this theorem says) still colinear. That is invisible in
`DisentangledPrefix`, which records no colinearity data, so the invariant is genuinely established;
but a later insertion step that wants to place `j` will find `j` sitting inside member `k`'s ball,
and neither branch can then give `j` a disjoint ball. The extra conclusion conjunct
`supportedIn (attnMeasureFlow (θ ++ θ') (μ₀ j)) (Metric.ball ω ε)` is exposed precisely so that a
caller sees where `j` went instead of having to guess. Resolving the pair (rather than deferring it)
means running Phases 2/3 BEFORE any shrink, on a caller-supplied open carrier `U` containing both
members' mass and disjoint from every placed ball, and only then calling the non-colinear branch;
that route needs `GenRestNearBall` plus a bundle of carrier hypotheses (bystanders supported in
`Uᶜ`, bystanders non-colinear with every `U`-supported measure, and a `U`-uniform version of `hsep`)
and is left for the induction's own assembly.

**Hypothesis shapes.** `hnoncol` is Phase 1's own shape ("every pair not touching member `k` is
non-colinear"): the branch's premise is that member `k` is the single colinearity offender.
`hsep` mirrors the non-colinear sibling's (the already-placed radii are strictly smaller than their
distance to the new confinement centre `ω`), and is fed to Phase 1 through the same
`Option (Fin k)` padding that handles `k = 0`. -/
theorem disentangle_insert_colinear (hd : 2 ≤ d) {N k : ℕ} (hk : k < N)
    (μ₀ : Fin N → Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (θ : AttnSchedule d) (α : Fin k → Eucl d) (r : Fin k → ℝ)
    (hinv : DisentangledPrefix d N k μ₀ θ α r)
    (j : Fin N) (hjun : k < (j : ℕ))
    (hnoncol : Pairwise fun i i' : Fin N => i ≠ (⟨k, hk⟩ : Fin N) → i' ≠ (⟨k, hk⟩ : Fin N) →
        ∀ c : ℝ, barycenter (attnMeasureFlow θ (μ₀ i)) ≠ c • barycenter (attnMeasureFlow θ (μ₀ i')))
    (hcol : ∃ c : ℝ, barycenter (attnMeasureFlow θ (μ₀ ⟨k, hk⟩))
      = c • barycenter (attnMeasureFlow θ (μ₀ j)))
    (hsep : ∀ i : Fin k, r i < dist
        (‖barycenter (attnMeasureFlow θ (μ₀ j))‖⁻¹ • barycenter (attnMeasureFlow θ (μ₀ j))) (α i))
    (T : ℝ) (hT : 0 < T) :
    ∃ θ' : AttnSchedule d, AttnSchedule.durationSum θ' = T ∧
      ∃ (ω : Eucl d) (ε : ℝ), 0 < ε ∧
        supportedIn (attnMeasureFlow (θ ++ θ') (μ₀ j)) (Metric.ball ω ε) ∧
        DisentangledPrefix d N (k + 1) μ₀ (θ ++ θ') (Fin.snoc α ω) (Fin.snoc r ε) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hsph, horth, hball, hballdisj, -⟩ := hinv
  set kk : Fin N := ⟨k, hk⟩ with hkkdef
  have hjk : j ≠ kk := by
    intro h
    rw [h, hkkdef] at hjun
    simp at hjun
  set μ₀' : Fin N → Measure (Eucl d) := fun i => attnMeasureFlow θ (μ₀ i) with hμ₀'def
  have hμ' : ∀ i, IsProbabilityMeasure (μ₀' i) :=
    fun i => haveI := hμ i; isProbabilityMeasure_attnMeasureFlow θ (μ₀ i) (hμs i)
  haveI := hμ' j
  set ω : Eucl d := ‖barycenter (μ₀' j)‖⁻¹ • barycenter (μ₀' j) with hωdef
  -- `ω` is (strictly) in the open orthant, so a small enough ball around it stays inside.
  have hbint : Integrable (fun x : Eucl d => x) (μ₀' j) := integrable_id_of_sphere_support (hsph j)
  have hbmem : barycenter (μ₀' j) ∈ orthant d := barycenter_mem_orthant (hsph j) hbint (horth j)
  have hbpos : 0 < ‖barycenter (μ₀' j)‖ := norm_barycenter_pos_of_orthant (hsph j) hbint (horth j)
  have hωmem : ω ∈ orthant d := by
    intro i
    have hinvpos : (0 : ℝ) < ‖barycenter (μ₀' j)‖⁻¹ := inv_pos.mpr hbpos
    simpa [hωdef] using mul_pos hinvpos (hbmem i)
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.isOpen_iff.mp isOpen_orthant ω hωmem
  -- Phase 1, with the orthant slack `ε₀` as the caller-supplied radius cap.
  obtain ⟨θ', hdur, ⟨ε, hεpos, hεε₀, hshrinkj, hshrinkk, hdisj⟩, hfix⟩ :=
    exists_shrink_colinear_pair_disjoint_from_bystanders hd j kk hjk μ₀' hμ' T hT ε₀ hε₀pos
      hsph horth hnoncol hcol
      (fun o : Option (Fin k) => o.elim (0 : Eucl d) α)
      (fun o : Option (Fin k) => o.elim (-1 : ℝ) r)
      (by
        rintro (_ | i)
        · simp only [Option.elim, dist_zero_right]
          linarith [norm_nonneg ω]
        · exact hsep i)
  have hballorth : Metric.ball ω ε ⊆ orthant d :=
    (Metric.ball_subset_ball hεε₀).trans hε₀sub
  refine ⟨θ', hdur, ω, ε, hεpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The colinear partner `j` shares the new ball (the deferred-conflict record).
    rw [attnMeasureFlow_append]
    exact hshrinkj
  · -- Clause 1 (sphere support): schedule-generic, exactly as in the non-colinear sibling.
    intro i
    rw [attnMeasureFlow_append]
    exact attnMeasureFlow_supportedIn_sphere θ' (attnMeasureFlow θ (μ₀ i))
      (haveI := hμ' i; hsph i)
  · -- Clause 2 (orthant support): the pair sits in `ball ω ε ⊆ ball ω ε₀ ⊆ orthant d`, every other
    -- member is fixed by Phase 1.
    intro i
    rw [attnMeasureFlow_append]
    by_cases hij : i = j
    · subst hij
      exact measure_mono_null (Set.compl_subset_compl.mpr hballorth) hshrinkj
    · by_cases hik : i = kk
      · subst hik
        exact measure_mono_null (Set.compl_subset_compl.mpr hballorth) hshrinkk
      · rw [hfix i hij hik]
        exact horth i
  · -- Clause 3 (ball placement of every placed member, now `i < k + 1`). Already-placed members
    -- are neither `j` (unplaced, `k < j`) nor `k`, so Phase 1 fixes them.
    intro i hik
    rw [attnMeasureFlow_append]
    rcases Fin.eq_castSucc_or_eq_last (⟨i, hik⟩ : Fin (k + 1)) with ⟨i', hi'⟩ | hi'
    · have hval : (i : ℕ) = (i' : ℕ) := by
        have h := congrArg Fin.val hi'; simpa using h
      have hik' : (i : ℕ) < k := hval ▸ i'.isLt
      have hii' : i' = (⟨i, hik'⟩ : Fin k) := Fin.ext hval.symm
      have hfixk : i ≠ kk := by
        intro h
        have hikk : (i : ℕ) = k := by rw [h, hkkdef]
        omega
      have hfixj : i ≠ j := by
        intro h
        rw [h] at hik'
        omega
      rw [hfix i hfixj hfixk, hi', hii']
      simp only [Fin.snoc_castSucc]
      exact hball i hik'
    · have hival : (i : ℕ) = k := by
        have := congrArg Fin.val hi'; simpa using this
      have hieqk : i = kk := by
        apply Fin.ext; simp [hkkdef, hival]
      rw [hi', hieqk]
      simp only [Fin.snoc_last]
      exact hshrinkk
  · -- Clause 4 (pairwise disjoint balls, extended to `k + 1`): Phase 1 chose its radius disjoint
    -- from every already-placed ball.
    intro a b hab
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha'⟩ | ha'
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb'⟩ | hb'
      · rw [ha', hb'] at hab ⊢
        simp only [Fin.snoc_castSucc]
        exact hballdisj (by simpa using (Fin.castSucc_injective k).ne_iff.mp hab)
      · rw [ha', hb']
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact (hdisj (some a')).symm
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', hb'⟩ | hb'
      · rw [ha', hb']
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hdisj (some b')
      · exfalso; apply hab; rw [ha', hb']
  · -- Clause 5 (invertible on-sphere flow map): schedule-generic, as in the non-colinear sibling.
    intro i hik
    haveI := hμ i
    obtain ⟨Φ, Φinv, hΦm, -, hΦinvm, hΦeq, -, hΦinv⟩ :=
      attnMeasureFlow_exists_map (θ ++ θ') (μ₀ i) (hμs i)
    exact ⟨Φ, Φinv, hΦm, hΦinvm, hΦeq, hΦinv⟩

/-! ### The pair-RESOLVING colinear insertion step

`disentangle_insert_colinear` above DEFERS the colinearity: `j` and `k` leave sharing one ball, so
iterating that branch alone cannot close the induction over `N` (a later step wanting to place `j`
finds it inside `k`'s ball). The three declarations below build the variant that BREAKS the
colinearity instead, by running Phases 2/3 FIRST, before any shrink, and only then handing off to
the already-banked non-colinear branch.

**Why this order is forced.** Phase 2 (`barycenter_ne_of_massGapCollapse_meanField`) needs
`hne : μ ≠ ν` for the two acted members. Run BEFORE any shrink, that is
`attnMeasureFlow θ (μ₀ j) ≠ attnMeasureFlow θ (μ₀ k)`, a statable hypothesis about the data the
caller already has. Run AFTER a Phase-1 shrink it is neither statable nor derivable: mean-field flow
maps are measure-DEPENDENT, so `attnMeasureFlow_exists_map` gives no injectivity across two
different measures, and nothing propagates distinctness through the shrink.

**Standing caveat on `GenRestNearBall` (kernel-stated since finding F22).** Phase 3 is gated on
`GenRestNearBall d`, which `Regression/Refuted/HgenRestUnconditionallyFalse.lean` now REFUTES in
the kernel: `genRestNearBall_false : ¬ GenRestNearBall 2` (via the admissible `partTwoMu`/`partTwoNu`
witness pair), on top of `lemma_3_4_part2_hgenRest_unsatisfiable` showing the underlying `hgenRest`
bundle fails for every measure pair at every `2 ≤ d`. So `exists_phase3_nonColinear_symm`,
`exists_phase23_nonColinear`, and `disentangle_insert_colinear_resolving` are kernel-clean but NOT
invocable: the `kernel-clean-not-applicable` pattern, deliberately, exactly as for the already-merged
`exists_phase3_of_genRestNearBall` they are built on. What is banked here is the ARCHITECTURE (the
correct phase order, the carrier bundle, and the hand-off to `disentangle_insert_noncolinear`);
replacing `GenRestNearBall` by a satisfiable Phase-3 non-degeneracy condition (the planned
asymmetric-cap route, `Leaves/AsymmetricMassGapCap.lean`) is a separate open problem, and every
hypothesis OTHER than `hgen` is jointly satisfiable (see the notes on
`disentangle_insert_colinear_resolving` below).

**Role split between the two colinear branches.** `disentangle_insert_colinear` (PR #294) is
UNCONDITIONAL and invocable but only DEFERS the colinearity: the pair leaves sharing one ball, so a
later step cannot place the partner and iterating it alone cannot complete the induction over `N`.
`disentangle_insert_colinear_resolving` (PR #295) genuinely BREAKS the colinearity and is the
induction path, but is gated as above. The induction over `N` becomes assemblable exactly when the
resolving branch's gate is replaced. -/

/-- A sphere-supported measure is supported in `Metric.ball 0 2`: `sphere d` is the unit sphere, so
every point of it has norm `1 < 2`. Used to discharge, vacuously, the ball-confinement clause of
`GenRestNearBall` at the decorative instantiation `center := 0`, `ε' := 2` -- Phase 3 is applied
here BEFORE any shrink, so no genuine confinement is available (nor needed: `GenRestNearBall`
quantifies
over every ball, and a ball containing the whole sphere makes that clause carry no information). -/
theorem supportedIn_ball_two_of_sphere {d : ℕ} {ρ : Measure (Eucl d)}
    (hρ : supportedIn ρ (sphere d)) : supportedIn ρ (Metric.ball (0 : Eucl d) 2) := by
  refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hρ
  intro x hx
  simp only [sphere, Metric.mem_sphere, dist_zero_right] at hx
  simp only [Metric.mem_ball, dist_zero_right, hx]
  norm_num

/-- **Phase 3, in BOTH directions.** `exists_phase3_of_genRestNearBall` (`GenRestNearBall.lean`)
concludes `∀ γ₂, barycenter (flow A) ≠ γ₂ • barycenter (flow B)`, one direction only. The insertion
step needs a `Pairwise` non-colinearity statement, which is symmetric, so the reverse direction is
produced here once and for all by `ne_smul_flip_of_ne_zero`: the flip needs
`barycenter (flow B) ≠ 0`, which follows from `B`'s image staying inside the carrier `U ⊆ orthant d`
(the region-generic conjunct at `S := orthant d`) plus `norm_barycenter_pos_of_orthant`.

The ball-confinement inputs of `exists_phase3_of_genRestNearBall` are instantiated at
`center := 0`, `ε' := 2` (see `supportedIn_ball_two_of_sphere`): this variant applies Phase 3
BEFORE any shrink, so there is no confining ball to point at, and none is needed. -/
theorem exists_phase3_nonColinear_symm {d : ℕ} [NeZero d] (hgen : GenRestNearBall d)
    (A B : Measure (Eucl d)) [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (T : ℝ) (hT : 0 < T) (hAB : A ≠ B)
    (hAs : supportedIn A (sphere d)) (hBs : supportedIn B (sphere d))
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hUorth : U ⊆ orthant d)
    (hAU : supportedIn A U) (hBU : supportedIn B U)
    (hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ barycenter A = γ • barycenter B) :
    ∃ ψ : AttnSchedule d, AttnSchedule.durationSum ψ = T ∧
      (∀ c : ℝ, barycenter (attnMeasureFlow ψ A) ≠ c • barycenter (attnMeasureFlow ψ B)) ∧
      (∀ c : ℝ, barycenter (attnMeasureFlow ψ B) ≠ c • barycenter (attnMeasureFlow ψ A)) ∧
      (∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        supportedIn ρ Uᶜ → attnMeasureFlow ψ ρ = ρ) ∧
      (∀ S : Set (Eucl d), MeasurableSet S → U ⊆ S →
        ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
          supportedIn ρ S → supportedIn (attnMeasureFlow ψ ρ) S) := by
  have horthsub : ∀ ρ : Measure (Eucl d), supportedIn ρ U → supportedIn ρ (orthant d) :=
    fun ρ h => measure_mono_null (Set.compl_subset_compl.mpr hUorth) h
  obtain ⟨ψ, hdur, -, hnc, -, hfix, hreg⟩ :=
    exists_phase3_of_genRestNearBall hgen 0 2 (by norm_num) A B T hT hAB hAs hBs
      (horthsub A hAU) (horthsub B hBU)
      (supportedIn_ball_two_of_sphere hAs) (supportedIn_ball_two_of_sphere hBs)
      hcol U hUopen hAU hBU
  refine ⟨ψ, hdur, hnc, ?_, hfix, hreg⟩
  haveI : IsProbabilityMeasure (attnMeasureFlow ψ B) :=
    isProbabilityMeasure_attnMeasureFlow ψ B hBs
  have hBs' : supportedIn (attnMeasureFlow ψ B) (sphere d) :=
    attnMeasureFlow_supportedIn_sphere ψ B hBs
  have hBo' : supportedIn (attnMeasureFlow ψ B) (orthant d) :=
    hreg (orthant d) isOpen_orthant.measurableSet hUorth B hBs (horthsub B hBU)
  exact ne_smul_flip_of_ne_zero
    (norm_pos_iff.mp (norm_barycenter_pos_of_orthant hBs'
      (integrable_id_of_sphere_support hBs') hBo')) hnc

/-- **Phases 2 and 3 together: a pair of distinct carrier-supported members is made fully
non-colinear.** Phase 2 (`barycenter_ne_of_massGapCollapse_meanField`, kernel-clean and
unconditional) separates the two barycenters; if that already broke colinearity outright, Phase 3
is SKIPPED and its time budget is handed back to the caller through `Tf` (the returned schedule
satisfies `durationSum ψ + Tf = T` with `0 < Tf`, so the caller always has a strictly positive
remaining budget for its own final step, and no identity/filler schedule is ever needed). Otherwise
Phase 3 runs on the ordered pair, and the leftover budget is `T / 3`.

**The `γ`-bookkeeping between the two phases.** Phase 3 needs `barycenter μ = γ • barycenter ν` with
`γ ∈ Ioo 0 1`, while the residual relation after Phase 2 is just some `γ = c`. Positivity of `c` is
forced by the ORTHANT: both barycenters lie in `orthant d` (`barycenter_mem_orthant`), so comparing
coordinate `0` gives `0 < c`. `c = 1` is excluded by Phase 2's own conclusion. `c > 1` is handled by
swapping the two roles (`barycenter ν = c⁻¹ • barycenter μ`) and reading the conclusion off the
other direction of `exists_phase3_nonColinear_symm`, which is why that lemma exposes both.

The bystander-fixing and region-generic conjuncts compose across `θ₂ ++ θ₃` in the obvious way:
`attnMeasureFlow_append` plus the fact that the intermediate measure is again a sphere-supported
probability measure. -/
theorem exists_phase23_nonColinear {d : ℕ} [NeZero d] (hgen : GenRestNearBall d)
    (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hUorth : U ⊆ orthant d)
    (hμU : supportedIn μ U) (hνU : supportedIn ν U) :
    ∃ (ψ : AttnSchedule d) (Tf : ℝ), 0 < Tf ∧ AttnSchedule.durationSum ψ + Tf = T ∧
      (∀ c : ℝ, barycenter (attnMeasureFlow ψ μ) ≠ c • barycenter (attnMeasureFlow ψ ν)) ∧
      (∀ c : ℝ, barycenter (attnMeasureFlow ψ ν) ≠ c • barycenter (attnMeasureFlow ψ μ)) ∧
      (∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        supportedIn ρ Uᶜ → attnMeasureFlow ψ ρ = ρ) ∧
      (∀ S : Set (Eucl d), MeasurableSet S → U ⊆ S →
        ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
          supportedIn ρ S → supportedIn (attnMeasureFlow ψ ρ) S) := by
  have horthsub : ∀ ρ : Measure (Eucl d), supportedIn ρ U → supportedIn ρ (orthant d) :=
    fun ρ h => measure_mono_null (Set.compl_subset_compl.mpr hUorth) h
  -- Phase 2: separate the barycenters (unconditional, no `hgen` needed).
  obtain ⟨θ₂, hdur₂, hbne, -, hfix₂, hreg₂⟩ :=
    barycenter_ne_of_massGapCollapse_meanField μ ν (T / 3) (by linarith) hne hμs hνs
      (horthsub μ hμU) (horthsub ν hνU) U hUopen hμU hνU
  haveI hμ₂p : IsProbabilityMeasure (attnMeasureFlow θ₂ μ) :=
    isProbabilityMeasure_attnMeasureFlow θ₂ μ hμs
  haveI hν₂p : IsProbabilityMeasure (attnMeasureFlow θ₂ ν) :=
    isProbabilityMeasure_attnMeasureFlow θ₂ ν hνs
  have hμ₂s : supportedIn (attnMeasureFlow θ₂ μ) (sphere d) :=
    attnMeasureFlow_supportedIn_sphere θ₂ μ hμs
  have hν₂s : supportedIn (attnMeasureFlow θ₂ ν) (sphere d) :=
    attnMeasureFlow_supportedIn_sphere θ₂ ν hνs
  have hμ₂U : supportedIn (attnMeasureFlow θ₂ μ) U :=
    hreg₂ U hUopen.measurableSet (subset_refl U) μ hμs hμU
  have hν₂U : supportedIn (attnMeasureFlow θ₂ ν) U :=
    hreg₂ U hUopen.measurableSet (subset_refl U) ν hνs hνU
  have hne₂ : attnMeasureFlow θ₂ μ ≠ attnMeasureFlow θ₂ ν := fun h => hbne (by rw [h])
  by_cases hnc : ∀ c : ℝ, barycenter (attnMeasureFlow θ₂ μ)
      ≠ c • barycenter (attnMeasureFlow θ₂ ν)
  · -- Phase 2 alone already resolved the pair: skip Phase 3, hand its budget back.
    have hν₂o : supportedIn (attnMeasureFlow θ₂ ν) (orthant d) := horthsub _ hν₂U
    have hnz : barycenter (attnMeasureFlow θ₂ ν) ≠ 0 :=
      norm_pos_iff.mp (norm_barycenter_pos_of_orthant hν₂s
        (integrable_id_of_sphere_support hν₂s) hν₂o)
    exact ⟨θ₂, T / 3 * 2, by linarith, by rw [hdur₂]; ring, hnc,
      ne_smul_flip_of_ne_zero hnz hnc, hfix₂, hreg₂⟩
  · simp only [ne_eq, not_forall, not_not] at hnc
    obtain ⟨c, hc⟩ := hnc
    have hμ₂o : supportedIn (attnMeasureFlow θ₂ μ) (orthant d) := horthsub _ hμ₂U
    have hν₂o : supportedIn (attnMeasureFlow θ₂ ν) (orthant d) := horthsub _ hν₂U
    have hbμ : barycenter (attnMeasureFlow θ₂ μ) ∈ orthant d :=
      barycenter_mem_orthant hμ₂s (integrable_id_of_sphere_support hμ₂s) hμ₂o
    have hbν : barycenter (attnMeasureFlow θ₂ ν) ∈ orthant d :=
      barycenter_mem_orthant hν₂s (integrable_id_of_sphere_support hν₂s) hν₂o
    have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    -- Orthant positivity forces `0 < c`, Phase 2 forces `c ≠ 1`.
    have hcpos : 0 < c := by
      have h1 := hbμ ⟨0, hd0⟩
      have h2 := hbν ⟨0, hd0⟩
      rw [hc] at h1
      simp only [PiLp.smul_apply, smul_eq_mul] at h1
      nlinarith
    have hcne1 : c ≠ 1 := by
      intro h; rw [h, one_smul] at hc; exact hbne hc
    rcases lt_or_gt_of_ne hcne1 with hlt | hgt
    · obtain ⟨θ₃, hdur₃, hnc₃, hnc₃', hfix₃, hreg₃⟩ :=
        exists_phase3_nonColinear_symm hgen _ _ (T / 3) (by linarith) hne₂ hμ₂s hν₂s
          U hUopen hUorth hμ₂U hν₂U ⟨c, ⟨hcpos, hlt⟩, hc⟩
      refine ⟨θ₂ ++ θ₃, T / 3, by linarith, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [AttnSchedule.durationSum_append, hdur₂, hdur₃]; ring
      · simpa [attnMeasureFlow_append] using hnc₃
      · simpa [attnMeasureFlow_append] using hnc₃'
      · intro ρ _ hρs hρU
        rw [attnMeasureFlow_append, hfix₂ ρ hρs hρU, hfix₃ ρ hρs hρU]
      · intro S hS hUS ρ _ hρs hρS
        rw [attnMeasureFlow_append]
        haveI := isProbabilityMeasure_attnMeasureFlow θ₂ ρ hρs
        exact hreg₃ S hS hUS _ (attnMeasureFlow_supportedIn_sphere θ₂ ρ hρs)
          (hreg₂ S hS hUS ρ hρs hρS)
    · -- `c > 1`: swap the two roles and read the other direction of the symmetric Phase 3.
      have hcne0 : c ≠ 0 := by linarith
      have hc' : barycenter (attnMeasureFlow θ₂ ν)
          = c⁻¹ • barycenter (attnMeasureFlow θ₂ μ) := by
        rw [hc, smul_smul, inv_mul_cancel₀ hcne0, one_smul]
      have hcinv : c⁻¹ ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨inv_pos.mpr hcpos, by rw [inv_lt_one_iff₀]; right; exact hgt⟩
      obtain ⟨θ₃, hdur₃, hnc₃, hnc₃', hfix₃, hreg₃⟩ :=
        exists_phase3_nonColinear_symm hgen _ _ (T / 3) (by linarith) (Ne.symm hne₂) hν₂s hμ₂s
          U hUopen hUorth hν₂U hμ₂U ⟨c⁻¹, hcinv, hc'⟩
      refine ⟨θ₂ ++ θ₃, T / 3, by linarith, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [AttnSchedule.durationSum_append, hdur₂, hdur₃]; ring
      · simpa [attnMeasureFlow_append] using hnc₃'
      · simpa [attnMeasureFlow_append] using hnc₃
      · intro ρ _ hρs hρU
        rw [attnMeasureFlow_append, hfix₂ ρ hρs hρU, hfix₃ ρ hρs hρU]
      · intro S hS hUS ρ _ hρs hρS
        rw [attnMeasureFlow_append]
        haveI := isProbabilityMeasure_attnMeasureFlow θ₂ ρ hρs
        exact hreg₃ S hS hUS _ (attnMeasureFlow_supportedIn_sphere θ₂ ρ hρs)
          (hreg₂ S hS hUS ρ hρs hρS)

/-- **The pair-RESOLVING colinear insertion step.** The sibling of `disentangle_insert_colinear`
that BREAKS the colinearity between the new member `k` and its colinear partner `j` instead of
deferring it: the returned schedule splits as `ψ ++ ψ'`, and the exposed middle conjunct records
that after the FIRST half the WHOLE family is pairwise non-colinear. `j` and `k` therefore do NOT
end up sharing a ball; `j` stays unplaced but now has a barycenter direction not colinear with
anyone else's, so a later insertion step can place it through the non-colinear branch. This is
additive: `disentangle_insert_colinear` is untouched.

**The four steps, in the order that is forced.**
1. Phases 2 and 3 run FIRST, on the pair `(j, k)`, through `exists_phase23_nonColinear`. Doing this
   before any shrink is what makes `hne` (distinctness of the two flowed members) a statable
   hypothesis at all: post-shrink it is neither statable nor derivable, because mean-field flow maps
   are measure-dependent so `attnMeasureFlow_exists_map` gives no cross-measure injectivity.
2. Phase 3's ball-confinement parameters are decorative here (`center := 0`, `ε' := 2`, a ball
   containing the whole sphere), which is exactly what lets Phase 3 precede the shrink.
3. If Phase 2 alone already resolved the pair, Phase 3 is skipped and its duration budget is handed
   to the final step; `exists_phase23_nonColinear` reports the remaining budget as `Tf`.
4. The finish is the ALREADY-BANKED `disentangle_insert_noncolinear` applied on the composed
   schedule `θ ++ ψ`, whose full-family `Pairwise` hypothesis is precisely the conjunct step 1
   establishes. `List.append_assoc` converts its `(θ ++ ψ) ++ ψ'` conclusion into the
   `θ ++ (ψ ++ ψ')` shape stated here.

**The carrier bundle.** Phases 2/3 fix only what lies outside their open carrier `U`, so the caller
must supply `U` together with: `IsOpen U`, `U ⊆ orthant d` (this is what turns the region-generic
conjunct of Phases 2/3 into orthant preservation for the two acted members, i.e. clause 2 of the
invariant), support of both acted members in `U`, and support of every OTHER member in `Uᶜ` (this is
what makes Phases 2/3 fix them literally, preserving clauses 2/3 for the already-placed prefix).
Two further hypotheses are needed because the two acted members MOVE during Phases 2/3, so
statements about the pre-phase family do not transfer: `hbys` (every bystander is non-colinear with
EVERY `U`-supported sphere probability measure, not merely with the pre-phase members) and `hsepU`
(a `U`-uniform form of `disentangle_insert_noncolinear`'s own `hsep`). Both are genuine
strengthenings, carried as standing hypotheses in the same style as `hsep` in leaf 2, to be
established by the induction that eventually consumes this step.

**`j` must be unplaced (`hjun : k < j`),** for the same reason as in `disentangle_insert_colinear`:
`j` is moved by Phases 2/3 (it is inside `U`), so if it already owned a ball, clause 3 of the
invariant would break at `j`. Unplaced members carry no ball commitment (module docstring), so
moving `j` is harmless.

**Gate.** `hgen : GenRestNearBall d` is threaded through UNRESOLVED, and
`Regression/Refuted/HgenRestUnconditionallyFalse.lean` records that it is in fact unconditionally
false for `2 ≤ d`. This theorem is therefore kernel-clean but not currently invocable, deliberately:
what it banks is the phase ordering and the carrier bookkeeping, which are independent of how
Phase 3's non-degeneracy condition is eventually repaired. Every hypothesis other than `hgen` is
jointly satisfiable, e.g. `N = 2`, `k = 0`, `θ = []`, `U = orthant d`, `μ₀ = ![δ_p, δ_q]` for two
distinct points of `sphere d ∩ orthant d`: then `hout`, `hbys`, `hrest` and `hsepU` are vacuous
(there are no bystanders and no placed members) and `hinv` is `DisentangledPrefix … 0` with empty
ball data. -/
theorem disentangle_insert_colinear_resolving {d : ℕ} (hd : 2 ≤ d) {N k : ℕ} (hk : k < N)
    (hgen : GenRestNearBall d)
    (μ₀ : Fin N → Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (θ : AttnSchedule d) (α : Fin k → Eucl d) (r : Fin k → ℝ)
    (hinv : DisentangledPrefix d N k μ₀ θ α r)
    (j : Fin N) (hjun : k < (j : ℕ))
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hUorth : U ⊆ orthant d)
    (hjU : supportedIn (attnMeasureFlow θ (μ₀ j)) U)
    (hkU : supportedIn (attnMeasureFlow θ (μ₀ ⟨k, hk⟩)) U)
    (hout : ∀ i : Fin N, i ≠ j → i ≠ ⟨k, hk⟩ → supportedIn (attnMeasureFlow θ (μ₀ i)) Uᶜ)
    (hne : attnMeasureFlow θ (μ₀ j) ≠ attnMeasureFlow θ (μ₀ ⟨k, hk⟩))
    (hbys : ∀ i : Fin N, i ≠ j → i ≠ ⟨k, hk⟩ → ∀ ρ : Measure (Eucl d),
        IsProbabilityMeasure ρ → supportedIn ρ (sphere d) → supportedIn ρ U →
        ∀ c : ℝ, barycenter (attnMeasureFlow θ (μ₀ i)) ≠ c • barycenter ρ)
    (hrest : Pairwise fun i i' : Fin N => i ≠ j → i ≠ ⟨k, hk⟩ → i' ≠ j → i' ≠ ⟨k, hk⟩ →
        ∀ c : ℝ, barycenter (attnMeasureFlow θ (μ₀ i))
          ≠ c • barycenter (attnMeasureFlow θ (μ₀ i')))
    (hsepU : ∀ i : Fin k, ∀ ρ : Measure (Eucl d), IsProbabilityMeasure ρ →
        supportedIn ρ (sphere d) → supportedIn ρ U →
        r i < dist (‖barycenter ρ‖⁻¹ • barycenter ρ) (α i))
    (T : ℝ) (hT : 0 < T) :
    ∃ ψ ψ' : AttnSchedule d, AttnSchedule.durationSum (ψ ++ ψ') = T ∧
      Pairwise (fun i i' : Fin N => ∀ c : ℝ,
        barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i))
          ≠ c • barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i'))) ∧
      ∃ (ω : Eucl d) (ε : ℝ), 0 < ε ∧
        DisentangledPrefix d N (k + 1) μ₀ (θ ++ (ψ ++ ψ')) (Fin.snoc α ω) (Fin.snoc r ε) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hsph, horth, hball, hballdisj, -⟩ := hinv
  set kk : Fin N := ⟨k, hk⟩ with hkkdef
  have hμ'p : ∀ i, IsProbabilityMeasure (attnMeasureFlow θ (μ₀ i)) :=
    fun i => haveI := hμ i; isProbabilityMeasure_attnMeasureFlow θ (μ₀ i) (hμs i)
  haveI := hμ'p j
  haveI := hμ'p kk
  -- Step 1: Phases 2/3, run BEFORE any shrink.
  obtain ⟨ψ, Tf, hTf, hdursum, hnc1, hnc2, hfix, hreg⟩ :=
    exists_phase23_nonColinear hgen _ _ T hT hne (hsph j) (hsph kk) U hUopen hUorth hjU hkU
  -- Every member outside the carrier is fixed literally; the two acted members stay in `U`.
  have hFbys : ∀ i : Fin N, i ≠ j → i ≠ kk →
      attnMeasureFlow (θ ++ ψ) (μ₀ i) = attnMeasureFlow θ (μ₀ i) := by
    intro i hij hik
    rw [attnMeasureFlow_append]
    exact hfix _ (haveI := hμ'p i; hsph i) (hout i hij hik)
  have hFs : ∀ i : Fin N, supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ i)) (sphere d) := by
    intro i
    rw [attnMeasureFlow_append]
    exact attnMeasureFlow_supportedIn_sphere ψ _ (haveI := hμ'p i; hsph i)
  have hFp : ∀ i : Fin N, IsProbabilityMeasure (attnMeasureFlow (θ ++ ψ) (μ₀ i)) := by
    intro i
    haveI := hμ i
    exact isProbabilityMeasure_attnMeasureFlow (θ ++ ψ) (μ₀ i) (hμs i)
  have hFjU : supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ j)) U := by
    rw [attnMeasureFlow_append]
    exact hreg U hUopen.measurableSet (subset_refl U) _ (hsph j) hjU
  have hFkU : supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ kk)) U := by
    rw [attnMeasureFlow_append]
    exact hreg U hUopen.measurableSet (subset_refl U) _ (hsph kk) hkU
  have horthsub : ∀ ρ : Measure (Eucl d), supportedIn ρ U → supportedIn ρ (orthant d) :=
    fun ρ h => measure_mono_null (Set.compl_subset_compl.mpr hUorth) h
  have hnz : ∀ ρ : Measure (Eucl d), IsProbabilityMeasure ρ → supportedIn ρ (sphere d) →
      supportedIn ρ (orthant d) → barycenter ρ ≠ 0 := by
    intro ρ hρp hρs hρo
    haveI := hρp
    exact norm_pos_iff.mp (norm_barycenter_pos_of_orthant hρs
      (integrable_id_of_sphere_support hρs) hρo)
  have hFjnz : barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ j)) ≠ 0 :=
    hnz _ (hFp j) (hFs j) (horthsub _ hFjU)
  have hFknz : barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ kk)) ≠ 0 :=
    hnz _ (hFp kk) (hFs kk) (horthsub _ hFkU)
  -- Step 2: the whole family is pairwise non-colinear after `θ ++ ψ` (the resolution itself).
  have hpair : Pairwise (fun i i' : Fin N => ∀ c : ℝ,
      barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i))
        ≠ c • barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i'))) := by
    intro a b hab
    by_cases haj : a = j
    · have hbj : b ≠ j := by rw [← haj]; exact Ne.symm hab
      by_cases hbk : b = kk
      · rw [haj, hbk]
        simpa [attnMeasureFlow_append] using hnc1
      · rw [haj, hFbys b hbj hbk]
        exact ne_smul_flip_of_ne_zero hFjnz (hbys b hbj hbk _ (hFp j) (hFs j) hFjU)
    · by_cases hak : a = kk
      · have hbk : b ≠ kk := by rw [← hak]; exact Ne.symm hab
        by_cases hbj : b = j
        · rw [hak, hbj]
          simpa [attnMeasureFlow_append] using hnc2
        · rw [hak, hFbys b hbj hbk]
          exact ne_smul_flip_of_ne_zero hFknz (hbys b hbj hbk _ (hFp kk) (hFs kk) hFkU)
      · rw [hFbys a haj hak]
        by_cases hbj : b = j
        · rw [hbj]
          exact hbys a haj hak _ (hFp j) (hFs j) hFjU
        · by_cases hbk : b = kk
          · rw [hbk]
            exact hbys a haj hak _ (hFp kk) (hFs kk) hFkU
          · rw [hFbys b hbj hbk]
            exact hrest hab haj hak hbj hbk
  -- Step 3: the prefix invariant survives Phases 2/3.
  have hprefix : DisentangledPrefix d N k μ₀ (θ ++ ψ) α r := by
    refine ⟨hFs, ?_, ?_, hballdisj, ?_⟩
    · intro i
      by_cases hij : i = j
      · rw [hij]; exact horthsub _ hFjU
      · by_cases hik : i = kk
        · rw [hik]; exact horthsub _ hFkU
        · rw [hFbys i hij hik]; exact horth i
    · intro i hik
      have hij : i ≠ j := by intro h; rw [h] at hik; omega
      have hikk : i ≠ kk := by
        intro h; rw [h, hkkdef] at hik; simp at hik
      rw [hFbys i hij hikk]; exact hball i hik
    · intro i _
      haveI := hμ i
      obtain ⟨Φ, Φinv, hΦm, -, hΦinvm, hΦeq, -, hΦinv⟩ :=
        attnMeasureFlow_exists_map (θ ++ ψ) (μ₀ i) (hμs i)
      exact ⟨Φ, Φinv, hΦm, hΦinvm, hΦeq, hΦinv⟩
  have hsep : ∀ i : Fin k, r i < dist
      (‖barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ ⟨k, hk⟩))‖⁻¹ •
        barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ ⟨k, hk⟩))) (α i) :=
    fun i => hsepU i _ (hFp kk) (hFs kk) hFkU
  -- Step 4: hand off to the already-banked non-colinear branch.
  obtain ⟨ψ', hdur', ω, ε, hεpos, hprefix'⟩ :=
    disentangle_insert_noncolinear hk μ₀ hμ hμs (θ ++ ψ) α r hprefix hpair hsep Tf hTf
  refine ⟨ψ, ψ', ?_, hpair, ω, ε, hεpos, ?_⟩
  · simp only [AttnSchedule.durationSum_append, hdur']
    exact hdursum
  · rw [← List.append_assoc]
    exact hprefix'

end MeasureToMeasure.Leaves
