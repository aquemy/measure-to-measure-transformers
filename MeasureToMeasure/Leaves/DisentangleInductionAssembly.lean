import MeasureToMeasure.Leaves.DisentangleResolveFamily
import MeasureToMeasure.Leaves.UniformRadiusPackingUnit
import MeasureToMeasure.Leaves.OrthantSameRayBridge

/-!
# The induction over `N`: every member of an exclusive-support family placed in its own ball

The final assembly of `exists_disentangling_balls`'s static-cap re-base: the strong induction that
places all `N` members of the family into pairwise-disjoint balls,
`disentangled_prefix_of_exclusive_supports`. The chain is

* base rotation (`exclusiveSupportFamily_rotate_family_to_orthant`, one chunk of duration `τ`):
  the whole family moved into sphere-and-orthant support by ONE shared injective map, which
  transports the `ExclusiveSupportFamily` gate for free;
* Phase R (`exists_resolve_family_noncolinear`, `N` chunks): every member collapsed once against
  all other members' barycenter lines, so the family leaves pairwise non-colinear, the blanket
  shape `lemma_3_3`'s `hnoncol` needs;
* placement induction (`key` below, `N` chunks): members are placed one at a time through the
  avoiding insertion step `disentangle_insert_noncolinear_avoiding`, ALWAYS on its non-colinear
  branch (the colinear branch is never entered, Phase R having emptied it).

With `τ := T / (2N + 1)` the `1 + N + N` chunks telescope to total duration EXACTLY `T`.

## The placement invariant

Beyond `DisentangledPrefix` itself, the induction carries three records, and each survives an
insertion step only because the step literally fixes every unmoved member (the bystander-fixing
conjunct exposed in PR #319):

* radii positivity (`Fin.snoc` of the previous record with the fresh `ε > 0`);
* whole-family pairwise non-colinearity: the placed member's new barycenter lies in the CLOSED
  fresh ball (`barycenter_mem_closedBall`, which is why closed-ball avoidance was load-bearing in
  PR #319), and the step's line-avoidance conjunct keeps that ball off every other member's
  barycenter line; the reverse direction is `ne_smul_flip_of_ne_zero` on nonzero orthant
  barycenters;
* the separation feed (`hsep` of the NEXT step): every unplaced member's normalized barycenter
  direction stays clear of every placed ball, read off the same line-avoidance conjunct at
  `c := ‖barycenter‖⁻¹` for the fresh ball and inherited (bystander barycenters being literally
  fixed) for the old balls.

M3b/mid-level staging: the `G-unwrap` step consumes this below: the uniformization round
(`disentangled_prefix_uniformize`) and the gated companion
(`exists_disentangling_balls_of_exclusive_supports`, finding F27), which proves the
`exists_disentangling_balls` conclusion byte-identical under the exclusivity gate; see the
`exists-disentangling-balls-campaign` notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule AttnParams attnMeasureFlow)
open MeasureToMeasure.Foundations (isProbabilityMeasure_attnMeasureFlow
  attnMeasureFlow_supportedIn_sphere attnMeasureFlow_append attnMeasureFlow_exists_map)
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Ball-supported sphere measures have their barycenter in the closed ball.** The barycenter
minus the center is `∫ (y - c) dμ`, whose norm is at most the essential bound `ε` on `‖y - c‖`
(probability measure). Non-strict on the boundary, which is exactly why the avoidance conjuncts of
`disentangle_insert_noncolinear_avoiding` are stated for the CLOSED ball. -/
theorem barycenter_mem_closedBall {μ : Measure (Eucl d)} [IsProbabilityMeasure μ]
    (hμs : supportedIn μ (sphere d)) {c : Eucl d} {ε : ℝ}
    (hμb : supportedIn μ (Metric.ball c ε)) :
    barycenter μ ∈ Metric.closedBall c ε := by
  have hint : Integrable (fun y : Eucl d => y) μ := integrable_id_of_sphere_support hμs
  have hae : ∀ᵐ y ∂μ, ‖y - c‖ ≤ ε := by
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) hμb
    simp only [Set.mem_setOf_eq, not_le] at hy
    simp only [Set.mem_compl_iff, Metric.mem_ball, dist_eq_norm, not_lt]
    exact hy.le
  have hsub : ∫ y, (y - c) ∂μ = barycenter μ - c := by
    rw [integral_sub hint (integrable_const c), integral_const]
    simp [barycenter]
  have hle := norm_integral_le_of_norm_le_const (μ := μ) hae
  rw [hsub] at hle
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa [measureReal_def] using hle

set_option maxHeartbeats 1000000 in
/-- **The strong induction over `N`: every member of an exclusive-support family lands in its own
ball, in total duration exactly `T`.** Under the standing family hypotheses of
`exists_disentangling_balls` (probability members, sphere support, a shared missing direction)
plus the `ExclusiveSupportFamily` gate, some schedule `θ` of duration exactly `T` establishes the
FULL prefix invariant `DisentangledPrefix d N N` with strictly positive radii: every member is
confined to its own ball, the balls are pairwise disjoint, and every member's flow is realized by
a measurable map with a measurable on-sphere inverse. See the module docstring for the
base-rotation / Phase-R / placement chain and the placement invariant.

The final conjunct additionally exposes the WHOLE-FAMILY pairwise non-colinearity of the flowed
barycenters, which the placement induction carries anyway (its `key` invariant) and which the
`G-unwrap` uniformization round (`disentangled_prefix_uniformize`) needs: per-member ball
disjointness alone does NOT imply it (two disjoint balls can straddle one ray), so discarding it
here would make the final shrink round unassemblable. -/
theorem disentangled_prefix_of_exclusive_supports (hd : 3 ≤ d) {N : ℕ}
    (μ₀ : Fin N → Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hmiss : SharedMissingDirection μ₀) (hgate : ExclusiveSupportFamily μ₀)
    (T : ℝ) (hT : 0 < T) :
    ∃ (θ : AttnSchedule d) (α : Fin N → Eucl d) (r : Fin N → ℝ),
      (∀ i, 0 < r i) ∧ AttnSchedule.durationSum θ = T ∧
      DisentangledPrefix d N N μ₀ θ α r ∧
      Pairwise fun i j : Fin N => ∀ c : ℝ,
        barycenter (attnMeasureFlow θ (μ₀ i)) ≠ c • barycenter (attnMeasureFlow θ (μ₀ j)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd2 : 2 ≤ d := by omega
  have hden : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
  have hden' : (2 * (N : ℝ) + 1) ≠ 0 := ne_of_gt hden
  set τ : ℝ := T / (2 * (N : ℝ) + 1) with hτdef
  have hτ : 0 < τ := div_pos hT hden
  -- generic per-member facts, at any schedule
  have hFp : ∀ (θ : AttnSchedule d) (i : Fin N),
      IsProbabilityMeasure (attnMeasureFlow θ (μ₀ i)) := fun θ i =>
    haveI := hμ i; isProbabilityMeasure_attnMeasureFlow θ (μ₀ i) (hμs i)
  have hFs : ∀ (θ : AttnSchedule d) (i : Fin N),
      supportedIn (attnMeasureFlow θ (μ₀ i)) (sphere d) := fun θ i =>
    haveI := hμ i; attnMeasureFlow_supportedIn_sphere θ (μ₀ i) (hμs i)
  have hbnz : ∀ (θ : AttnSchedule d) (i : Fin N),
      supportedIn (attnMeasureFlow θ (μ₀ i)) (orthant d) →
      barycenter (attnMeasureFlow θ (μ₀ i)) ≠ 0 := by
    intro θ i ho
    haveI := hFp θ i
    exact norm_pos_iff.mp (norm_barycenter_pos_of_orthant (hFs θ i)
      (integrable_id_of_sphere_support (hFs θ i)) ho)
  -- base rotation (duration τ), transporting the exclusivity gate
  obtain ⟨θ₀, _hsw, hdur₀, hso, hexcl'⟩ :=
    exclusiveSupportFamily_rotate_family_to_orthant μ₀ hμ hd2 hμs hmiss hgate
      (τ / 2) (by linarith)
  have hdur₀' : AttnSchedule.durationSum θ₀ = τ := by rw [hdur₀]; ring
  -- Phase R (duration N * τ) on the rotated family
  obtain ⟨ψR, hdurR, hRs, hRo, hRnc⟩ :=
    exists_resolve_family_noncolinear hd2 (fun i => attnMeasureFlow θ₀ (μ₀ i))
      (fun i => hFp θ₀ i) (fun i => (hso i).1) (fun i => (hso i).2) hexcl' τ hτ
  -- the placement induction over the number of already-placed members
  have key : ∀ k : ℕ, k ≤ N → ∃ (θ : AttnSchedule d) (α : Fin k → Eucl d) (r : Fin k → ℝ),
      AttnSchedule.durationSum θ = ((N : ℝ) + 1 + (k : ℝ)) * τ ∧
      DisentangledPrefix d N k μ₀ θ α r ∧
      (∀ a, 0 < r a) ∧
      (Pairwise fun i j : Fin N => ∀ c : ℝ,
        barycenter (attnMeasureFlow θ (μ₀ i)) ≠ c • barycenter (attnMeasureFlow θ (μ₀ j))) ∧
      (∀ mIdx : Fin N, k ≤ (mIdx : ℕ) → ∀ a : Fin k,
        r a < dist (‖barycenter (attnMeasureFlow θ (μ₀ mIdx))‖⁻¹ •
          barycenter (attnMeasureFlow θ (μ₀ mIdx))) (α a)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨θ₀ ++ ψR, Fin.elim0, Fin.elim0, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [AttnSchedule.durationSum_append, hdur₀', hdurR]
        push_cast
        ring
      · intro i
        rw [attnMeasureFlow_append]
        exact hRs i
      · intro i
        rw [attnMeasureFlow_append]
        exact hRo i
      · intro i hik
        exact absurd hik (Nat.not_lt_zero _)
      · intro a b _
        exact a.elim0
      · intro i hik
        exact absurd hik (Nat.not_lt_zero _)
      · intro a
        exact a.elim0
      · intro i j hij c
        simp only [attnMeasureFlow_append]
        exact hRnc hij c
      · intro mIdx _ a
        exact a.elim0
    | succ k ih =>
      intro hk1
      obtain ⟨θ, α, r, hdur, hpre, hrpos, hnc, hsep⟩ := ih (by omega)
      have hkN : k < N := by omega
      -- the avoiding insertion step, on its non-colinear branch, with no extra avoided points
      obtain ⟨θ', hdur', ω, ε, hεpos, hωnorm, -, hlineav, hfixE, hpre'⟩ :=
        disentangle_insert_noncolinear_avoiding hkN μ₀ hμ hμs θ α r hpre hnc
          (fun a => hsep ⟨k, hkN⟩ (le_refl k) a) (m := 0) Fin.elim0
          (fun l => l.elim0) τ hτ
      -- the freshly placed member's new barycenter lies in the CLOSED fresh ball
      have hball' := hpre'.2.2.1
      have hik : ((⟨k, hkN⟩ : Fin N) : ℕ) < k + 1 := Nat.lt_succ_self k
      have hidx : (⟨((⟨k, hkN⟩ : Fin N) : ℕ), hik⟩ : Fin (k + 1)) = Fin.last k :=
        Fin.ext rfl
      have hkkball := hball' ⟨k, hkN⟩ hik
      rw [hidx, Fin.snoc_last, Fin.snoc_last] at hkkball
      haveI := hFp (θ ++ θ') ⟨k, hkN⟩
      have hbmem : barycenter (attnMeasureFlow (θ ++ θ') (μ₀ ⟨k, hkN⟩)) ∈
          Metric.closedBall ω ε :=
        barycenter_mem_closedBall (hFs (θ ++ θ') ⟨k, hkN⟩) hkkball
      -- one direction of the new non-colinearity, against every other member
      have hnewdir : ∀ i : Fin N, i ≠ ⟨k, hkN⟩ → ∀ c : ℝ,
          barycenter (attnMeasureFlow (θ ++ θ') (μ₀ ⟨k, hkN⟩)) ≠
            c • barycenter (attnMeasureFlow (θ ++ θ') (μ₀ i)) := by
        intro i hi c he
        rw [hfixE i hi] at he
        exact hlineav i hi c (he ▸ hbmem)
      refine ⟨θ ++ θ', Fin.snoc α ω, Fin.snoc r ε, ?_, hpre', ?_, ?_, ?_⟩
      · rw [AttnSchedule.durationSum_append, hdur, hdur']
        push_cast
        ring
      · intro a
        rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha'⟩ | ha'
        · rw [ha']
          simp only [Fin.snoc_castSucc]
          exact hrpos a'
        · rw [ha']
          simp only [Fin.snoc_last]
          exact hεpos
      · intro i j hij c
        by_cases hi : i = ⟨k, hkN⟩
        · subst hi
          exact hnewdir j (Ne.symm hij) c
        · by_cases hj : j = ⟨k, hkN⟩
          · subst hj
            rw [hfixE i hi]
            refine ne_smul_flip_of_ne_zero (hbnz θ i (hpre.2.1 i)) (fun c' => ?_) c
            have hnd := hnewdir i hi c'
            rwa [hfixE i hi] at hnd
          · rw [hfixE i hi, hfixE j hj]
            exact hnc hij c
      · intro mIdx hm a
        have hmval : (mIdx : ℕ) ≠ k := by omega
        have hmne : mIdx ≠ ⟨k, hkN⟩ := fun h => hmval (by rw [h])
        rw [hfixE mIdx hmne]
        rcases Fin.eq_castSucc_or_eq_last a with ⟨a', ha'⟩ | ha'
        · rw [ha']
          simp only [Fin.snoc_castSucc]
          exact hsep mIdx (by omega) a'
        · rw [ha']
          simp only [Fin.snoc_last]
          have hnot := hlineav mIdx hmne
            (‖barycenter (attnMeasureFlow θ (μ₀ mIdx))‖⁻¹)
          exact not_le.mp (fun hle => hnot (Metric.mem_closedBall.mpr hle))
  obtain ⟨θfin, α, r, hdurfin, hprefin, hrposfin, hncfin, -⟩ := key N (le_refl N)
  refine ⟨θfin, α, r, hrposfin, ?_, hprefin, hncfin⟩
  rw [hdurfin, hτdef]
  field_simp
  ring

/-! ### The G-unwrap uniformization round

`DisentangledPrefix` at `k = N` places every member in its OWN ball, with per-member radii and
non-unit centers. `exists_disentangling_balls`'s conclusion instead wants ONE uniform radius
`rU < 1`, UNIT centers, and `2 rU` center separation. The per-member/uniform mismatch is real:
confinement in `ball (α i) (r i)` gives nothing at a smaller radius (ball support is not monotone
under shrinking), so a final, load-bearing shrink round is run below: each member is re-shrunk
once, by the banked self-pairing trick (`lemma_3_3` with `ν₀ :=` the member itself), onto its
CURRENT normalized barycenter direction, with the uniform target radius coming from the abstract
packing lemma (`exists_uniform_radius_of_pairwise_ne_unit`, applied, never re-elaborated, per the
`Eucl d` instance-heaviness note in `UniformRadiusPackingUnit.lean`). -/

/-- **Line-through-a-far-unit-direction avoidance.** For unit vectors `u, w` with nonnegative
inner product (e.g. two orthant directions) separated by `2 rU ≤ dist u w`, NO point of
`closedBall u rU` is a scalar multiple of `w`: the squared distance from `u` to `c • w` is
`1 - 2 c ⟪u, w⟫ + c² ≥ 1 - ⟪u, w⟫² ≥ 1 - ⟪u, w⟫ = dist² / 2 ≥ 2 rU²`, strictly beyond `rU²`.
(Nonnegativity of `⟪u, w⟫` is load-bearing: for nearly-antipodal unit vectors the line through
`w` passes arbitrarily close to `u` even at large `dist u w`.) During the uniformization round
this is what keeps an already-shrunk member's barycenter, trapped in `closedBall (ω a) rU`, off
every not-yet-shrunk member's barycenter LINE. -/
theorem ne_smul_of_mem_closedBall_unit_sep {u w p : Eucl d} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hinner : 0 ≤ ⟪u, w⟫) {rU : ℝ} (hr : 0 < rU) (hsep : 2 * rU ≤ dist u w)
    (hp : p ∈ Metric.closedBall u rU) : ∀ c : ℝ, p ≠ c • w := by
  intro c hpc
  have hdp : dist u p ≤ rU := by rw [dist_comm]; exact Metric.mem_closedBall.mp hp
  have ht1 : ⟪u, w⟫ ≤ 1 := by
    have := real_inner_le_norm u w
    rwa [hu, hw, one_mul] at this
  have hexp : dist u (c • w) ^ 2 = 1 - 2 * (c * ⟪u, w⟫) + c ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, hw]
    simp [sq_abs]
  have hdsq : dist u w ^ 2 = 2 - 2 * ⟪u, w⟫ := by
    rw [dist_eq_norm, norm_sub_sq_real, hu, hw]
    ring
  have hsep2 : (2 * rU) ^ 2 ≤ dist u w ^ 2 := by
    nlinarith [dist_nonneg (x := u) (y := w)]
  have hpc' : dist u p = dist u (c • w) := by rw [hpc]
  nlinarith [sq_nonneg (c - ⟪u, w⟫), dist_nonneg (x := u) (y := p)]

set_option maxHeartbeats 1000000 in
/-- **The uniformization round: from the full prefix to one uniform radius at unit centers.**
Given `DisentangledPrefix` at `k = N` together with the whole-family barycenter non-colinearity
(both exactly as `disentangled_prefix_of_exclusive_supports` returns them), one further schedule
chunk `θ'` of any prescribed duration `Tlast` re-confines every member into the ball of ONE
uniform radius `rU < 1` around its normalized barycenter direction `α' i` (unit vectors, pairwise
`2 rU`-separated) -- the exact geometric package `exists_disentangling_balls`'s conclusion wants.

The round runs `N` sequential self-paired `lemma_3_3` shrinks (companion `ν₀ :=` the member
itself, the `c = 1` colinearity witness), each of duration `Tlast / N` and target radius
`min rU ε₀` (`ε₀` the orthant slack at the center, keeping the confinement ball inside the open
orthant), each fixing every other member exactly (`lemma_3_3`'s bystander clause). The blanket
`hnoncol` `lemma_3_3` demands is RE-DERIVED at every step from three sources: untouched pairs keep
the input non-colinearity; two already-shrunk members sit in `2 rU`-separated unit-center balls
(`barycenter_ne_smul_of_separated_balls`); and a shrunk/unshrunk pair is split by
`ne_smul_of_mem_closedBall_unit_sep` (the shrunk barycenter is trapped in the closed ball by
`barycenter_mem_closedBall`, and the unshrunk barycenter LINE stays `√2 rU` clear of it),
flipped with `ne_smul_flip_of_ne_zero` for the reverse order. -/
theorem disentangled_prefix_uniformize (hd : 3 ≤ d) {N : ℕ}
    (μ₀ : Fin N → Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (θ : AttnSchedule d) (α : Fin N → Eucl d) (r : Fin N → ℝ)
    (hprefix : DisentangledPrefix d N N μ₀ θ α r)
    (hnoncol : Pairwise fun i j : Fin N => ∀ c : ℝ,
      barycenter (attnMeasureFlow θ (μ₀ i)) ≠ c • barycenter (attnMeasureFlow θ (μ₀ j)))
    (Tlast : ℝ) (hT : 0 < Tlast) :
    ∃ (θ' : AttnSchedule d) (α' : Fin N → Eucl d) (rU : ℝ),
      AttnSchedule.durationSum θ' = Tlast ∧ 0 < rU ∧ rU < 1 ∧
      (∀ i, ‖α' i‖ = 1) ∧
      (∀ i j, i ≠ j → 2 * rU ≤ dist (α' i) (α' j)) ∧
      (∀ i, supportedIn (attnMeasureFlow (θ ++ θ') (μ₀ i)) (Metric.ball (α' i) rU)) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hsph, horth, -, -, -⟩ := hprefix
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- `N = 0`: one arbitrary block of duration `Tlast`; every member clause is vacuous.
    subst hN0
    refine ⟨[⟨0, 0, 0, 0, 0, Tlast, hT.le⟩], Fin.elim0, 1 / 2,
      ?_, by norm_num, by norm_num, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    simp [AttnSchedule.durationSum]
  haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  -- barycenter data of the incoming (post-`θ`) family
  have hprob : ∀ i, IsProbabilityMeasure (attnMeasureFlow θ (μ₀ i)) := fun i =>
    haveI := hμ i; isProbabilityMeasure_attnMeasureFlow θ (μ₀ i) (hμs i)
  have hint : ∀ i, Integrable (fun x : Eucl d => x) (attnMeasureFlow θ (μ₀ i)) := fun i =>
    integrable_id_of_sphere_support (hsph i)
  have hBorth : ∀ i, barycenter (attnMeasureFlow θ (μ₀ i)) ∈ orthant d := fun i =>
    haveI := hprob i; barycenter_mem_orthant (hsph i) (hint i) (horth i)
  have hBpos : ∀ i, 0 < ‖barycenter (attnMeasureFlow θ (μ₀ i))‖ := fun i =>
    haveI := hprob i; norm_barycenter_pos_of_orthant (hsph i) (hint i) (horth i)
  have hBnz : ∀ i, barycenter (attnMeasureFlow θ (μ₀ i)) ≠ 0 := fun i =>
    norm_pos_iff.mp (hBpos i)
  set ω : Fin N → Eucl d := fun i =>
    ‖barycenter (attnMeasureFlow θ (μ₀ i))‖⁻¹ • barycenter (attnMeasureFlow θ (μ₀ i)) with hωdef
  have hωeq : ∀ i, ω i =
      ‖barycenter (attnMeasureFlow θ (μ₀ i))‖⁻¹ • barycenter (attnMeasureFlow θ (μ₀ i)) :=
    fun _ => rfl
  have hωunit : ∀ i, ‖ω i‖ = 1 := fun i => by
    rw [hωeq i, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hBnz i))]
  have hωorth : ∀ i, ω i ∈ orthant d := by
    intro i k
    have hinvpos : (0 : ℝ) < ‖barycenter (attnMeasureFlow θ (μ₀ i))‖⁻¹ := inv_pos.mpr (hBpos i)
    simpa [hωeq i] using mul_pos hinvpos (hBorth i k)
  -- normalized directions are pairwise distinct: equality would be a colinearity witness
  have hωne : Pairwise fun i j : Fin N => ω i ≠ ω j := by
    intro i j hij he
    refine hnoncol hij (‖barycenter (attnMeasureFlow θ (μ₀ i))‖ *
      ‖barycenter (attnMeasureFlow θ (μ₀ j))‖⁻¹) ?_
    calc barycenter (attnMeasureFlow θ (μ₀ i))
        = ‖barycenter (attnMeasureFlow θ (μ₀ i))‖ • ω i := by
          rw [hωeq i, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hBnz i)), one_smul]
      _ = ‖barycenter (attnMeasureFlow θ (μ₀ i))‖ • ω j := by rw [he]
      _ = (‖barycenter (attnMeasureFlow θ (μ₀ i))‖ *
            ‖barycenter (attnMeasureFlow θ (μ₀ j))‖⁻¹) •
            barycenter (attnMeasureFlow θ (μ₀ j)) := by rw [hωeq j, smul_smul]
  -- the uniform packing radius (APPLY the banked abstract lemma, never re-elaborate near `Eucl d`)
  obtain ⟨rU, hrU0, hrU1, hrUsep⟩ := exists_uniform_radius_of_pairwise_ne_unit ω hωunit hωne
  set τ : ℝ := Tlast / (N : ℝ) with hτdef
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hτ : 0 < τ := div_pos hT hNR
  -- the shrink round, one member at a time, each fixing all the others
  have key : ∀ m : ℕ, m ≤ N → ∃ ψ : AttnSchedule d,
      AttnSchedule.durationSum ψ = (m : ℝ) * τ ∧
      (∀ i : Fin N, supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ i)) (orthant d)) ∧
      (∀ a : Fin N, (a : ℕ) < m →
        supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ a)) (Metric.ball (ω a) rU)) ∧
      (∀ u : Fin N, m ≤ (u : ℕ) →
        attnMeasureFlow (θ ++ ψ) (μ₀ u) = attnMeasureFlow θ (μ₀ u)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨[], by simp, ?_, ?_, ?_⟩
      · intro i
        rw [List.append_nil]
        exact horth i
      · intro a ha
        exact absurd ha (Nat.not_lt_zero _)
      · intro u _
        rw [List.append_nil]
    | succ m ih =>
      intro hm1
      obtain ⟨ψ, hdur, ho, hballs, hfix⟩ := ih (by omega)
      have hmN : m < N := by omega
      set jm : Fin N := ⟨m, hmN⟩ with hjmdef
      -- generic facts about the current (post-`θ ++ ψ`) family
      have hcurprob : ∀ i, IsProbabilityMeasure (attnMeasureFlow (θ ++ ψ) (μ₀ i)) := fun i =>
        haveI := hμ i; isProbabilityMeasure_attnMeasureFlow (θ ++ ψ) (μ₀ i) (hμs i)
      have hcurs : ∀ i, supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ i)) (sphere d) := fun i =>
        haveI := hμ i; attnMeasureFlow_supportedIn_sphere (θ ++ ψ) (μ₀ i) (hμs i)
      have hjmfix : attnMeasureFlow (θ ++ ψ) (μ₀ jm) = attnMeasureFlow θ (μ₀ jm) :=
        hfix jm (le_refl m)
      -- shrunk-vs-unshrunk non-colinearity, the one direction needing the line-avoidance lemma
      have hkey1 : ∀ a u : Fin N, (a : ℕ) < m → m ≤ (u : ℕ) → ∀ c : ℝ,
          barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ a)) ≠
            c • barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ u)) := by
        intro a u ha hu c hEq
        have hane : a ≠ u := by
          intro h
          rw [h] at ha
          omega
        haveI := hcurprob a
        have hmem : barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ a)) ∈
            Metric.closedBall (ω a) rU :=
          barycenter_mem_closedBall (hcurs a) (hballs a ha)
        have hBu : attnMeasureFlow (θ ++ ψ) (μ₀ u) = attnMeasureFlow θ (μ₀ u) := hfix u hu
        have hrw : c • barycenter (attnMeasureFlow θ (μ₀ u)) =
            (c * ‖barycenter (attnMeasureFlow θ (μ₀ u))‖) • ω u := by
          rw [hωeq u, smul_smul, mul_assoc,
            mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hBnz u)), mul_one]
        rw [hBu, hrw] at hEq
        exact ne_smul_of_mem_closedBall_unit_sep (hωunit a) (hωunit u)
          (inner_nonneg_of_orthant (hωorth a) (orthant_subset_closedOrthant (hωorth u)))
          hrU0 (hrUsep a u hane) hmem _ hEq
      -- the blanket non-colinearity of the current family, re-derived for this step
      have hcur : Pairwise fun i j : Fin N => ∀ c : ℝ,
          barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i)) ≠
            c • barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ j)) := by
        intro i j hij
        rcases Nat.lt_or_ge (i : ℕ) m with hi | hi
        · rcases Nat.lt_or_ge (j : ℕ) m with hj | hj
          · haveI := hcurprob i
            haveI := hcurprob j
            exact barycenter_ne_smul_of_separated_balls (hωunit i) (hωunit j) hrU0
              (hrUsep i j hij) (hcurs i) (hcurs j) (hballs i hi) (hballs j hj) (ho i) (ho j)
          · exact hkey1 i j hi hj
        · rcases Nat.lt_or_ge (j : ℕ) m with hj | hj
          · refine ne_smul_flip_of_ne_zero ?_ (hkey1 j i hj hi)
            rw [hfix i hi]
            exact hBnz i
          · intro c
            rw [hfix i hi, hfix j hj]
            exact hnoncol hij c
      -- the self-paired shrink of member `m`, radius capped by the orthant slack
      obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.isOpen_iff.mp isOpen_orthant (ω jm) (hωorth jm)
      have hεpos : 0 < min rU ε₀ := lt_min hrU0 hε₀pos
      haveI := hcurprob jm
      obtain ⟨θ'', hdur'', -, hshrinkμ, hfix''⟩ :=
        lemma_3_3 jm (fun i => attnMeasureFlow (θ ++ ψ) (μ₀ i))
          (attnMeasureFlow (θ ++ ψ) (μ₀ jm)) hcurprob τ (min rU ε₀) hτ hεpos
          hcurs ho (hcurs jm) (ho jm) hcur ⟨1, (one_smul ℝ _).symm⟩
      have hcenter : ‖barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ jm))‖⁻¹ •
          barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ jm)) = ω jm := by
        rw [hjmfix, hωeq jm]
      rw [hcenter] at hshrinkμ
      refine ⟨ψ ++ θ'', ?_, ?_, ?_, ?_⟩
      · rw [AttnSchedule.durationSum_append, hdur, hdur'']
        push_cast
        ring
      · -- orthant support of every member survives the step
        intro i
        rw [← List.append_assoc, attnMeasureFlow_append]
        by_cases hij : i = jm
        · subst hij
          have hsub : Metric.ball (ω jm) (min rU ε₀) ⊆ orthant d :=
            (Metric.ball_subset_ball (min_le_right rU ε₀)).trans hε₀sub
          exact measure_mono_null (Set.compl_subset_compl.mpr hsub) hshrinkμ
        · rw [hfix'' i hij]
          exact ho i
      · -- ball placement, extended to `m + 1`
        intro a ha1
        rw [← List.append_assoc, attnMeasureFlow_append]
        by_cases haj : a = jm
        · subst haj
          have hsub : Metric.ball (ω jm) (min rU ε₀) ⊆ Metric.ball (ω jm) rU :=
            Metric.ball_subset_ball (min_le_left rU ε₀)
          exact measure_mono_null (Set.compl_subset_compl.mpr hsub) hshrinkμ
        · have ham : (a : ℕ) < m := by
            rcases Nat.lt_succ_iff_lt_or_eq.mp ha1 with h | h
            · exact h
            · exact absurd (Fin.ext h) haj
          rw [hfix'' a haj]
          exact hballs a ham
      · -- everyone not yet shrunk is fixed by this step too
        intro u hu
        have hune : u ≠ jm := by
          intro h
          rw [h] at hu
          simp only [hjmdef] at hu
          omega
        rw [← List.append_assoc, attnMeasureFlow_append, hfix'' u hune, hfix u (by omega)]
  obtain ⟨ψ, hdurψ, -, hballs, -⟩ := key N (le_refl N)
  have hNne : (N : ℝ) ≠ 0 := hNR.ne'
  refine ⟨ψ, ω, rU, ?_, hrU0, hrU1, hωunit, hrUsep, fun i => hballs i i.isLt⟩
  rw [hdurψ, hτdef]
  field_simp

/-- **The gated companion of the `exists_disentangling_balls` axiom.** Under the axiom's exact
hypothesis bundle PLUS the `ExclusiveSupportFamily` gate (every member owns a support point
exclusive to it), the axiom's conclusion holds verbatim: one schedule of duration exactly `T`
concentrates each member into the ball of one uniform radius `r < 1` around a unit direction
`α i`, the directions pairwise `2 r`-separated, with per-member measurable flow maps and
measurable on-sphere inverses. Assembly: the strong induction
(`disentangled_prefix_of_exclusive_supports`, duration `T / 2`) followed by the uniformization
round (`disentangled_prefix_uniformize`, duration `T / 2`); the flow maps are
`attnMeasureFlow_exists_map` on the composite schedule.

**Honest-narrowing note.** The paper's Proposition 3.1 (p.15, arXiv:2411.04551v3) carries NEITHER
the exclusivity gate NOR any atomlessness hypothesis: its Section 3.3 induction claims the full
generality in which members may share supports entirely. The gate is what makes the formal
placement chain close: it survives the shared base rotation, feeds the Phase-R resolution, and
keeps every colinear branch empty (the branch whose paper construction has the F17(b) gap). The
GENERAL case, distinct measures on possibly equal supports, stays on the untouched public axiom
(which gains NO hypothesis here), pending the equal-supports follow-up campaign through the B.16
asymmetric cap, `pAlign`, and the Prop 2.1 nesting, the route charted by findings F17(b), F22,
and F24/F25. `_hne` (the paper's standing pairwise-distinctness assumption) is retained for
statement fidelity per the faithful-scope convention; the gate subsumes it in this proof. -/
theorem exists_disentangling_balls_of_exclusive_supports (hd : 3 ≤ d) {N : ℕ}
    (μ₀ : Fin N → Measure (Eucl d)) (T : ℝ) (hT : 0 < T)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (_hne : Pairwise fun i j => μ₀ i ≠ μ₀ j)
    (hmiss : SharedMissingDirection μ₀)
    (hgate : ExclusiveSupportFamily μ₀) :
    ∃ (θ : AttnSchedule d) (α : Fin N → Eucl d) (r : ℝ),
      AttnSchedule.durationSum θ = T ∧
      0 < r ∧ r < 1 ∧
      (∀ i, ‖α i‖ = 1) ∧
      (∀ i j, i ≠ j → 2 * r ≤ dist (α i) (α j)) ∧
      (∀ i, supportedIn (attnMeasureFlow θ (μ₀ i)) (Metric.ball (α i) r)) ∧
      (∀ i, ∃ Φ Φinv : Eucl d → Eucl d, Measurable Φ ∧ Measurable Φinv ∧
        attnMeasureFlow θ (μ₀ i) = (μ₀ i).map Φ ∧
        ∀ x ∈ sphere d, Φinv (Φ x) = x) := by
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  obtain ⟨θ₁, α₁, r₁, -, hdur₁, hprefix, hnoncol⟩ :=
    disentangled_prefix_of_exclusive_supports hd μ₀ hμ hμs hmiss hgate (T / 2) hT2
  obtain ⟨θ₂, α, rU, hdur₂, hrU0, hrU1, hunit, hsep, hballs⟩ :=
    disentangled_prefix_uniformize hd μ₀ hμ hμs θ₁ α₁ r₁ hprefix hnoncol (T / 2) hT2
  refine ⟨θ₁ ++ θ₂, α, rU, ?_, hrU0, hrU1, hunit, hsep, hballs, ?_⟩
  · rw [AttnSchedule.durationSum_append, hdur₁, hdur₂]
    ring
  · intro i
    haveI := hμ i
    obtain ⟨Φ, Φinv, hΦm, -, hΦinvm, hmap, -, hinv⟩ :=
      attnMeasureFlow_exists_map (θ₁ ++ θ₂) (μ₀ i) (hμs i)
    exact ⟨Φ, Φinv, hΦm, hΦinvm, hmap, hinv⟩

end MeasureToMeasure.Leaves
