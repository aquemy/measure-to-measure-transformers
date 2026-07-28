import MeasureToMeasure.Leaves.DisentangleResolveFamily

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

M3b/mid-level staging: the `G-unwrap` step (uniformizing the per-member radii and discharging
`exists_disentangling_balls` itself) consumes this; see the `exists-disentangling-balls-campaign`
notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule AttnParams attnMeasureFlow)
open MeasureToMeasure.Foundations (isProbabilityMeasure_attnMeasureFlow
  attnMeasureFlow_supportedIn_sphere attnMeasureFlow_append)
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
base-rotation / Phase-R / placement chain and the placement invariant. -/
theorem disentangled_prefix_of_exclusive_supports (hd : 3 ≤ d) {N : ℕ}
    (μ₀ : Fin N → Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hmiss : SharedMissingDirection μ₀) (hgate : ExclusiveSupportFamily μ₀)
    (T : ℝ) (hT : 0 < T) :
    ∃ (θ : AttnSchedule d) (α : Fin N → Eucl d) (r : Fin N → ℝ),
      (∀ i, 0 < r i) ∧ AttnSchedule.durationSum θ = T ∧
      DisentangledPrefix d N N μ₀ θ α r := by
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
  obtain ⟨θfin, α, r, hdurfin, hprefin, hrposfin, -, -⟩ := key N (le_refl N)
  refine ⟨θfin, α, r, hrposfin, ?_, hprefin⟩
  rw [hdurfin, hτdef]
  field_simp
  ring

end MeasureToMeasure.Leaves
