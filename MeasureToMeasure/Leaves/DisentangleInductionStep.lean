import MeasureToMeasure.Leaves.RotateFamilyToOrthant

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

end MeasureToMeasure.Leaves
