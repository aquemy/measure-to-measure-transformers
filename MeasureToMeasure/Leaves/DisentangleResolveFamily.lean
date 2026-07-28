import MeasureToMeasure.Leaves.DisentangleInductionStepAsym

/-!
# Phase R: resolving a whole family to pairwise non-colinearity, one member at a time

The family resolution phase of `exists_disentangling_balls`'s induction over `N`. The placement
induction (`DisentangleInductionAssembly.lean`) can only run its non-colinear branch
(`disentangle_insert_noncolinear_avoiding`) when the WHOLE post-rotation family is pairwise
non-colinear: `lemma_3_3`'s `hnoncol` is a blanket `Pairwise` over the whole family, so a single
still-colinear pair of unplaced members blocks EVERY placement step, not just their own. The
per-pair colinear branch (`disentangle_insert_colinear_resolving_asym`) cannot serve inside the
induction either: its carrier hypotheses (`hbys`, `hsepU`) quantify over every probability measure
supported in an open carrier `U` containing BOTH pair members' supports, and before any placement
those supports are spread over the whole orthant sphere, making the `∀ ρ` clauses unsatisfiable
for the small `U` they need. This file therefore resolves ALL colinearities UP FRONT: each member
is collapsed exactly once, against the barycenter lines of ALL other members simultaneously
(`exists_multiline_collapse_schedule`), while every other member is literally fixed.

## The gate, and its bookkeeping

`ExclusiveSupportFamily` (`RotateFamilyToOrthant.lean`) is the gate: every member owns a support
point no other member's support contains, a property the base rotation transports for free
(`exclusiveSupportFamily_rotate_family_to_orthant`). Per resolution step `m`, the static cap
machinery needs a closed bad set `K` carrying
every OTHER member's support while missing one point of member `m`'s support
(`exists_static_cap_in_open_avoiding_closed`). Two facts make the gate survive all `N` steps:

* members are resolved in index order and each step literally fixes everyone else (zero cap mass
  through `measure_cap_null_of_trace_disjoint_support`), so member `m`'s own support is UNMOVED
  until its own step, where its original witness point is still available; and
* each step's cap-trace additionally avoids every other member's witness HALF-BALL (folded into
  `K`; the ball slack comes from `exclusiveSupportFamily_ball_slack`, since the finite union of
  the other supports is closed), and the moved member's image is confined away from those
  half-balls by the collapse block's region-invariance clause, so no earlier-moved member's new
  support can swallow a later member's witness point.

The moved member stays orthant-supported because the cap's sphere-trace lies in the open carrier
`W := orthant d`, so the region-invariance clause applies at `S := orthant d`.

M3b/mid-level staging: consumed by the placement induction of
`exists_disentangling_balls`'s re-base; see the `exists-disentangling-balls-campaign` notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule AttnParams attnMeasureFlow)
open MeasureToMeasure.Foundations (isProbabilityMeasure_attnMeasureFlow
  attnMeasureFlow_supportedIn_sphere attnMeasureFlow_append)
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Ball slack for an exclusive-support family** (`ExclusiveSupportFamily` is the initial-data
gate of `RotateFamilyToOrthant.lean`, transported through the base rotation by
`exclusiveSupportFamily_rotate_family_to_orthant`). The union of the OTHER members' supports is a
finite union of closed sets, hence closed, so each member's exclusive witness point keeps a whole
metric ball clear of every other member's support. This is the quantitative form Phase R's
per-step bad set `K` consumes (witness half-balls have to be avoidable by the cap trace, which
needs positive clearance, not just a point exclusion). -/
theorem exclusiveSupportFamily_ball_slack {N : ℕ} {μ : Fin N → Measure (Eucl d)}
    (h : ExclusiveSupportFamily μ) :
    ∃ (x : Fin N → Eucl d) (δ : Fin N → ℝ), (∀ i, 0 < δ i) ∧
      (∀ i, x i ∈ (μ i).support) ∧
      ∀ i j : Fin N, j ≠ i → Disjoint (Metric.ball (x i) (δ i)) (μ j).support := by
  choose x hxsupp hxout using h
  have hδ : ∀ i, ∃ δ : ℝ, 0 < δ ∧
      Metric.ball (x i) δ ⊆ (⋃ j ∈ ({i}ᶜ : Set (Fin N)), (μ j).support)ᶜ := by
    intro i
    have hclosed : IsClosed (⋃ j ∈ ({i}ᶜ : Set (Fin N)), (μ j).support) :=
      Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ => Measure.isClosed_support
    have hxnotin : x i ∉ ⋃ j ∈ ({i}ᶜ : Set (Fin N)), (μ j).support := by
      intro hmem
      obtain ⟨j, hj, hjs⟩ := Set.mem_iUnion₂.mp hmem
      exact hxout i j (by simpa using hj) hjs
    obtain ⟨δ, hδpos, hδsub⟩ :=
      Metric.isOpen_iff.mp hclosed.isOpen_compl (x i) hxnotin
    exact ⟨δ, hδpos, hδsub⟩
  choose δ hδpos hδsub using hδ
  refine ⟨x, δ, hδpos, hxsupp, ?_⟩
  intro i j hji
  rw [Set.disjoint_left]
  intro a ha haj
  exact hδsub i ha (Set.mem_biUnion (by simpa using hji) haj)

set_option maxHeartbeats 1000000 in
/-- **Phase R: the whole family made pairwise non-colinear, in `N` collapse blocks of total
duration exactly `N * τ`.** Given a sphere-and-orthant-supported probability family with exclusive
supports, one schedule `ψ` (one multi-line collapse block per member, in index order, each of
duration `τ`) keeps every member sphere-and-orthant supported and makes the flowed barycenters
pairwise non-colinear for EVERY scalar. Consumed by the placement induction as the post-rotation
preprocessing that lets every subsequent insertion step run the non-colinear branch.

The inner induction (`key`) tracks four invariants over the number `m` of already-resolved
members: orthant support of everyone; literal fixed-ness of every unresolved member (so its
support, witness point, and barycenter are still the originals when its turn comes); pairwise
non-colinearity of every pair touching a resolved member (each step's multi-line conclusion gives
one direction against every other CURRENT barycenter, `ne_smul_flip_of_ne_zero` the other, since
orthant barycenters are nonzero by `norm_barycenter_pos_of_orthant`); and witness-half-ball
avoidance by every resolved member's support (the region-invariance clause of the collapse block
at the complement of the other witness half-balls, whose union the cap-trace avoids through `K`).
After `m = N`, every pair touches a resolved member, giving the blanket `Pairwise`. -/
theorem exists_resolve_family_noncolinear (hd2 : 2 ≤ d) {N : ℕ}
    (ν : Fin N → Measure (Eucl d)) (hν : ∀ i, IsProbabilityMeasure (ν i))
    (hνs : ∀ i, supportedIn (ν i) (sphere d)) (hνo : ∀ i, supportedIn (ν i) (orthant d))
    (hgate : ExclusiveSupportFamily ν)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ ψ : AttnSchedule d, AttnSchedule.durationSum ψ = N * τ ∧
      (∀ i, supportedIn (attnMeasureFlow ψ (ν i)) (sphere d)) ∧
      (∀ i, supportedIn (attnMeasureFlow ψ (ν i)) (orthant d)) ∧
      Pairwise fun i j : Fin N => ∀ c : ℝ,
        barycenter (attnMeasureFlow ψ (ν i)) ≠ c • barycenter (attnMeasureFlow ψ (ν j)) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨x, δ, hδpos, hxsupp, hdisj⟩ := exclusiveSupportFamily_ball_slack hgate
  have hprob : ∀ (ψ : AttnSchedule d) (i : Fin N),
      IsProbabilityMeasure (attnMeasureFlow ψ (ν i)) := fun ψ i =>
    haveI := hν i; isProbabilityMeasure_attnMeasureFlow ψ (ν i) (hνs i)
  have hsph : ∀ (ψ : AttnSchedule d) (i : Fin N),
      supportedIn (attnMeasureFlow ψ (ν i)) (sphere d) := fun ψ i =>
    haveI := hν i; attnMeasureFlow_supportedIn_sphere ψ (ν i) (hνs i)
  have key : ∀ m : ℕ, m ≤ N → ∃ ψ : AttnSchedule d,
      AttnSchedule.durationSum ψ = m * τ ∧
      (∀ i, supportedIn (attnMeasureFlow ψ (ν i)) (orthant d)) ∧
      (∀ i : Fin N, m ≤ (i : ℕ) → attnMeasureFlow ψ (ν i) = ν i) ∧
      (∀ i j : Fin N, i ≠ j → ((i : ℕ) < m ∨ (j : ℕ) < m) → ∀ c : ℝ,
        barycenter (attnMeasureFlow ψ (ν i)) ≠ c • barycenter (attnMeasureFlow ψ (ν j))) ∧
      (∀ i : Fin N, (i : ℕ) < m → ∀ l : Fin N, l ≠ i →
        attnMeasureFlow ψ (ν i) (Metric.ball (x l) (δ l / 2)) = 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨[], by simp, ?_, ?_, ?_, ?_⟩
      · intro i; simpa using hνo i
      · intro i _; simp
      · intro i j _ hlt c
        rcases hlt with h | h <;> exact absurd h (Nat.not_lt_zero _)
      · intro i hi
        exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm1
      obtain ⟨ψ, hdur, horth, hfix, hnc, hwit⟩ := ih (by omega)
      have hmN : m < N := by omega
      set mm : Fin N := ⟨m, hmN⟩ with hmmdef
      set F : Fin N → Measure (Eucl d) := fun i => attnMeasureFlow ψ (ν i) with hFdef
      haveI : IsProbabilityMeasure (F mm) := hprob ψ mm
      have hFmm : F mm = ν mm := hfix mm (le_refl m)
      -- nonzero barycenters of every current member (orthant plus sphere support)
      have hbnz : ∀ l : Fin N, barycenter (F l) ≠ 0 := by
        intro l
        haveI := hprob ψ l
        exact norm_pos_iff.mp (norm_barycenter_pos_of_orthant (hsph ψ l)
          (integrable_id_of_sphere_support (hsph ψ l)) (horth l))
      -- the closed bad set: every other member's current support plus witness half-ball
      set K : Set (Eucl d) :=
        (⋃ l ∈ ({mm}ᶜ : Set (Fin N)), (F l).support) ∪
        (⋃ l ∈ ({mm}ᶜ : Set (Fin N)), Metric.closedBall (x l) (δ l / 2)) with hKdef
      have hKclosed : IsClosed K := by
        refine IsClosed.union ?_ ?_
        · exact Set.Finite.isClosed_biUnion (Set.toFinite _)
            fun l _ => Measure.isClosed_support
        · exact Set.Finite.isClosed_biUnion (Set.toFinite _)
            fun l _ => Metric.isClosed_closedBall
      -- the acted member's witness point is outside `K`
      have hxout : x mm ∉ K := by
        rw [hKdef]
        rintro (hin | hin)
        · obtain ⟨l, hl, hlsupp⟩ := Set.mem_iUnion₂.mp hin
          have hlne : l ≠ mm := by simpa using hl
          by_cases hlm : m ≤ (l : ℕ)
          · have hFl : F l = ν l := hfix l hlm
            rw [hFl] at hlsupp
            exact Set.disjoint_left.mp (hdisj mm l hlne)
              (Metric.mem_ball_self (hδpos mm)) hlsupp
          · have hlm' : (l : ℕ) < m := by omega
            exact (Measure.notMem_support_iff_exists.mpr
              ⟨Metric.ball (x mm) (δ mm / 2),
                Metric.ball_mem_nhds _ (by linarith [hδpos mm]),
                hwit l hlm' mm (Ne.symm hlne)⟩) hlsupp
        · obtain ⟨l, hl, hlball⟩ := Set.mem_iUnion₂.mp hin
          have hlne : l ≠ mm := by simpa using hl
          have hxin : x mm ∈ Metric.ball (x l) (δ l) :=
            Metric.closedBall_subset_ball (by linarith [hδpos l]) hlball
          exact Set.disjoint_left.mp (hdisj l mm hlne.symm) hxin (hxsupp mm)
      -- the static cap for the acted member, inside the orthant, clear of `K`
      obtain ⟨z, cosR, hznorm, hcosR, hcappos, htrace⟩ :=
        exists_static_cap_in_open_avoiding_closed (F mm) (hsph ψ mm)
          (orthant d) isOpen_orthant (horth mm) K hKclosed
          ⟨x mm, by rw [hFmm]; exact hxsupp mm, hxout⟩
      have hzs : z ∈ sphere d := by
        rw [sphere, Metric.mem_sphere, dist_zero_right, hznorm]
      -- the multi-line collapse block against every other member's barycenter line
      obtain ⟨p, hpdur, hlines, hpfix, hpS⟩ :=
        exists_multiline_collapse_schedule hd2 (F mm) (hsph ψ mm) hzs hcosR hcappos
          (ι := {l : Fin N // l ≠ mm}) (fun l => barycenter (F l.1))
          (fun l => hbnz l.1) hτ
      -- every other member has zero cap mass (its support is inside `K`), hence is fixed
      have hcapnull : ∀ l : Fin N, l ≠ mm →
          (F l) {x' | cosR < (⟪z, x'⟫ : ℝ)} = 0 := by
        intro l hl
        refine measure_cap_null_of_trace_disjoint_support (F l) (hsph ψ l) ?_
        intro x' hx' hcap' hsupp
        exact (htrace x' hx' hcap').2
          (Or.inl (Set.mem_biUnion (by simpa using hl) hsupp))
      have hFix' : ∀ l : Fin N, l ≠ mm →
          attnMeasureFlow (ψ ++ [p]) (ν l) = F l := by
        intro l hl
        haveI := hprob ψ l
        rw [attnMeasureFlow_append]
        exact hpfix (F l) (hsph ψ l) (hcapnull l hl)
      -- the moved member stays in the orthant (the trace lands there)
      have hmorth : supportedIn (attnMeasureFlow [p] (F mm)) (orthant d) :=
        hpS (orthant d) isOpen_orthant.measurableSet
          (fun x' hx' hc => (htrace x' hx' hc).1) (F mm) (hsph ψ mm) (horth mm)
      -- the moved member avoids every other member's witness half-ball
      set B : Set (Eucl d) :=
        ⋃ l ∈ ({mm}ᶜ : Set (Fin N)), Metric.ball (x l) (δ l / 2) with hBdef
      have hBmeas : MeasurableSet Bᶜ :=
        (isOpen_biUnion fun l _ => Metric.isOpen_ball).measurableSet.compl
      have htraceB : ∀ x' ∈ sphere d, cosR < (⟪z, x'⟫ : ℝ) → x' ∈ Bᶜ := by
        intro x' hx' hc hxB
        obtain ⟨l, hl, hlball⟩ := Set.mem_iUnion₂.mp hxB
        exact (htrace x' hx' hc).2
          (Or.inr (Set.mem_biUnion hl (Metric.ball_subset_closedBall hlball)))
      have hνmmB : supportedIn (F mm) Bᶜ := by
        rw [hFmm, supportedIn, compl_compl, hBdef]
        refine (measure_biUnion_null_iff (Set.to_countable _)).mpr ?_
        intro l hl
        have hlne : l ≠ mm := by simpa using hl
        refine measure_mono_null ?_ Measure.measure_compl_support
        intro a ha
        have hain : a ∈ Metric.ball (x l) (δ l) :=
          Metric.ball_subset_ball (by linarith [hδpos l]) ha
        exact fun hasupp => Set.disjoint_left.mp (hdisj l mm hlne.symm) hain hasupp
      have hmovedB : supportedIn (attnMeasureFlow [p] (F mm)) Bᶜ :=
        hpS Bᶜ hBmeas htraceB (F mm) (hsph ψ mm) hνmmB
      -- assemble the extended schedule
      refine ⟨ψ ++ [p], ?_, ?_, ?_, ?_, ?_⟩
      · rw [AttnSchedule.durationSum_append, hdur]
        have hone : AttnSchedule.durationSum [p] = p.duration := by
          simp [AttnSchedule.durationSum]
        rw [hone, hpdur]
        push_cast
        ring
      · intro i
        by_cases hi : i = mm
        · subst hi
          rw [attnMeasureFlow_append]
          exact hmorth
        · rw [hFix' i hi]
          exact horth i
      · intro i hi
        have hine : i ≠ mm := by
          intro h
          rw [h] at hi
          simp only [hmmdef] at hi
          omega
        rw [hFix' i hine]
        exact hfix i (by omega)
      · intro i j hij hlt c
        by_cases hi : i = mm
        · subst hi
          have hj : j ≠ mm := Ne.symm hij
          rw [hFix' j hj, attnMeasureFlow_append]
          exact hlines ⟨j, hj⟩ c
        · by_cases hj : j = mm
          · subst hj
            rw [hFix' i hi, attnMeasureFlow_append]
            exact ne_smul_flip_of_ne_zero (hbnz i) (fun c' => hlines ⟨i, hi⟩ c') c
          · rw [hFix' i hi, hFix' j hj]
            refine hnc i j hij ?_ c
            rcases hlt with h | h
            · left
              have : (i : ℕ) ≠ m := fun he => hi (Fin.ext he)
              omega
            · right
              have : (j : ℕ) ≠ m := fun he => hj (Fin.ext he)
              omega
      · intro i hi l hl
        by_cases him : i = mm
        · subst him
          rw [attnMeasureFlow_append]
          have h0 : attnMeasureFlow [p] (F mm) B = 0 := by
            have h := hmovedB
            rwa [supportedIn, compl_compl] at h
          have hlmem : l ∈ ({mm}ᶜ : Set (Fin N)) := by simpa using hl
          have hsub : Metric.ball (x l) (δ l / 2) ⊆ B :=
            fun a ha => Set.mem_biUnion hlmem ha
          exact measure_mono_null hsub h0
        · have him' : (i : ℕ) < m := by
            have : (i : ℕ) ≠ m := fun he => him (Fin.ext he)
            omega
          rw [hFix' i him]
          exact hwit i him' l hl
  obtain ⟨ψ, hdur, horth, -, hnc, -⟩ := key N (le_refl N)
  exact ⟨ψ, hdur, fun i => hsph ψ i, horth, fun i j hij => hnc i j hij (Or.inl i.isLt)⟩

end MeasureToMeasure.Leaves
