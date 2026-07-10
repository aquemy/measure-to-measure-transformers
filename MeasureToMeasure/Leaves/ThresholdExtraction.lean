import MeasureToMeasure.Leaves.AtomlessDirection
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Exact threshold extraction via IVT on a continuous CDF (Proposition 2.2, Step B)

Given the generic atomless direction `u` from Step A (`Leaves/AtomlessDirection.lean`), this leaf
extracts a threshold `t` such that slicing `{x | ⟪u,x⟫ ≤ t}` carries EXACTLY a prescribed mass `m`.
This is the one-dimensional intermediate-value argument behind the paper's "sweep a threshold until
it captures the target mass" construction, made precise without ever invoking a packaged CDF or
quantile-function API -- Mathlib has none suited to this (`ProbabilityTheory.cdf` exists but only as
a `StieltjesFunction`, i.e. right-continuous by construction; the *left*-continuity this needs, which
is where atomlessness enters, is not itself packaged).

**The construction.** Let `F t := μ0 {x | ⟪u,x⟫ ≤ t}`. `F` is monotone, `F(-1)=0` and `F(1)=1` for
`μ0` supported on the sphere (Cauchy-Schwarz + atomlessness kills the antipodal boundary atom), and
-- this is the crux -- `F` is *continuous*: right-continuity is a general fact about any measure's
`Iic`-content (`Antitone.measure_iInter`, no atomlessness needed), while *left*-continuity is where
Step A's hypothesis enters (`F(t) = F(t⁻) + μ0{x|⟪u,x⟫=t}`, and the jump term vanishes exactly
because `u` was chosen atomless). Given continuity, `t := sInf {s ∈ [-1,1] | m ≤ F s}` achieves
`F t = m` exactly by a two-sided squeeze: `F t ≥ m` from right-continuity (every `s > t` has
`F s ≥ m` by definition of the infimum), `F t ≤ m` from left-continuity (every `s < t` has `F s ≤ m`,
and no atom sits exactly at `t`, so `F t` doesn't jump past `m` at the last moment).

`measure_proj_Iic_ge_of_forall_gt` and `measure_proj_Iic_le_of_forall_lt` package right- and
left-continuity respectively as reusable one-sided squeeze lemmas; `exists_threshold_eq` is the
assembled existence statement.

M3b/mid-level staging: Step B of the `prop_2_2` partition construction; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set Filter
open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- **The antipodal boundary carries no mass.** For `μ0` supported on the sphere, the "below -1"
level set of `⟪u,·⟩` is exactly the single antipodal point `{-u}` (Cauchy-Schwarz equality case),
which is atomless. -/
theorem measure_proj_le_neg_one (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0] [NoAtoms μ0]
    (u : Metric.sphere (0:Eucl d) 1) (hμ0S : μ0 (sphere d)ᶜ = 0) :
    μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ -1} = 0 := by
  have hun : ‖(u:Eucl d)‖ = 1 := by
    have := u.2; rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at this; exact this
  have hsub : {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ -1} ⊆ (sphere d)ᶜ ∪ {-(u:Eucl d)} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_cases hxs : x ∈ sphere d
    · right
      have hxnorm : ‖x‖ = 1 := by
        rw [MeasureToMeasure.sphere] at hxs
        exact norm_eq_one_of_mem_sphere hxs
      have hcs : |(⟪(u:Eucl d), x⟫ : ℝ)| ≤ 1 := by
        have := abs_real_inner_le_norm (u:Eucl d) x
        rwa [hun, hxnorm, mul_one] at this
      rw [abs_le] at hcs
      have heq : (⟪(u:Eucl d), x⟫ : ℝ) = -1 := le_antisymm hx hcs.1
      have heq' : (⟪x, (u:Eucl d)⟫ : ℝ) = -1 := by rw [real_inner_comm]; exact heq
      have hnormsq : ‖x + (u:Eucl d)‖^2 = 0 := by
        rw [norm_add_sq_real, hxnorm, hun, heq']; ring
      have hzero : x + (u:Eucl d) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)
      simp only [Set.mem_singleton_iff]
      exact eq_neg_of_add_eq_zero_left hzero
    · left; exact hxs
  have hle : μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ -1} ≤ 0 := by
    calc μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ -1}
        ≤ μ0 ((sphere d)ᶜ ∪ {-(u:Eucl d)}) := measure_mono hsub
      _ ≤ μ0 (sphere d)ᶜ + μ0 {-(u:Eucl d)} := measure_union_le _ _
      _ = 0 := by rw [hμ0S, measure_singleton]; simp
  exact nonpos_iff_eq_zero.mp hle

/-- **The "at most 1" level set is everything.** For `μ0` supported on the sphere, `⟪u,·⟩ ≤ 1`
always (Cauchy-Schwarz), so this level set has full measure. -/
theorem measure_proj_le_one (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    (u : Metric.sphere (0:Eucl d) 1) (hμ0S : μ0 (sphere d)ᶜ = 0) :
    μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ 1} = 1 := by
  have hun : ‖(u:Eucl d)‖ = 1 := by
    have := u.2; rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at this; exact this
  have hcompl : {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ 1}ᶜ ⊆ (sphere d)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
    intro hcon
    have hxnorm : ‖x‖ = 1 := by
      rw [MeasureToMeasure.sphere] at hcon
      exact norm_eq_one_of_mem_sphere hcon
    have hcs : |(⟪(u:Eucl d), x⟫ : ℝ)| ≤ 1 := by
      have := abs_real_inner_le_norm (u:Eucl d) x
      rwa [hun, hxnorm, mul_one] at this
    rw [abs_le] at hcs
    linarith [hcs.2]
  have hnull : μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ 1}ᶜ = 0 :=
    nonpos_iff_eq_zero.mp (hμ0S ▸ measure_mono hcompl)
  have hmeas : MeasurableSet {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have := measure_add_measure_compl (μ := μ0) hmeas
  rw [hnull, add_zero, measure_univ] at this
  exact this

/-- **Right-continuity of the threshold measure** (general fact, needs no atomlessness): if every
`s > t` already reaches mass `m`, so does `t` itself -- via `Antitone.measure_iInter` on the shrinking
family `Iic (t + 1/(n+1))`, whose intersection is exactly `Iic t`. -/
theorem measure_proj_Iic_ge_of_forall_gt (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    (u : Metric.sphere (0:Eucl d) 1) (m : ENNReal) (t : ℝ)
    (hgap : ∀ s, t < s → m ≤ μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ s}) :
    m ≤ μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ t} := by
  set f : Eucl d → ℝ := fun x => (⟪(u:Eucl d), x⟫ : ℝ) with hfdef
  have hfmeas : Measurable f := by rw [hfdef]; fun_prop
  have hIic : ⋂ n : ℕ, Set.Iic (t + 1/((n:ℝ)+1)) = Set.Iic t := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Iic]
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (x - t))
      have hpos : (0:ℝ) < x - t := by linarith
      have hxn := h n
      have : (1:ℝ)/((n:ℝ)+1) < x - t := by
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      linarith
    · intro h n
      have : (0:ℝ) ≤ 1/((n:ℝ)+1) := by positivity
      linarith
  have hset : ⋂ n : ℕ, f ⁻¹' Set.Iic (t + 1/((n:ℝ)+1)) = {x : Eucl d | f x ≤ t} := by
    rw [← Set.preimage_iInter, hIic]; rfl
  have hanti : Antitone (fun n : ℕ => f ⁻¹' Set.Iic (t + 1/((n:ℝ)+1))) := by
    intro a b hab
    apply Set.preimage_mono
    intro y hy
    simp only [Set.mem_Iic] at hy ⊢
    have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
    have : (1:ℝ)/((b:ℝ)+1) ≤ 1/((a:ℝ)+1) := by gcongr
    linarith
  have hmeasurable : ∀ n : ℕ, NullMeasurableSet (f ⁻¹' Set.Iic (t + 1/((n:ℝ)+1))) μ0 :=
    fun n => (hfmeas measurableSet_Iic).nullMeasurableSet
  have hfin : ∃ n : ℕ, μ0 (f ⁻¹' Set.Iic (t + 1/((n:ℝ)+1))) ≠ ⊤ :=
    ⟨0, (measure_lt_top μ0 _).ne⟩
  have hkey := Antitone.measure_iInter hanti hmeasurable hfin
  rw [hset] at hkey
  rw [hkey]
  refine le_iInf (fun n => hgap _ ?_)
  have hp : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
  linarith

/-- **Left-continuity of the threshold measure, given no atom at `t`**: if every `s < t` stays
below mass `m`, so does `t` itself -- via `Monotone.measure_iUnion` on the growing family
`Iic (t - 1/(n+1))`, whose union is `Iio t`, plus the hypothesis that `{x | ⟪u,x⟫ = t}` is null
(so `Iic t`'s measure doesn't jump past `Iio t`'s). This is exactly where Step A's genericity is
consumed. -/
theorem measure_proj_Iic_le_of_forall_lt (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    (u : Metric.sphere (0:Eucl d) 1) (m : ENNReal) (t : ℝ)
    (hatomless : μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) = t} = 0)
    (hbelow : ∀ s, s < t → μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ s} ≤ m) :
    μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ t} ≤ m := by
  set f : Eucl d → ℝ := fun x => (⟪(u:Eucl d), x⟫ : ℝ) with hfdef
  have hfmeas : Measurable f := by rw [hfdef]; fun_prop
  have hsplit : {x : Eucl d | f x ≤ t} = {x : Eucl d | f x < t} ∪ {x : Eucl d | f x = t} := by
    ext x; simp only [Set.mem_union, Set.mem_setOf_eq]; exact le_iff_lt_or_eq
  have hdisj : Disjoint {x : Eucl d | f x < t} {x : Eucl d | f x = t} := by
    rw [Set.disjoint_iff_forall_ne]
    intro a ha b hb heq
    simp only [Set.mem_setOf_eq] at ha hb
    rw [heq] at ha
    exact absurd hb ha.ne
  have hmeasEq : MeasurableSet {x : Eucl d | f x = t} := measurableSet_eq_fun hfmeas measurable_const
  have hunion_meas : μ0 {x : Eucl d | f x ≤ t}
      = μ0 {x : Eucl d | f x < t} + μ0 {x : Eucl d | f x = t} := by
    rw [hsplit, measure_union hdisj hmeasEq]
  rw [hunion_meas, hatomless, add_zero]
  have hIio : ⋃ n : ℕ, Set.Iic (t - 1/((n:ℝ)+1)) = Set.Iio t := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_Iio]
    constructor
    · rintro ⟨n, hn⟩
      have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      linarith
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t - x))
      have hpos : (0:ℝ) < t - x := by linarith
      refine ⟨n, ?_⟩
      have : (1:ℝ)/((n:ℝ)+1) < t - x := by
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      linarith
  have hset : ⋃ n : ℕ, f ⁻¹' Set.Iic (t - 1/((n:ℝ)+1)) = {x : Eucl d | f x < t} := by
    rw [← Set.preimage_iUnion, hIio]; rfl
  have hmono : Monotone (fun n : ℕ => f ⁻¹' Set.Iic (t - 1/((n:ℝ)+1))) := by
    intro a b hab
    apply Set.preimage_mono
    intro y hy
    simp only [Set.mem_Iic] at hy ⊢
    have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
    have : (1:ℝ)/((b:ℝ)+1) ≤ 1/((a:ℝ)+1) := by gcongr
    linarith
  have hkey := Monotone.measure_iUnion (μ := μ0) hmono
  rw [hset] at hkey
  rw [hkey]
  apply iSup_le
  intro n
  by_cases hpos : t - 1/((n:ℝ)+1) < t
  · exact hbelow _ hpos
  · exfalso
    apply hpos
    have hp : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    linarith

/-- **Exact threshold extraction.** For `μ0` supported on the sphere with atomless projection along
`u` (Step A's conclusion), every target mass `m ∈ [0,1]` is hit EXACTLY by some threshold cut
`{x | ⟪u,x⟫ ≤ t}` -- and that threshold itself carries no mass (`u`-atomlessness at `t` specifically),
so consecutive thresholds can be glued into disjoint slabs without losing or double-counting mass. -/
theorem exists_threshold_eq (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0] [NoAtoms μ0]
    (u : Metric.sphere (0:Eucl d) 1) (hμ0S : μ0 (sphere d)ᶜ = 0)
    (hatomless : ∀ c : ℝ, μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) = c} = 0)
    (m : ENNReal) (hm : m ≤ 1) :
    ∃ t : ℝ, μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) = t} = 0 ∧
      μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ t} = m := by
  set F : ℝ → ENNReal := fun t => μ0 {x : Eucl d | (⟪(u:Eucl d), x⟫ : ℝ) ≤ t} with hFdef
  have hFmono : Monotone F := by
    intro a b hab
    apply measure_mono
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    linarith
  have hF_neg1 : F (-1) = 0 := measure_proj_le_neg_one μ0 u hμ0S
  have hF_1 : F 1 = 1 := measure_proj_le_one μ0 u hμ0S
  set S : Set ℝ := {t ∈ Set.Icc (-1:ℝ) 1 | m ≤ F t} with hSdef
  have h1S : (1:ℝ) ∈ S := by rw [hSdef]; exact ⟨⟨by norm_num, le_refl 1⟩, hF_1 ▸ hm⟩
  have hSne : S.Nonempty := ⟨1, h1S⟩
  have hSbdd : BddBelow S := ⟨-1, fun t ht => (ht.1).1⟩
  set t : ℝ := sInf S with htdef
  have ht_le1 : t ≤ 1 := csInf_le hSbdd h1S
  have ht_lb : ∀ s ∈ S, t ≤ s := fun s hs => csInf_le hSbdd hs
  have hgap : ∀ s, t < s → m ≤ F s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    by_cases hsle : s ≤ 1
    · have hns : ¬ (∀ s' ∈ S, s ≤ s') := by
        intro hcon2
        exact absurd (le_csInf hSne hcon2) (not_le.mpr hs)
      push Not at hns
      obtain ⟨s', hs'S, hs'lt⟩ := hns
      exact absurd (hFmono hs'lt.le) (not_le.mpr (lt_of_lt_of_le hcon hs'S.2))
    · push Not at hsle
      have hmono1 := hFmono hsle.le
      rw [hF_1] at hmono1
      exact absurd (le_trans hm hmono1) (not_le.mpr hcon)
  have hbelow : ∀ s, s < t → F s ≤ m := by
    intro s hs
    by_cases hsge : -1 ≤ s
    · have hsnotS : s ∉ S := fun hsS => absurd (ht_lb s hsS) (not_le.mpr hs)
      rw [hSdef] at hsnotS
      simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and, not_le] at hsnotS
      have hsle1 : s ≤ 1 := le_trans hs.le ht_le1
      exact (hsnotS ⟨hsge, hsle1⟩).le
    · push Not at hsge
      calc F s ≤ F (-1) := hFmono hsge.le
        _ = 0 := hF_neg1
        _ ≤ m := bot_le
  refine ⟨t, hatomless t, le_antisymm ?_ ?_⟩
  · exact measure_proj_Iic_le_of_forall_lt μ0 u m t (hatomless t) hbelow
  · exact measure_proj_Iic_ge_of_forall_gt μ0 u m t hgap

end MeasureToMeasure.Leaves
