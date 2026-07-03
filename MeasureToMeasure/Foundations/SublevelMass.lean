import MeasureToMeasure.Foundations.Sphere
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Measure continuity along shrinking sublevel sets (Lemma B.2, eq. B.6)

In Appendix B.2 the mass retained by the gated transport is bounded below by the mass of a slightly
smaller cap, `μ(B(z, R-δ)) ≥ (1-ε)μ(B(z, R))` for `δ` small enough (eq. B.6). The geometric ball is
the sublevel set `{x | f x < R}` of the geodesic distance `f = d_g(z, ·)`; this file proves the
underlying measure fact for the sublevel set of *any* continuous function, so the cap version is a
direct instance.

The proof is continuity of measure from below: the open sublevel `{f < R}` is the increasing union of
the closed sublevels `{f ≤ R - 1/(n+1)}`, so `μ{f ≤ R - 1/(n+1)} → μ{f < R}`, and any fraction `< 1`
of the (finite) limit is eventually attained.
-/

namespace MeasureToMeasure

open MeasureTheory Filter
open scoped ENNReal Topology

variable {d : ℕ}

/-- **Measure continuity from below along a shrinking sublevel (eq. B.6).** For a continuous `f` and a
measure putting finite mass on the open sublevel `{f < R}`, any fraction `1 - ε < 1` of that mass is
already carried by a closed sublevel `{f ≤ r}` with `r < R`. Applied to `f = d_g(z, ·)` this is the
cap estimate `μ(B(z, r)) ≥ (1-ε)μ(B(z, R))`. -/
theorem exists_closed_sublevel_mass_ge {f : Eucl d → ℝ} (hf : Continuous f)
    {μ : Measure (Eucl d)} {R : ℝ} (hfin : μ {x | f x < R} ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r, r < R ∧ (1 - ENNReal.ofReal ε) * μ {x | f x < R} ≤ μ {x | f x ≤ r} := by
  set m : ℝ≥0∞ := μ {x | f x < R} with hm
  -- the increasing closed sublevels `A n = {f ≤ R - 1/(n+1)}` fill the open sublevel `{f < R}`
  set A : ℕ → Set (Eucl d) := fun n => {x | f x ≤ R - 1 / (n + 1)} with hA
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le hf.measurable measurable_const
  have hmono : Monotone A := by
    intro a b hab x hx
    have : (1 : ℝ) / (b + 1) ≤ 1 / (a + 1) := by
      apply one_div_le_one_div_of_le <;> [positivity; · exact_mod_cast Nat.add_le_add_right hab 1]
    simp only [hA, Set.mem_setOf_eq] at hx ⊢; linarith
  have hunion : ⋃ n, A n = {x | f x < R} := by
    ext x
    simp only [hA, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
  have htend : Tendsto (fun n => μ (A n)) atTop (𝓝 m) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rwa [hunion] at this
  -- the target fraction is strictly below the finite limit `m`, so it is eventually attained
  rcases eq_or_ne m 0 with hm0 | hm0
  · exact ⟨R - 1, by linarith, by simp [hm0]⟩
  · have hcoef : (1 : ℝ≥0∞) - ENNReal.ofReal ε < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.mpr hε).ne'
    have hlt : (1 - ENNReal.ofReal ε) * m < m := by
      rw [mul_comm]
      calc m * (1 - ENNReal.ofReal ε) < m * 1 := ENNReal.mul_lt_mul_right hm0 hfin hcoef
        _ = m := mul_one m
    obtain ⟨n, hn⟩ := (htend.eventually (eventually_gt_nhds hlt)).exists
    refine ⟨R - 1 / ((n : ℝ) + 1), ?_, hn.le⟩
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

end MeasureToMeasure
