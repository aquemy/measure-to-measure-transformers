import MeasureToMeasure.Leaves.OrthantBoundaryGap
import MeasureToMeasure.Leaves.TaylorRemainderBound

/-!
# The local perturbative divergence formula (Lemma 3.4 Part 2 leaf 4)

The paper's Appendix B.3 (p.36) Phase 1 construction runs the SAME barycenter-alignment block
(`pAlign`) independently on `μ0` and `ν0`, and compares the two trajectories from a SHARED starting
point `x0` via a small-`τ` Taylor/Duhamel expansion. This leaf assembles that comparison into a
single theorem, combining leaves 2-3: **`exists_pos_divergence`** shows that for small enough
`τ`, the `ν0`-trajectory strictly outruns the `μ0`-trajectory along the shared barycenter direction
`u := barycenter μ0 / ‖barycenter μ0‖`.

The computation (with `v := barycenter μ0`, `w := barycenter ν0`, `v = γ • w`):
- Leaf 2 (`norm_taylor_remainder_le`) applied to BOTH flows at the SAME `x0` (leaf 2 is uniform over
  the whole sphere, not just `supp μ0`, which is exactly what makes this legal even though `x0` need
  not lie in `supp ν0`) gives `Φμ τ x0 = x0 + τ•P_x0^⊥(v) + O(τ²)` and
  `Φν τ x0 = x0 + τ•P_x0^⊥(w) + O(τ²)`.
- Subtracting: `Φν τ x0 - Φμ τ x0 = τ•P_x0^⊥(w-v) + O(τ²) = τ(1-γ)•P_x0^⊥(w) + O(τ²)` (`w - v =
  (1-γ)•w` from the colinearity hypothesis, `tangentialProjector` linear in its vector argument).
- Projecting onto `u`: `⟪P_x0^⊥(w), u⟫ = ‖w‖(1 - ⟪x0,u⟫²) = ‖w‖·g/‖v‖`, where `g` is leaf 3's
  quantitative gap (`g = ‖v‖(1-⟪x0,u⟫²)` -- the SAME quantity, related by the definitions of `u`).
- So `⟪Φν τ x0 - Φμ τ x0, u⟫ = τ(1-γ)‖w‖g/‖v‖ + O(τ²)`, with a STRICTLY POSITIVE linear coefficient
  (`1-γ>0` since `γ<1`, `‖w‖>0` and `g>0` from leaves 2-3), hence strictly positive for `τ` small
  enough that the linear term dominates the combined `O(τ²)` remainder (explicit threshold
  `τstar := min ((1-γ)‖w‖g/(6‖v‖)) T`, using leaf 2's explicit constant `3` per flow).

M3b/mid-level staging: consumed when `lemma_3_4_part2` is discharged; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure.Statements MeasureToMeasure.Foundations

variable {d : ℕ}

theorem tangentialProjector_smul_right (x : Eucl d) (c : ℝ) (v : Eucl d) :
    tangentialProjector x (c • v) = c • tangentialProjector x v := by
  simp only [tangentialProjector_apply, inner_smul_right, smul_sub, smul_smul]

theorem inner_tangentialProjector_self_dir {w x0 : Eucl d} (hw : 0 < ‖w‖) :
    ⟪tangentialProjector x0 w, (‖w‖⁻¹ : ℝ) • w⟫ = ‖w‖ - ‖w‖ * ⟪x0, (‖w‖⁻¹ : ℝ) • w⟫ ^ 2 := by
  rw [tangentialProjector_apply, inner_sub_left, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  have huw : ⟪x0, w⟫ = ‖w‖ * ⟪x0, (‖w‖⁻¹ : ℝ) • w⟫ := by
    rw [real_inner_smul_right]; field_simp
  rw [huw]; field_simp

/-- **The local perturbative divergence formula.** Two `pAlign`-flows on colinear-but-unequal
sphere-and-orthant-supported probability measures, started from the SAME point `x0` (leaf 3's
quantitative boundary point for `μ0`), diverge strictly along the shared barycenter direction after
a small enough time `τstar` -- the local comparison the paper's App. B.3 Phase 1 needs. -/
theorem exists_pos_divergence {μ0 ν0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure ν0]
    (hμs : μ0 (sphere d)ᶜ = 0) (hνs : ν0 (sphere d)ᶜ = 0)
    (hμint : Integrable (fun x : Eucl d => x) μ0) (hνint : Integrable (fun x : Eucl d => x) ν0)
    (hμorth : μ0 (orthant d)ᶜ = 0) (hνorth : ν0 (orthant d)ᶜ = 0)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hcol : barycenter μ0 = γ • barycenter ν0)
    (T : ℝ) (hT : (0 : ℝ) < T)
    (Φμ Φν : ℝ → Eucl d → Eucl d)
    (hΦμ : IsMeanFieldFlow (pAlign T hT.le) μ0 Φμ) (hΦν : IsMeanFieldFlow (pAlign T hT.le) ν0 Φν) :
    ∃ x0 ∈ μ0.support, x0 ∈ sphere d ∧ ∃ τstar : ℝ, 0 < τstar ∧ τstar ≤ T ∧
      ∀ τ ∈ Set.Ioo (0 : ℝ) τstar,
        0 < ⟪Φν τ x0 - Φμ τ x0, (‖barycenter μ0‖⁻¹ : ℝ) • barycenter μ0⟫ := by
  set v := barycenter μ0 with hv
  set w := barycenter ν0 with hw
  have hvlt : ‖v‖ < 1 := norm_barycenter_colinear_lt_one hνs hνint hγ hcol
  have hwpos : 0 < ‖w‖ := norm_barycenter_pos_of_orthant hνs hνint hνorth
  obtain ⟨x0, hx0supp, hx0sphere, hgap⟩ := exists_orthant_support_gap hμs hμint hμorth hvlt
  set g := ‖v‖ - ⟪v, x0⟫ ^ 2 / ‖v‖ with hgdef
  have hvpos : 0 < ‖v‖ := norm_barycenter_pos_of_orthant hμs hμint hμorth
  set u := (‖v‖⁻¹ : ℝ) • v with hu
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]; field_simp
  have huw : u = (‖w‖⁻¹ : ℝ) • w := by
    rw [hu, hcol, norm_smul, Real.norm_eq_abs, abs_of_pos hγ.1, smul_smul]
    congr 1
    field_simp [hγ.1.ne']
  have hveq : v = (‖v‖ : ℝ) • u := by
    rw [hu, smul_smul]
    field_simp
    exact (one_smul ℝ v).symm
  have hvx0 : ⟪v, x0⟫ = ‖v‖ * ⟪x0, u⟫ := by
    conv_lhs => rw [hveq]
    rw [real_inner_smul_left, real_inner_comm]
  have hgu : g = ‖v‖ * (1 - ⟪x0, u⟫ ^ 2) := by
    rw [hgdef, hvx0]; field_simp
  set K : ℝ := (1 - γ) * ‖w‖ * g / (6 * ‖v‖) with hKdef
  have hKpos : 0 < K := by
    show 0 < (1 - γ) * ‖w‖ * g / (6 * ‖v‖)
    apply div_pos _ (by positivity)
    apply mul_pos (mul_pos (by linarith [hγ.2]) hwpos) hgap
  refine ⟨x0, hx0supp, hx0sphere, min K T, lt_min hKpos hT, min_le_right K T, ?_⟩
  intro τ ⟨hτpos, hτlt⟩
  have hτltK : τ < K := lt_of_lt_of_le hτlt (min_le_left K T)
  have hτT : τ ≤ T := le_of_lt (lt_of_lt_of_le hτlt (min_le_right K T))
  have hτIcc : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτpos.le, hτT⟩
  have hrem_μ : ‖Φμ τ x0 - x0 - τ • tangentialProjector x0 v‖ ≤ 3 * τ ^ 2 :=
    norm_taylor_remainder_le T hT.le μ0 hμs hμint Φμ hΦμ x0 hx0sphere hτIcc
  have hrem_ν : ‖Φν τ x0 - x0 - τ • tangentialProjector x0 w‖ ≤ 3 * τ ^ 2 :=
    norm_taylor_remainder_le T hT.le ν0 hνs hνint Φν hΦν x0 hx0sphere hτIcc
  have hcomb : ‖(Φν τ x0 - Φμ τ x0) - τ • (tangentialProjector x0 w - tangentialProjector x0 v)‖
      ≤ 6 * τ ^ 2 := by
    have heq : (Φν τ x0 - Φμ τ x0) - τ • (tangentialProjector x0 w - tangentialProjector x0 v)
        = (Φν τ x0 - x0 - τ • tangentialProjector x0 w)
          - (Φμ τ x0 - x0 - τ • tangentialProjector x0 v) := by
      simp only [smul_sub]; abel
    rw [heq]
    calc ‖(Φν τ x0 - x0 - τ • tangentialProjector x0 w)
            - (Φμ τ x0 - x0 - τ • tangentialProjector x0 v)‖
        ≤ ‖Φν τ x0 - x0 - τ • tangentialProjector x0 w‖
          + ‖Φμ τ x0 - x0 - τ • tangentialProjector x0 v‖ := norm_sub_le _ _
      _ ≤ 3 * τ ^ 2 + 3 * τ ^ 2 := add_le_add hrem_ν hrem_μ
      _ = 6 * τ ^ 2 := by ring
  have hwv : tangentialProjector x0 w - tangentialProjector x0 v
      = (1 - γ) • tangentialProjector x0 w := by
    rw [tangentialProjector_sub_right, hcol]
    have heq2 : w - γ • w = (1 - γ) • w := by rw [sub_smul, one_smul]
    rw [heq2, tangentialProjector_smul_right]
  rw [hwv] at hcomb
  have hinner : |⟪(Φν τ x0 - Φμ τ x0) - τ • ((1 - γ) • tangentialProjector x0 w), u⟫| ≤ 6 * τ ^ 2 := by
    calc |⟪(Φν τ x0 - Φμ τ x0) - τ • ((1 - γ) • tangentialProjector x0 w), u⟫|
        ≤ ‖(Φν τ x0 - Φμ τ x0) - τ • ((1 - γ) • tangentialProjector x0 w)‖ * ‖u‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ 6 * τ ^ 2 * 1 := by rw [hunorm]; linarith [hcomb]
      _ = 6 * τ ^ 2 := by ring
  have hexpand : ⟪(Φν τ x0 - Φμ τ x0) - τ • ((1 - γ) • tangentialProjector x0 w), u⟫
      = ⟪Φν τ x0 - Φμ τ x0, u⟫ - τ * (1 - γ) * ⟪tangentialProjector x0 w, u⟫ := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    ring
  rw [hexpand] at hinner
  have hproj : ⟪tangentialProjector x0 w, u⟫ = ‖w‖ * g / ‖v‖ := by
    rw [huw, inner_tangentialProjector_self_dir hwpos, ← huw, hgu]
    field_simp
  rw [hproj] at hinner
  rw [abs_le] at hinner
  have hlb : ⟪Φν τ x0 - Φμ τ x0, u⟫ ≥ τ * (1 - γ) * (‖w‖ * g / ‖v‖) - 6 * τ ^ 2 := by
    linarith [hinner.1]
  have hKeq : 6 * ‖v‖ * K = (1 - γ) * ‖w‖ * g := by
    show 6 * ‖v‖ * ((1 - γ) * ‖w‖ * g / (6 * ‖v‖)) = (1 - γ) * ‖w‖ * g
    field_simp
  have hτltK' : 6 * ‖v‖ * τ < (1 - γ) * ‖w‖ * g := by
    have h6v : 0 < 6 * ‖v‖ := by positivity
    have step : 6 * ‖v‖ * τ < 6 * ‖v‖ * K := mul_lt_mul_of_pos_left hτltK h6v
    linarith [step, hKeq]
  have hrecast : τ * (1 - γ) * (‖w‖ * g / ‖v‖) - 6 * τ ^ 2
      = τ / ‖v‖ * ((1 - γ) * ‖w‖ * g - 6 * ‖v‖ * τ) := by
    field_simp
  rw [hrecast] at hlb
  have hpos2 : 0 < τ / ‖v‖ * ((1 - γ) * ‖w‖ * g - 6 * ‖v‖ * τ) :=
    mul_pos (div_pos hτpos hvpos) (by linarith [hτltK'])
  linarith [hlb, hpos2]

end MeasureToMeasure.Leaves
