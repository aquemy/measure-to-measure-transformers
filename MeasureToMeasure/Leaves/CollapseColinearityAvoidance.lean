import MeasureToMeasure.Foundations.Sphere
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Avoiding colinearity of the mass-gap-cap-collapse targets (`lemma_3_4_part2` Gap 2, cases A & B)

`lemma_3_4_part2`'s discharge via the mass-gap-cap-collapse route (`Leaves/Lemma34Part1MeanField.lean`)
reduces to ONE remaining gap ("Gap 2", `mean-field-axioms-retractability` project notes): the
construction proves the flowed barycenters are UNEQUAL, but the axiom needs them NON-COLINEAR for
every `γ₂`. The collapse-target vectors are `Sμ•ω(θ)+p` and `Sν•ω(θ)+q` (`Sμ,Sν` cap masses, `p,q`
leftover-mass integrals, `ω(θ) := cosθ•z+sinθ•w` the cap-pole curve parametrized by the auxiliary
direction `w`), and the question is which `θ` make these colinear.

**Case A** (easiest): writing `p,q`'s components orthogonal to `span{z,w}` as `restComp z w p`,
`restComp z w q` (θ-INDEPENDENT, since `ω(θ)` lies entirely in `span{z,w}` --
`restComp_add_smul_omega`), if these rest-components are NOT scalar multiples of each other, the
collapse targets can NEVER be colinear, for ANY `θ` or `γ₂` (`ne_smul_collapse_of_restComp_not_smul`)
-- the rest-component mismatch alone rules it out, since a colinear pair would need proportional
rest-components too.

**Combined with `Leaves/PoleGeometry.lean`'s `exists_unit_orthogonal_two`** (`d≥3`, choose `w⊥{z,q}`
so `q`'s rest-component is exactly `q`'s component orthogonal to `z` alone, independent of `w`), this
handles the case `q ∦ z` (or symmetrically `p ∦ z`) entirely, WHENEVER `p`'s own rest-component (now
pinned to `p - ⟨p,z⟩z - ⟨p,w⟩w` for the specific chosen `w`) also fails to be parallel to `q`'s.

**Case B**: when the rest-components ARE parallel (`restComp z w p = r₀ • restComp z w q` for a forced
ratio `r₀`, with `restComp z w q ≠ 0`), any colinearity witness `γ` at any angle `θ` is FORCED to equal
`r₀` (`gamma_eq_r0_of_colinear` -- same rest-component argument as Case A, but pinning `γ` instead of
refuting it). Substituting `γ = r₀` back into the colinearity equation and taking `z`- and
`w`-components (`ω(θ)` lies in `span{z,w}`, so this captures the whole equation together with the
already-matched rest-components) yields a LINEAR system `(Sμ-r₀Sν)cosθ = r₀q_z-p_z`,
`(Sμ-r₀Sν)sinθ = r₀q_w-p_w` (`cos_eq_of_colinear`, `sin_eq_of_colinear`). Whenever `Sμ ≠ r₀Sν`, this
system pins `cosθ,sinθ` uniquely, so **at most one angle (mod 2π) can be colinear**
(`angle_unique_of_colinear`, via `Real.Angle.cos_sin_inj`) -- combined with the existing 2-candidate
cap-pole pigeonhole (`exists_pole_in_cap_ne`), the OTHER candidate angle is then guaranteed safe.

**NOT yet done** (see `mean-field-axioms-retractability` for the full derivation): the residual case
(`Sμ = r₀Sν` as well, a narrow 4-way conjunctive degeneracy) is not excluded here, nor is `restComp z w
q = 0`. The final assembly connecting these standalone lemmas to `Lemma34Part1MeanField.lean`'s actual
`μ, ν, z, w, p, q, Sμ, Sν` instantiation, and wiring the 2-candidate pigeonhole through
`angle_unique_of_colinear`, is NOT attempted here.

**`gramGap`**: the actual flowed barycenters in `Lemma34Part1MeanField.lean` are only `W₂`-CLOSE to the
IDEAL collapse targets `Sμ•ω+p`/`Sν•ω+q` (not equal to them), so composing cases A/B with that
`W₂`-closeness needs a QUANTITATIVE, perturbation-stable non-colinearity margin, not just a bare `≠`.
`ne_smul_of_gramGap_pos` provides the right bridge: the strict Cauchy-Schwarz/Lagrange gap
`⟪A,B⟫² < ‖A‖²‖B‖²` implies `A ≠ γ₂•B` for every `γ₂`, UNCONDITIONALLY (no nonzero-`B` hypothesis
needed, unlike a raw distance-to-line argument) -- and, being a polynomial inequality in `A,B`, is the
natural target for a future Lipschitz/continuity perturbation-stability lemma (NOT yet built) that
would convert cases A/B's ideal-target non-colinearity into a `W₂`-robust one.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The component of `v` orthogonal to both `z` and `w`. -/
noncomputable def restComp (z w v : Eucl d) : Eucl d := v - (⟪z, v⟫ : ℝ) • z - (⟪w, v⟫ : ℝ) • w

/-- `restComp` is linear in its third argument. -/
theorem restComp_smul {z w v : Eucl d} (c : ℝ) : restComp z w (c • v) = c • restComp z w v := by
  unfold restComp
  simp only [real_inner_smul_right, smul_sub, smul_smul]

/-- If `A`'s rest-component (relative to `z,w`) is NOT a scalar multiple of `B`'s, `A` is never a
scalar multiple of `B` -- the rest-components alone rule out colinearity. -/
theorem ne_smul_of_restComp_not_smul {z w A B : Eucl d}
    (hne : ∀ c : ℝ, restComp z w A ≠ c • restComp z w B) (γ₂ : ℝ) : A ≠ γ₂ • B := by
  intro h
  apply hne γ₂
  show A - (⟪z, A⟫ : ℝ) • z - (⟪w, A⟫ : ℝ) • w = γ₂ • (B - (⟪z, B⟫ : ℝ) • z - (⟪w, B⟫ : ℝ) • w)
  rw [h]
  simp only [real_inner_smul_right, smul_sub, smul_smul]

/-- Since `ω(θ) := cosθ•z + sinθ•w` lies entirely in `span{z,w}`, adding `Sμ•ω(θ)` to a vector `p`
doesn't change its rest-component relative to orthonormal `z,w`. -/
theorem restComp_add_smul_omega {z w p : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0) (Sμ θ : ℝ) :
    restComp z w (Sμ • (Real.cos θ • z + Real.sin θ • w) + p) = restComp z w p := by
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hww : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwz : (⟪w, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzw
  unfold restComp
  simp only [inner_add_right, real_inner_smul_right, hzz, hww, hzw, hwz]
  module

/-- **Case A: rest-components not parallel ⟹ NEVER colinear, for any pole angle `θ` or scalar
`γ₂`.** If the leftover-mass integrals `p,q`'s components orthogonal to `span{z,w}` are not scalar
multiples of each other, the collapse-target vectors `Sμ•ω(θ)+p` and `Sν•ω(θ)+q` can never be
colinear, for every `θ` and every `γ₂`. -/
theorem ne_smul_collapse_of_restComp_not_smul {z w p q : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0) (Sμ Sν : ℝ)
    (hne : ∀ c : ℝ, restComp z w p ≠ c • restComp z w q) (θ γ₂ : ℝ) :
    Sμ • (Real.cos θ • z + Real.sin θ • w) + p
      ≠ γ₂ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q) := by
  apply ne_smul_of_restComp_not_smul
  intro c
  rw [restComp_add_smul_omega hz hw hzw, restComp_add_smul_omega hz hw hzw]
  exact hne c

/-- **Case B step 1: the colinearity ratio is forced.** If `p,q`'s rest-components are parallel with
ratio `r₀` and `q`'s rest-component is nonzero, ANY colinearity witness `γ` (at any angle `θ`) must
equal `r₀` -- the rest-component match alone pins it, since `q`'s rest-component is a nonzero vector
whose scalar multiples are distinct. -/
theorem gamma_eq_r0_of_colinear {z w p q : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0)
    {Sμ Sν r₀ γ θ : ℝ} (hr : restComp z w p = r₀ • restComp z w q) (hq0 : restComp z w q ≠ 0)
    (h : Sμ • (Real.cos θ • z + Real.sin θ • w) + p
           = γ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q)) :
    γ = r₀ := by
  have hL : restComp z w (Sμ • (Real.cos θ • z + Real.sin θ • w) + p) = r₀ • restComp z w q := by
    rw [restComp_add_smul_omega hz hw hzw]; exact hr
  have hR : restComp z w (γ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q))
      = γ • restComp z w q := by
    rw [restComp_smul, restComp_add_smul_omega hz hw hzw]
  rw [h, hR] at hL
  have heq : (r₀ - γ) • restComp z w q = 0 := by
    rw [sub_smul, hL]; abel
  rcases smul_eq_zero.mp heq with h1 | h1
  · linarith [sub_eq_zero.mp h1]
  · exact absurd h1 hq0

/-- **Case B step 2a: the `z`-component of a (ratio-`r₀`) colinearity equation is a linear equation
in `cosθ`.** -/
theorem cos_eq_of_colinear {z w p q : Eucl d} (hz : ‖z‖ = 1) (hzw : (⟪z, w⟫ : ℝ) = 0)
    {Sμ Sν r₀ θ : ℝ}
    (h : Sμ • (Real.cos θ • z + Real.sin θ • w) + p
           = r₀ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q)) :
    (Sμ - r₀ * Sν) * Real.cos θ = r₀ * (⟪z, q⟫ : ℝ) - (⟪z, p⟫ : ℝ) := by
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have := congrArg (fun v => (⟪z, v⟫ : ℝ)) h
  simp only [inner_add_right, inner_smul_right, hzz, hzw] at this
  ring_nf at this ⊢
  linarith [this]

/-- **Case B step 2b: the `w`-component**, symmetric to `cos_eq_of_colinear`. -/
theorem sin_eq_of_colinear {z w p q : Eucl d} (hw : ‖w‖ = 1) (hzw : (⟪z, w⟫ : ℝ) = 0)
    {Sμ Sν r₀ θ : ℝ}
    (h : Sμ • (Real.cos θ • z + Real.sin θ • w) + p
           = r₀ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q)) :
    (Sμ - r₀ * Sν) * Real.sin θ = r₀ * (⟪w, q⟫ : ℝ) - (⟪w, p⟫ : ℝ) := by
  have hww : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwz : (⟪w, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzw
  have := congrArg (fun v => (⟪w, v⟫ : ℝ)) h
  simp only [inner_add_right, inner_smul_right, hww, hwz] at this
  ring_nf at this ⊢
  linarith [this]

/-- **Case B step 3: a linear system with a nonzero coefficient pins the angle uniquely** (mod `2π`),
via `Real.Angle.cos_sin_inj`. -/
theorem angle_eq_of_linear_system (k RHS1 RHS2 θ₁ θ₂ : ℝ) (hk : k ≠ 0)
    (h1a : k * Real.cos θ₁ = RHS1) (h1b : k * Real.sin θ₁ = RHS2)
    (h2a : k * Real.cos θ₂ = RHS1) (h2b : k * Real.sin θ₂ = RHS2) :
    (θ₁ : Real.Angle) = (θ₂ : Real.Angle) := by
  have hc : Real.cos θ₁ = Real.cos θ₂ := mul_left_cancel₀ hk (h1a.trans h2a.symm)
  have hs : Real.sin θ₁ = Real.sin θ₂ := mul_left_cancel₀ hk (h1b.trans h2b.symm)
  exact Real.Angle.cos_sin_inj hc hs

/-- **Case B assembly: at most one angle can be colinear**, given parallel-but-nonzero rest-components
(forced ratio `r₀`) and `Sμ ≠ r₀Sν`. Any two colinearity witnesses at angles `θ₁, θ₂` (with any scalars
`γ₁, γ₂`) force `θ₁ = θ₂` as angles mod `2π` -- combined with a 2-candidate cap-pole pigeonhole giving
two DISTINCT angles, this rules out one of them being colinear. -/
theorem angle_unique_of_colinear {z w p q : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0) {Sμ Sν r₀ : ℝ} (hr : restComp z w p = r₀ • restComp z w q)
    (hq0 : restComp z w q ≠ 0) (hSne : Sμ ≠ r₀ * Sν)
    {θ₁ θ₂ γ₁ γ₂ : ℝ}
    (h1 : Sμ • (Real.cos θ₁ • z + Real.sin θ₁ • w) + p
            = γ₁ • (Sν • (Real.cos θ₁ • z + Real.sin θ₁ • w) + q))
    (h2 : Sμ • (Real.cos θ₂ • z + Real.sin θ₂ • w) + p
            = γ₂ • (Sν • (Real.cos θ₂ • z + Real.sin θ₂ • w) + q)) :
    (θ₁ : Real.Angle) = (θ₂ : Real.Angle) := by
  have hg1 : γ₁ = r₀ := gamma_eq_r0_of_colinear hz hw hzw hr hq0 h1
  have hg2 : γ₂ = r₀ := gamma_eq_r0_of_colinear hz hw hzw hr hq0 h2
  rw [hg1] at h1
  rw [hg2] at h2
  exact angle_eq_of_linear_system (Sμ - r₀ * Sν) (r₀ * (⟪z, q⟫ : ℝ) - (⟪z, p⟫ : ℝ))
    (r₀ * (⟪w, q⟫ : ℝ) - (⟪w, p⟫ : ℝ)) θ₁ θ₂ (sub_ne_zero.mpr hSne)
    (cos_eq_of_colinear hz hzw h1) (sin_eq_of_colinear hw hzw h1)
    (cos_eq_of_colinear hz hzw h2) (sin_eq_of_colinear hw hzw h2)

/-- **The Lagrange/Cauchy-Schwarz gap.** A strictly positive gap `⟪A,B⟫² < ‖A‖²‖B‖²` rules out `A`
being ANY scalar multiple of `B` -- the natural QUANTITATIVE, `W₂`-perturbation-friendly form of
non-colinearity (a polynomial inequality in `A,B` jointly, unlike a raw distance-to-line argument,
which needs `B ≠ 0` and behaves badly as `B → 0`). -/
theorem ne_smul_of_gramGap_pos {A B : Eucl d}
    (hgap : (⟪A, B⟫ : ℝ) ^ 2 < ‖A‖ ^ 2 * ‖B‖ ^ 2) (γ₂ : ℝ) : A ≠ γ₂ • B := by
  intro h
  rw [h] at hgap
  simp only [real_inner_smul_left, norm_smul, real_inner_self_eq_norm_sq, Real.norm_eq_abs,
    mul_pow, sq_abs] at hgap
  nlinarith [hgap]

/-- **Converse of `ne_smul_of_gramGap_pos`.** If `B ≠ 0` and `A` is never a scalar multiple of `B`,
the gramGap is strictly positive -- the Cauchy-Schwarz equality case
(`norm_inner_eq_norm_tfae`) is exactly linear dependence, and `B ≠ 0` upgrades that to "`A` IS some
scalar multiple of `B`". Closes the loop from cases A/B's `∀γ₂,A₀≠γ₂•B₀` conclusion to a usable
`gramGap` hypothesis for `gramGap_pos_of_perturbation`. -/
theorem gramGap_pos_of_ne_smul {A B : Eucl d} (hB0 : B ≠ 0) (hne : ∀ γ₂ : ℝ, A ≠ γ₂ • B) :
    (⟪A, B⟫ : ℝ) ^ 2 < ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
  have hcs : |(⟪A, B⟫ : ℝ)| ≤ ‖A‖ * ‖B‖ := abs_real_inner_le_norm A B
  have hne' : ‖A‖ * ‖B‖ ≠ |(⟪A, B⟫ : ℝ)| := by
    intro heq
    have heq' : |(⟪B, A⟫ : ℝ)| = ‖B‖ * ‖A‖ := by rw [real_inner_comm]; linarith
    have h13 := (norm_inner_eq_norm_tfae ℝ B A).out 0 2
    rw [Real.norm_eq_abs] at h13
    rcases h13.mp heq' with h | ⟨r, hr⟩
    · exact hB0 h
    · exact hne r hr
  have hlt : |(⟪A, B⟫ : ℝ)| < ‖A‖ * ‖B‖ := lt_of_le_of_ne hcs (Ne.symm hne')
  have hAB2 : (⟪A, B⟫ : ℝ) ^ 2 = |(⟪A, B⟫ : ℝ)| ^ 2 := (sq_abs _).symm
  rw [hAB2, ← mul_pow]
  exact pow_lt_pow_left₀ hlt (abs_nonneg _) two_ne_zero

set_option maxHeartbeats 1000000 in
/-- **The gramGap survives `W₂`-scale perturbation.** If the IDEAL targets `A₀,B₀` (norms in
`[m,1]`) have a Lagrange gap of at least `δ`, and the ACTUAL vectors `A,B` are within `rP,rQ` of
them (`rP,rQ` small relative to `m²` and `δ`), the gap survives: `A,B` stay non-colinear. This is
the bridge from cases A/B's IDEAL-target non-colinearity to `Lemma34Part1MeanField.lean`'s ACTUAL
flowed barycenters, which are only `W₂`-close (not equal) to the collapse targets `Sμ•ω+p`,
`Sν•ω+q`. Proof: bound `⟪A,B⟫²` above by `⟪A₀,B₀⟫² + O(rP+rQ)` (expand `⟪A,B⟫` around `⟪A₀,B₀⟫`,
using `‖A₀‖,‖B₀‖≤1` to bound the cross terms) and `‖A‖²‖B‖²` below by `‖A₀‖²‖B₀‖² - O(rP+rQ)`
(expand each squared norm around its ideal value, using `‖A₀‖,‖B₀‖≥m>0` -- via `rP,rQ≤m²/8` -- to
keep the perturbed lower bounds on `‖A‖²,‖B‖²` nonnegative so their product bounds the true
product); the two `O(rP+rQ)` slop terms are dominated by `δ` once `rP,rQ` are small enough
(`20(rP+rQ)<δ` suffices, with comfortable room to spare). -/
theorem gramGap_pos_of_perturbation {A₀ B₀ A B : Eucl d} {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    (hA0lb : m ≤ ‖A₀‖) (hA0 : ‖A₀‖ ≤ 1) (hB0lb : m ≤ ‖B₀‖) (hB0 : ‖B₀‖ ≤ 1)
    {rP rQ δ : ℝ} (hrP : ‖A - A₀‖ ≤ rP) (hrQ : ‖B - B₀‖ ≤ rQ)
    (hrPsmall : rP ≤ m ^ 2 / 8) (hrQsmall : rQ ≤ m ^ 2 / 8)
    (hδ : (⟪A₀, B₀⟫ : ℝ) ^ 2 + δ ≤ ‖A₀‖ ^ 2 * ‖B₀‖ ^ 2)
    (hsmall : 20 * (rP + rQ) < δ) :
    (⟪A, B⟫ : ℝ) ^ 2 < ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
  have hrP0 : 0 ≤ rP := (norm_nonneg _).trans hrP
  have hrQ0 : 0 ≤ rQ := (norm_nonneg _).trans hrQ
  have hrPle1 : rP ≤ 1 := by nlinarith [hrPsmall, hm1]
  have hrQle1 : rQ ≤ 1 := by nlinarith [hrQsmall, hm1]
  have hA0nn : (0 : ℝ) ≤ ‖A₀‖ ^ 2 := sq_nonneg _
  have hB0nn : (0 : ℝ) ≤ ‖B₀‖ ^ 2 := sq_nonneg _
  have hA0sqle : ‖A₀‖ ^ 2 ≤ 1 := by nlinarith [hA0, norm_nonneg A₀]
  have hB0sqle : ‖B₀‖ ^ 2 ≤ 1 := by nlinarith [hB0, norm_nonneg B₀]
  have hABeq : (⟪A, B⟫ : ℝ) = ⟪A₀, B₀⟫ + ⟪A - A₀, B⟫ + ⟪A₀, B - B₀⟫ := by
    rw [inner_sub_left, inner_sub_right]; ring
  have hBnorm : ‖B‖ ≤ 1 + rQ := by
    calc ‖B‖ = ‖B₀ + (B - B₀)‖ := by congr 1; abel
      _ ≤ ‖B₀‖ + ‖B - B₀‖ := norm_add_le _ _
      _ ≤ 1 + rQ := add_le_add hB0 hrQ
  have hc1 : |(⟪A - A₀, B⟫ : ℝ)| ≤ rP * (1 + rQ) := by
    calc |(⟪A - A₀, B⟫ : ℝ)| ≤ ‖A - A₀‖ * ‖B‖ := abs_real_inner_le_norm _ _
      _ ≤ rP * (1 + rQ) := mul_le_mul hrP hBnorm (norm_nonneg _) hrP0
  have hc2 : |(⟪A₀, B - B₀⟫ : ℝ)| ≤ rQ := by
    calc |(⟪A₀, B - B₀⟫ : ℝ)| ≤ ‖A₀‖ * ‖B - B₀‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * rQ := mul_le_mul hA0 hrQ (norm_nonneg _) zero_le_one
      _ = rQ := one_mul rQ
  have hA0B0 : |(⟪A₀, B₀⟫ : ℝ)| ≤ 1 := by
    calc |(⟪A₀, B₀⟫ : ℝ)| ≤ ‖A₀‖ * ‖B₀‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := mul_le_mul hA0 hB0 (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  set e : ℝ := rP * (1 + rQ) + rQ with hedef
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  obtain ⟨hX1, hX2⟩ := abs_le.mp hc1
  obtain ⟨hY1, hY2⟩ := abs_le.mp hc2
  obtain ⟨hZ1, hZ2⟩ := abs_le.mp hA0B0
  have hABsq : (⟪A, B⟫ : ℝ) ^ 2 ≤ (⟪A₀, B₀⟫ : ℝ) ^ 2 + e * (e + 2) := by
    have hub : (⟪A, B⟫ : ℝ) ≤ ⟪A₀, B₀⟫ + e := by rw [hABeq, hedef]; linarith
    have hlb : ⟪A₀, B₀⟫ - e ≤ (⟪A, B⟫ : ℝ) := by rw [hABeq, hedef]; linarith
    nlinarith [hub, hlb, he0, hZ1, hZ2]
  have hesmall : e ≤ 2 * (rP + rQ) := by rw [hedef]; nlinarith [hrPle1, hrQle1, hrP0, hrQ0]
  have hehalf : e ≤ 1 / 2 := by
    have hm2 : m ^ 2 ≤ 1 := by nlinarith [hm0, hm1]
    have hrP8 : rP ≤ 1 / 8 := by linarith
    have hrQ8 : rQ ≤ 1 / 8 := by linarith
    rw [hedef]; nlinarith [hrP8, hrQ8, hrP0, hrQ0]
  have heub : e * (e + 2) ≤ 5 * (rP + rQ) := by nlinarith [hesmall, he0, hehalf]
  have hAnormlb : ‖A₀‖ ^ 2 - 2 * rP - rP ^ 2 ≤ ‖A‖ ^ 2 := by
    have hAeq : A = A₀ + (A - A₀) := by abel
    have heq : ‖A‖ ^ 2 = ‖A₀‖ ^ 2 + 2 * ⟪A₀, A - A₀⟫ + ‖A - A₀‖ ^ 2 := by
      conv_lhs => rw [hAeq]
      exact norm_add_sq_real A₀ (A - A₀)
    have hcross : -(2 * rP) ≤ 2 * (⟪A₀, A - A₀⟫ : ℝ) := by
      have hb : |(⟪A₀, A - A₀⟫ : ℝ)| ≤ 1 * rP :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul hA0 hrP (norm_nonneg _) zero_le_one)
      linarith [(abs_le.mp hb).1]
    nlinarith [heq, hcross]
  have hBnormlb : ‖B₀‖ ^ 2 - 2 * rQ - rQ ^ 2 ≤ ‖B‖ ^ 2 := by
    have hBeq : B = B₀ + (B - B₀) := by abel
    have heq : ‖B‖ ^ 2 = ‖B₀‖ ^ 2 + 2 * ⟪B₀, B - B₀⟫ + ‖B - B₀‖ ^ 2 := by
      conv_lhs => rw [hBeq]
      exact norm_add_sq_real B₀ (B - B₀)
    have hcross : -(2 * rQ) ≤ 2 * (⟪B₀, B - B₀⟫ : ℝ) := by
      have hb : |(⟪B₀, B - B₀⟫ : ℝ)| ≤ 1 * rQ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul hB0 hrQ (norm_nonneg _) zero_le_one)
      linarith [(abs_le.mp hb).1]
    nlinarith [heq, hcross]
  have hAlbpos : 0 ≤ ‖A₀‖ ^ 2 - 2 * rP - rP ^ 2 := by nlinarith [hA0lb, hrPsmall, hm0, hm1]
  have hBlbpos : 0 ≤ ‖B₀‖ ^ 2 - 2 * rQ - rQ ^ 2 := by nlinarith [hB0lb, hrQsmall, hm0, hm1]
  have hprodlb : (‖A₀‖ ^ 2 - 2 * rP - rP ^ 2) * (‖B₀‖ ^ 2 - 2 * rQ - rQ ^ 2) ≤ ‖A‖ ^ 2 * ‖B‖ ^ 2 :=
    mul_le_mul hAnormlb hBnormlb hBlbpos (hAlbpos.trans hAnormlb)
  have hprodgap : ‖A₀‖ ^ 2 * ‖B₀‖ ^ 2 - 4 * (rP + rQ) ≤
      (‖A₀‖ ^ 2 - 2 * rP - rP ^ 2) * (‖B₀‖ ^ 2 - 2 * rQ - rQ ^ 2) := by
    nlinarith [mul_nonneg hrP0 hrQ0, sq_nonneg rP, sq_nonneg rQ,
      mul_le_one₀ hA0sqle hB0nn hB0sqle, mul_le_one₀ hB0sqle hA0nn hA0sqle,
      hA0nn, hB0nn, hrP0, hrQ0]
  nlinarith [hABsq, hδ, hprodlb, hprodgap, heub, hsmall, hrP0, hrQ0]

set_option maxHeartbeats 1000000 in
/-- **`gramGap_pos_of_perturbation` with the norm lower bound derived for free.** The explicit
`m ≤ ‖A₀‖, ‖B₀‖` hypotheses of `gramGap_pos_of_perturbation` are NOT an independent non-degeneracy
condition that needs its own proof at call sites -- Cauchy-Schwarz gives `gramGap A₀ B₀ ≤ ‖A₀‖²‖B₀‖²`
unconditionally, so `δ ≤ gramGap A₀ B₀ ≤ ‖A₀‖²‖B₀‖² ≤ ‖A₀‖²` (using `‖B₀‖ ≤ 1`) forces `‖A₀‖² ≥ δ`
automatically, and symmetrically for `‖B₀‖`. Takes `m := √δ`. This closes what looked like a
genuine open gap for wiring cases A/B into `Lemma34Part1MeanField.lean`'s construction: the
collapse targets `Sμ•ω+p`, `Sν•ω+q` are ALREADY known `≤ 1` (`norm_barycenter_le_one`), so no
separate lower-bound argument (e.g. forcing the cap pole `ω` into the orthant) is needed at all. -/
theorem gramGap_pos_of_perturbation_free {A₀ B₀ A B : Eucl d}
    (hA0 : ‖A₀‖ ≤ 1) (hB0 : ‖B₀‖ ≤ 1)
    {rP rQ δ : ℝ} (hrP : ‖A - A₀‖ ≤ rP) (hrQ : ‖B - B₀‖ ≤ rQ)
    (hδ : (⟪A₀, B₀⟫ : ℝ) ^ 2 + δ ≤ ‖A₀‖ ^ 2 * ‖B₀‖ ^ 2) (hδpos : 0 < δ)
    (hrPsmall : rP ≤ δ / 8) (hrQsmall : rQ ≤ δ / 8) (hsmall : 20 * (rP + rQ) < δ) :
    (⟪A, B⟫ : ℝ) ^ 2 < ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
  have hA0nn : (0 : ℝ) ≤ ‖A₀‖ ^ 2 := sq_nonneg _
  have hB0nn : (0 : ℝ) ≤ ‖B₀‖ ^ 2 := sq_nonneg _
  have hA0sqle : ‖A₀‖ ^ 2 ≤ 1 := by nlinarith [hA0, norm_nonneg A₀]
  have hB0sqle : ‖B₀‖ ^ 2 ≤ 1 := by nlinarith [hB0, norm_nonneg B₀]
  have hA0lbsq : δ ≤ ‖A₀‖ ^ 2 := by nlinarith [sq_nonneg (⟪A₀, B₀⟫ : ℝ), mul_le_one₀ hA0sqle hB0nn hB0sqle]
  have hB0lbsq : δ ≤ ‖B₀‖ ^ 2 := by nlinarith [sq_nonneg (⟪A₀, B₀⟫ : ℝ), mul_le_one₀ hB0sqle hA0nn hA0sqle]
  have hδle1 : δ ≤ 1 := hA0lbsq.trans hA0sqle
  have hA0lb : Real.sqrt δ ≤ ‖A₀‖ := by
    rw [show ‖A₀‖ = Real.sqrt (‖A₀‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hA0lbsq
  have hB0lb : Real.sqrt δ ≤ ‖B₀‖ := by
    rw [show ‖B₀‖ = Real.sqrt (‖B₀‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hB0lbsq
  have hm0 : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδpos
  have hm1 : Real.sqrt δ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hδle1
  have hmsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδpos.le
  refine gramGap_pos_of_perturbation hm0 hm1 hA0lb hA0 hB0lb hB0 hrP hrQ ?_ ?_ hδ hsmall
  · rw [hmsq]; exact hrPsmall
  · rw [hmsq]; exact hrQsmall

/-- `restComp` is 1-Lipschitz (it is the linear orthogonal projection onto the complement of
`span{z,w}`, and orthogonal projections are nonexpansive). -/
theorem restComp_lipschitz {z w : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hzw : (⟪z, w⟫ : ℝ) = 0)
    (A A₀ : Eucl d) : ‖restComp z w A - restComp z w A₀‖ ≤ ‖A - A₀‖ := by
  have hlin : restComp z w A - restComp z w A₀ = restComp z w (A - A₀) := by
    unfold restComp; simp only [inner_sub_right, sub_smul]; abel
  rw [hlin]; unfold restComp
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hww : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  set v := A - A₀
  have hsq : ‖v - (⟪z, v⟫ : ℝ) • z - (⟪w, v⟫ : ℝ) • w‖ ^ 2
      = ‖v‖ ^ 2 - (⟪z, v⟫ : ℝ) ^ 2 - (⟪w, v⟫ : ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hzz, hww, hzw]
    rw [real_inner_comm z v, real_inner_comm w v, real_inner_comm z w, hzw,
      real_inner_self_eq_norm_sq]
    ring
  have hle : ‖v - (⟪z, v⟫ : ℝ) • z - (⟪w, v⟫ : ℝ) • w‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg ((⟪z, v⟫ : ℝ)), sq_nonneg ((⟪w, v⟫ : ℝ))]
  nlinarith [hle, sq_nonneg (‖v - (⟪z, v⟫ : ℝ) • z - (⟪w, v⟫ : ℝ) • w‖ - ‖v‖),
    norm_nonneg (v - (⟪z, v⟫ : ℝ) • z - (⟪w, v⟫ : ℝ) • w), norm_nonneg v]

/-- `restComp` is norm-nonexpansive from the origin (specializes `restComp_lipschitz` to `A₀ = 0`). -/
theorem restComp_norm_le {z w : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hzw : (⟪z, w⟫ : ℝ) = 0)
    (A : Eucl d) : ‖restComp z w A‖ ≤ ‖A‖ := by
  have h0 : restComp z w (0 : Eucl d) = 0 := by unfold restComp; simp
  have := restComp_lipschitz hz hw hzw A 0
  rwa [h0, sub_zero, sub_zero] at this

/-- **The direct case-A perturbation-stability lemma, avoiding `gramGap`'s `B₀ ≠ 0` requirement.**
If the IDEAL rest-components `restComp z w A₀`, `restComp z w B₀` have a strict Lagrange gap `δ`,
and `A,B` are `W₂`-close to `A₀,B₀`, the ACTUAL `A,B` stay non-colinear for every `γ₂` -- no nonzero
hypothesis on `A₀` or `B₀` needed at all (unlike routing through `gramGap_pos_of_ne_smul`), since
`ne_smul_of_restComp_not_smul`'s own argument never needed one. Applies
`gramGap_pos_of_perturbation_free` to the REST-COMPONENTS (not the raw vectors), using
`restComp_lipschitz`/`restComp_norm_le` to transfer the `W₂`-closeness and the `≤1` norm bound
through the (1-Lipschitz, norm-nonexpansive) `restComp` projection. -/
theorem ne_smul_of_restComp_gramGap_perturbation {z w A₀ B₀ A B : Eucl d}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hzw : (⟪z, w⟫ : ℝ) = 0)
    (hA0 : ‖A₀‖ ≤ 1) (hB0 : ‖B₀‖ ≤ 1)
    {rP rQ δ : ℝ} (hrP : ‖A - A₀‖ ≤ rP) (hrQ : ‖B - B₀‖ ≤ rQ)
    (hδ : (⟪restComp z w A₀, restComp z w B₀⟫ : ℝ) ^ 2 + δ
            ≤ ‖restComp z w A₀‖ ^ 2 * ‖restComp z w B₀‖ ^ 2)
    (hδpos : 0 < δ) (hrPsmall : rP ≤ δ / 8) (hrQsmall : rQ ≤ δ / 8) (hsmall : 20 * (rP + rQ) < δ)
    (γ₂ : ℝ) : A ≠ γ₂ • B := by
  have hrA0 : ‖restComp z w A₀‖ ≤ 1 := (restComp_norm_le hz hw hzw A₀).trans hA0
  have hrB0 : ‖restComp z w B₀‖ ≤ 1 := (restComp_norm_le hz hw hzw B₀).trans hB0
  have hrPc : ‖restComp z w A - restComp z w A₀‖ ≤ rP :=
    (restComp_lipschitz hz hw hzw A A₀).trans hrP
  have hrQc : ‖restComp z w B - restComp z w B₀‖ ≤ rQ :=
    (restComp_lipschitz hz hw hzw B B₀).trans hrQ
  have hcs : (⟪restComp z w A, restComp z w B⟫ : ℝ) ^ 2
      < ‖restComp z w A‖ ^ 2 * ‖restComp z w B‖ ^ 2 :=
    gramGap_pos_of_perturbation_free hrA0 hrB0 hrPc hrQc hδ hδpos hrPsmall hrQsmall hsmall
  apply ne_smul_of_restComp_not_smul (z := z) (w := w)
  exact ne_smul_of_gramGap_pos hcs

end MeasureToMeasure.Leaves
