import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Roots

/-!
# Leaf (`disentangle_insert_colinear_phase4_gap`, group G1): a circle meets a line finitely often

Pure geometry, no dependency on the mass-gap-collapse machinery. Bridging fact needed to eventually
generalize `exists_pole_in_cap_ne` (`Leaves/CapPole.lean`) into an arc-avoiding version: an affine
circle of radius `s ≠ 0` centered at `q` inside the 2-plane `span{z,w}` meets a line through the
origin (`span{β}`) in at most finitely many points, so a whole *arc* of candidate poles can avoid a
caller-supplied line, not just a single caller-supplied point (`CapPole`'s current `ω ≠ v`).

Deliberately proved over an ABSTRACT `[NormedAddCommGroup E] [InnerProductSpace ℝ E]`, not `Eucl d`,
in a file with no `Eucl`-touching import, per this repo's known elaboration-timeout gotcha (see
`Leaves/UniformRadiusPacking.lean`). Callers needing `Eucl d` should `apply` this theorem, not
re-elaborate it with `Eucl d` in scope.

## Deviation from the original sketch: θ must range over a BOUNDED interval, not all of `ℝ`

The sketch this leaf was drawn from stated the conclusion as
`{θ : ℝ | ∃ c, ...}.Finite` with `θ` ranging over *all* of `ℝ`. That statement is actually **false**
whenever a solution exists at all: `Real.cos` and `Real.sin` are `2π`-periodic, so if `θ₀` solves the
membership condition then so does every `θ₀ + 2πk`, `k : ℤ` -- an infinite, not finite, set. This is
not a corner case: a genuine witness exists under fully satisfiable hypotheses. Concretely, take any
orthonormal triple `z, w, u` (so `u ∉ span{z,w}`, making `hnondeg` hold trivially since `β := u ∉
span{z,w}`), set `q := z`, `β := u`, `s := 1`. Then for every `θ = π + 2πk`,
`s • (cos θ • z + sin θ • w) + q = -z + z = 0 = 0 • β`, so *every* `θ` in that residue class is a
solution -- the claimed-finite set contains a countably infinite arithmetic progression. This was
verified in isolation (a compiling `¬ Set.Finite` disproof of the literal sketch statement) before
this file was written.

The fix keeps the geometric content ("a circle meets a line in only finitely many points") but makes
it literally true by intersecting the solution set with an arbitrary bounded interval `Set.Icc a b`
(the natural shape for an "arc" of admissible angles at the eventual `CapPole`-generalization call
site, and strictly more general than fixing one period `[0, 2π)`: it holds for *any* bounded range of
angles a caller supplies, however positioned or however many periods wide).

`hnondeg` is preserved EXACTLY as specified in the sketch, unweakened: it is exactly what rules out
the genuinely degenerate configuration where `β ∈ span{z,w} ∧ q ∈ span{z,w}` -- in that case the whole
affine circle can be identically the zero vector shifted into the line's span, and the "finitely many
intersection points" claim would fail for a different, more fundamental reason (the entire circle
coincides with points on the line's containing plane). Do not drop or weaken this hypothesis; a later
group (G2) calls this lemma and needs precisely this non-degeneracy at its call site.

Staging: consumed only by `Leaves/CapPoleAvoiding.lean`'s `exists_pole_in_cap_avoiding`, itself
staged for the planned non-vacuous `lemma_3_4_part2` re-discharge; no other consumers today.

## The complementary planar case (group G3): `circle_meets_line_finite_planar`

`hnondeg` above is load-bearing for `circle_meets_line_finite`'s own proof technique (all
solutions share one `(cos θ, sin θ)` pair), but the finiteness CLAIM is also true in the excluded
planar configuration `β ∈ span{z, w} ∧ q ∈ span{z, w}`, by a different, equally elementary
argument: any witnessing coefficient `c` satisfies `‖c • β - q‖² = s²` (the circle point has norm
`|s|` after rescaling), a real quadratic in `c` with leading coefficient `‖β‖² ≠ 0`, so `c` ranges
over at most a finite root set (`finite_setOf_quadratic_root`); and for each fixed `c` the
solutions `θ` share one `(cos θ, sin θ)` pair (cancel `s ≠ 0`), so each fiber is finite by the
same `2π`-coset argument, factored here as `finite_of_shared_cos_sin`.
`circle_meets_line_finite_planar` packages this; note its proof never actually needs the two span
memberships, but they are kept (underscore-prefixed, per this repo's convention) because the
statement is the case-split complement of `hnondeg` at `exists_pole_in_cap_avoiding_total`'s
call site (`Leaves/CapPoleAvoiding.lean`, group G3) and the paper-facing scope is exactly that
planar configuration. `circle_meets_line_finite` itself is deliberately untouched.
-/

namespace MeasureToMeasure.Leaves

open scoped InnerProductSpace

/-- An affine circle of radius `s ≠ 0`, centered at `q`, inside the 2-plane `span{z, w}` (`z, w`
orthonormal) meets a line through the origin `span{β}` in at most finitely many points, when
restricted to any bounded range of angles `Set.Icc a b`. The non-degeneracy hypothesis `hnondeg`
rules out `β` and `q` both lying in `span{z, w}` -- the one configuration where the whole circle can
satisfy the colinearity condition (see the module docstring for the fix from the original
all-of-`ℝ` sketch, which is genuinely false without this restriction, due to `2π`-periodicity). -/
theorem circle_meets_line_finite {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : E) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hzw : ⟪z, w⟫_ℝ = 0)
    (s : ℝ) (hs : s ≠ 0) (q β : E) (_hβ : β ≠ 0)
    (hnondeg : ¬ (β ∈ Submodule.span ℝ ({z, w} : Set E) ∧
      q ∈ Submodule.span ℝ ({z, w} : Set E)))
    (a b : ℝ) :
    {θ : ℝ | θ ∈ Set.Icc a b ∧
      ∃ c : ℝ, s • (Real.cos θ • z + Real.sin θ • w) + q = c • β}.Finite := by
  have hzz : ⟪z, z⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hwz : ⟪w, z⟫_ℝ = 0 := by rw [real_inner_comm]; exact hzw
  have hww : ⟪w, w⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  set P : Submodule ℝ E := Submodule.span ℝ ({z, w} : Set E) with hP
  have hzP : z ∈ P := Submodule.subset_span (by simp)
  have hwP : w ∈ P := Submodule.subset_span (by simp)
  by_cases hβP : β ∈ P
  · -- `β ∈ span{z,w}` forces `q ∉ span{z,w}` (hnondeg); but any solution would force `q ∈ span{z,w}`.
    -- Contradiction, so the solution set is empty.
    have hSempty : {θ : ℝ | θ ∈ Set.Icc a b ∧
        ∃ c : ℝ, s • (Real.cos θ • z + Real.sin θ • w) + q = c • β} = ∅ := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, c, heq⟩
      have hcβ : c • β ∈ P := P.smul_mem c hβP
      have hX : (Real.cos θ • z + Real.sin θ • w) ∈ P :=
        P.add_mem (P.smul_mem _ hzP) (P.smul_mem _ hwP)
      have hsX : s • (Real.cos θ • z + Real.sin θ • w) ∈ P := P.smul_mem s hX
      have heq' : q = c • β - s • (Real.cos θ • z + Real.sin θ • w) := by
        have h2 := heq; rw [add_comm] at h2; exact eq_sub_of_add_eq h2
      have hqmem : q ∈ P := by rw [heq']; exact P.sub_mem hcβ hsX
      exact hnondeg ⟨hβP, hqmem⟩
    rw [hSempty]; exact Set.finite_empty
  · -- `β ∉ span{z,w}`: any two solutions share the same `(cos θ, sin θ)`, hence lie in one
    -- `2π`-coset; intersected with the bounded interval, that coset is finite.
    set S : Set ℝ := {θ : ℝ | θ ∈ Set.Icc a b ∧
      ∃ c : ℝ, s • (Real.cos θ • z + Real.sin θ • w) + q = c • β} with hS
    have hSicc : S ⊆ Set.Icc a b := fun θ hθ => hθ.1
    have hshare : ∀ θ1 θ2 : ℝ, θ1 ∈ S → θ2 ∈ S →
        Real.cos θ1 = Real.cos θ2 ∧ Real.sin θ1 = Real.sin θ2 := by
      rintro θ1 θ2 ⟨-, c1, he1⟩ ⟨-, c2, he2⟩
      have hsub : s • (Real.cos θ1 • z + Real.sin θ1 • w) -
          s • (Real.cos θ2 • z + Real.sin θ2 • w) = (c1 - c2) • β := by
        have heqdiff : s • (Real.cos θ1 • z + Real.sin θ1 • w) + q -
            (s • (Real.cos θ2 • z + Real.sin θ2 • w) + q) = c1 • β - c2 • β := by
          rw [he1, he2]
        rw [sub_smul]
        rw [show s • (Real.cos θ1 • z + Real.sin θ1 • w) + q -
            (s • (Real.cos θ2 • z + Real.sin θ2 • w) + q) =
            s • (Real.cos θ1 • z + Real.sin θ1 • w) -
            s • (Real.cos θ2 • z + Real.sin θ2 • w) from by abel] at heqdiff
        rw [heqdiff]
      have hc : c1 = c2 := by
        by_contra hne
        apply hβP
        have hβeq : β = (c1 - c2)⁻¹ • (s • (Real.cos θ1 • z + Real.sin θ1 • w) -
            s • (Real.cos θ2 • z + Real.sin θ2 • w)) := by
          rw [hsub, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
        rw [hβeq]
        apply P.smul_mem
        apply P.sub_mem <;> apply P.smul_mem <;>
          exact P.add_mem (P.smul_mem _ hzP) (P.smul_mem _ hwP)
      rw [hc] at hsub
      simp only [sub_self, zero_smul] at hsub
      have hsub0 : s • (Real.cos θ1 • z + Real.sin θ1 • w) =
          s • (Real.cos θ2 • z + Real.sin θ2 • w) := by
        rwa [sub_eq_zero] at hsub
      have hcoseq : Real.cos θ1 = Real.cos θ2 := by
        have hin := congrArg (fun x => ⟪x, z⟫_ℝ) hsub0
        simp only [inner_smul_left, inner_add_left, hzz, hwz, RCLike.conj_to_real] at hin
        have hfinal : s * Real.cos θ1 = s * Real.cos θ2 := by
          field_simp at hin ⊢
          linarith [hin]
        exact mul_left_cancel₀ hs hfinal
      have hsineq : Real.sin θ1 = Real.sin θ2 := by
        have hin := congrArg (fun x => ⟪x, w⟫_ℝ) hsub0
        simp only [inner_smul_left, inner_add_left, hww, hzw, RCLike.conj_to_real] at hin
        have hfinal : s * Real.sin θ1 = s * Real.sin θ2 := by
          field_simp at hin ⊢
          linarith [hin]
        exact mul_left_cancel₀ hs hfinal
      exact ⟨hcoseq, hsineq⟩
    rcases Set.eq_empty_or_nonempty S with hempty | ⟨θ0, hθ0⟩
    · rw [hempty]; exact Set.finite_empty
    · have hSsub : S ⊆ {θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} := by
        intro θ hθ
        obtain ⟨hc, hsn⟩ := hshare θ θ0 hθ hθ0
        have hexp : Complex.exp (θ * Complex.I) = Complex.exp (θ0 * Complex.I) := by
          rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, hc, hsn]
        rw [Complex.exp_eq_exp_iff_exists_int] at hexp
        obtain ⟨n, hn⟩ := hexp
        refine ⟨n, ?_⟩
        have h1 : (θ : ℂ) * Complex.I = ((θ0 + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
          push_cast; rw [hn]; ring
        have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
        exact_mod_cast mul_right_cancel₀ hI h1
      have hAP : ({θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} ∩ Set.Icc a b).Finite := by
        have hT : (0:ℝ) < 2 * Real.pi := by positivity
        set g : ℤ → ℝ := fun n => θ0 + n * (2 * Real.pi) with hg
        have hsub2 : ({θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} ∩ Set.Icc a b) ⊆
            g '' (Set.Icc (⌊(a - θ0) / (2 * Real.pi)⌋) (⌈(b - θ0) / (2 * Real.pi)⌉) : Set ℤ) := by
          rintro θ ⟨⟨n, rfl⟩, ⟨hab1, hab2⟩⟩
          refine ⟨n, ⟨?_, ?_⟩, rfl⟩
          · have hx : (a - θ0) / (2 * Real.pi) ≤ (n : ℝ) := by rw [div_le_iff₀ hT]; linarith
            have hfl := Int.floor_le ((a - θ0) / (2 * Real.pi))
            exact_mod_cast le_trans hfl hx
          · have hx : (n : ℝ) ≤ (b - θ0) / (2 * Real.pi) := by rw [le_div_iff₀ hT]; linarith
            have hce := Int.le_ceil ((b - θ0) / (2 * Real.pi))
            exact_mod_cast le_trans hx hce
        exact Set.Finite.subset ((Set.finite_Icc _ _).image g) hsub2
      apply Set.Finite.subset hAP
      intro θ hθ
      exact ⟨hSsub hθ, hSicc hθ⟩

/-- A real quadratic with nonzero leading coefficient has a finite root set. Packaged over the
explicit `A * c ^ 2 + B * c + D = 0` shape (atomic coefficients, so `Polynomial.C` does not get
simp-normalized through them) for direct reuse by `circle_meets_line_finite_planar`. -/
theorem finite_setOf_quadratic_root (A B D : ℝ) (hA : A ≠ 0) :
    {c : ℝ | A * c ^ 2 + B * c + D = 0}.Finite := by
  set p : Polynomial ℝ := Polynomial.C A * Polynomial.X ^ 2 +
    Polynomial.C B * Polynomial.X + Polynomial.C D with hp
  have hpne : p ≠ 0 := by
    intro h0
    apply hA
    have h2 := congrArg (fun r => Polynomial.coeff r 2) h0
    simpa [hp, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] using h2
  apply (Polynomial.finite_setOf_isRoot hpne).subset
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  linarith

/-- A set of angles confined to a bounded interval, any two of which share the same
`(cos θ, sin θ)` pair, is finite: the shared pair forces all members into a single `2π`-coset
(`Complex.exp` on the unit circle), and a coset of `2πℤ` meets a bounded interval finitely often.
This is the coset argument of `circle_meets_line_finite`'s non-degenerate branch, factored out so
`circle_meets_line_finite_planar` can reuse it fiberwise. -/
theorem finite_of_shared_cos_sin {a b : ℝ} {S : Set ℝ} (hSicc : S ⊆ Set.Icc a b)
    (hshare : ∀ θ1 θ2, θ1 ∈ S → θ2 ∈ S →
      Real.cos θ1 = Real.cos θ2 ∧ Real.sin θ1 = Real.sin θ2) :
    S.Finite := by
  rcases Set.eq_empty_or_nonempty S with hempty | ⟨θ0, hθ0⟩
  · rw [hempty]; exact Set.finite_empty
  · have hSsub : S ⊆ {θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} := by
      intro θ hθ
      obtain ⟨hc, hsn⟩ := hshare θ θ0 hθ hθ0
      have hexp : Complex.exp (θ * Complex.I) = Complex.exp (θ0 * Complex.I) := by
        rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, hc, hsn]
      rw [Complex.exp_eq_exp_iff_exists_int] at hexp
      obtain ⟨n, hn⟩ := hexp
      refine ⟨n, ?_⟩
      have h1 : (θ : ℂ) * Complex.I = ((θ0 + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
        push_cast; rw [hn]; ring
      exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1
    have hAP : ({θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} ∩ Set.Icc a b).Finite := by
      have hT : (0 : ℝ) < 2 * Real.pi := by positivity
      set g : ℤ → ℝ := fun n => θ0 + n * (2 * Real.pi) with hg
      have hsub2 : ({θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} ∩ Set.Icc a b) ⊆
          g '' (Set.Icc (⌊(a - θ0) / (2 * Real.pi)⌋) (⌈(b - θ0) / (2 * Real.pi)⌉) : Set ℤ) := by
        rintro θ ⟨⟨n, rfl⟩, ⟨hab1, hab2⟩⟩
        refine ⟨n, ⟨?_, ?_⟩, rfl⟩
        · have hx : (a - θ0) / (2 * Real.pi) ≤ (n : ℝ) := by rw [div_le_iff₀ hT]; linarith
          exact_mod_cast le_trans (Int.floor_le _) hx
        · have hx : (n : ℝ) ≤ (b - θ0) / (2 * Real.pi) := by rw [le_div_iff₀ hT]; linarith
          exact_mod_cast le_trans hx (Int.le_ceil _)
      exact Set.Finite.subset ((Set.finite_Icc _ _).image g) hsub2
    apply Set.Finite.subset hAP
    intro θ hθ
    exact ⟨hSsub hθ, hSicc hθ⟩

/-- **Planar complement of `circle_meets_line_finite`.** Same conclusion, but in the exact
configuration `circle_meets_line_finite`'s `hnondeg` excludes: `β` and `q` BOTH lie in the
2-plane `span{z, w}`. Then any witnessing coefficient `c` satisfies `‖c • β - q‖² = s²` (the
rescaled circle point has norm `|s|`), a real quadratic in `c` with leading coefficient
`‖β‖² ≠ 0`, so `c` ranges over a finite root set (`finite_setOf_quadratic_root`); for each fixed
`c`, all solving angles share one `(cos θ, sin θ)` pair (cancel `s ≠ 0` and test against the
orthonormal pair), so each fiber is finite (`finite_of_shared_cos_sin`), and the whole solution
set is a finite biUnion of finite fibers.

The two span memberships are not needed by this proof (the quadratic argument is fully general),
but they are kept underscore-prefixed per this repo's convention: this statement's paper-facing
scope is exactly the planar case-split complement at `exists_pole_in_cap_avoiding_total`'s
per-family-member case split (`Leaves/CapPoleAvoiding.lean`, group G3). -/
theorem circle_meets_line_finite_planar {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (z w : E) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hzw : ⟪z, w⟫_ℝ = 0)
    (s : ℝ) (hs : s ≠ 0) (q β : E) (hβ : β ≠ 0)
    (_hβP : β ∈ Submodule.span ℝ ({z, w} : Set E))
    (_hqP : q ∈ Submodule.span ℝ ({z, w} : Set E))
    (a b : ℝ) :
    {θ : ℝ | θ ∈ Set.Icc a b ∧
      ∃ c : ℝ, s • (Real.cos θ • z + Real.sin θ • w) + q = c • β}.Finite := by
  have hzz : ⟪z, z⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hwz : ⟪w, z⟫_ℝ = 0 := by rw [real_inner_comm]; exact hzw
  have hww : ⟪w, w⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  -- the circle point has unit norm, by orthonormality of `z, w`.
  have hnorm : ∀ θ : ℝ, ‖Real.cos θ • z + Real.sin θ • w‖ = 1 := by
    intro θ
    have hsq : ‖Real.cos θ • z + Real.sin θ • w‖ ^ 2 = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hzz, hww, hzw, hwz]
      ring
    calc ‖Real.cos θ • z + Real.sin θ • w‖
        = Real.sqrt (‖Real.cos θ • z + Real.sin θ • w‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 1 := by rw [hsq, add_comm, Real.sin_sq_add_cos_sq]
      _ = 1 := Real.sqrt_one
  -- the witnessing coefficients range over the root set of a nondegenerate real quadratic.
  set C : Set ℝ :=
    {c : ℝ | ‖β‖ ^ 2 * c ^ 2 + -(2 * ⟪β, q⟫_ℝ) * c + (‖q‖ ^ 2 - s ^ 2) = 0} with hC
  have hCfin : C.Finite :=
    finite_setOf_quadratic_root _ _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hβ))
  have hwit : ∀ θ c : ℝ, s • (Real.cos θ • z + Real.sin θ • w) + q = c • β → c ∈ C := by
    intro θ c heq
    have h1 : s • (Real.cos θ • z + Real.sin θ • w) = c • β - q := eq_sub_of_add_eq heq
    have h2 : ‖c • β - q‖ ^ 2 = s ^ 2 := by
      rw [← h1, norm_smul, hnorm θ, mul_one, Real.norm_eq_abs, sq_abs]
    have h3 : ‖c • β - q‖ ^ 2 = ‖β‖ ^ 2 * c ^ 2 - 2 * ⟪β, q⟫_ℝ * c + ‖q‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    simp only [hC, Set.mem_setOf_eq]
    linarith
  -- for a fixed coefficient, all solving angles share one `(cos θ, sin θ)` pair.
  have hfib : ∀ c : ℝ, {θ : ℝ | θ ∈ Set.Icc a b ∧
      s • (Real.cos θ • z + Real.sin θ • w) + q = c • β}.Finite := by
    intro c
    refine finite_of_shared_cos_sin (fun θ hθ => hθ.1) ?_
    rintro θ1 θ2 ⟨-, he1⟩ ⟨-, he2⟩
    have h12 : s • (Real.cos θ1 • z + Real.sin θ1 • w) =
        s • (Real.cos θ2 • z + Real.sin θ2 • w) := by
      have h0 := he1.trans he2.symm
      exact add_right_cancel h0
    have hω : Real.cos θ1 • z + Real.sin θ1 • w = Real.cos θ2 • z + Real.sin θ2 • w :=
      smul_right_injective E hs h12
    constructor
    · have hin := congrArg (fun x => ⟪z, x⟫_ℝ) hω
      simp only [inner_add_right, real_inner_smul_right, hzz, hzw, mul_one, mul_zero,
        add_zero] at hin
      exact hin
    · have hin := congrArg (fun x => ⟪w, x⟫_ℝ) hω
      simp only [inner_add_right, real_inner_smul_right, hwz, hww, mul_one, mul_zero,
        zero_add] at hin
      exact hin
  -- assemble: the solution set is a finite biUnion of finite fibers.
  apply Set.Finite.subset (hCfin.biUnion (fun c _ => hfib c))
  rintro θ ⟨hab, c, heq⟩
  exact Set.mem_biUnion (hwit θ c heq) ⟨hab, heq⟩

end MeasureToMeasure.Leaves
