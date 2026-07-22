import MeasureToMeasure.Foundations.Sphere
import MeasureToMeasure.Leaves.ArcAvoidsLine

/-!
# Leaf (`disentangle_insert_colinear_phase4_gap`, group G2): an arc-valued pole avoiding a line

`CapPole.lean`'s `exists_pole_in_cap_ne` picks the App. B.3 collapse pole `ω` from just **two**
candidate rotations `c·z ± s·w`, enough to dodge a single forbidden vector `v` by pigeonhole. Some
call sites additionally need `ω` to avoid *colinearity* with a finite family of directions `β i`
after an affine rescaling (`s • ω + q ≠ c • β i` for every `c : ℝ`), which a two-point candidate
set cannot generally satisfy (nothing stops both `c·z ± s·w` from being simultaneously bad).

This leaf strengthens the binary choice to a genuine **arc**: the whole open arc
`{ω = cos θ • z + sin θ • w : θ ∈ (-arccos cosR, arccos cosR)}` (i.e. every unit vector strictly
inside the cap `cosR < ⟪z, ·⟫`) is an *uncountable* set of candidates. Excluding `ω = v` removes at
most one `θ` (direct argument: any two solutions share `(cos θ, sin θ)`, hence lie in one `2π`-coset,
and this arc's own bounded range means at most one witness). Excluding each `β i` colinearity
constraint removes only a **finite** set of `θ` each (`circle_meets_line_finite`,
`Leaves/ArcAvoidsLine.lean`, applied once per `i` over the FINITE index type `ι`). An uncountable arc
minus a finite union of finite bad sets is still nonempty, so a good `ω` survives.

The `hnondeg` hypothesis (needed once per family member `i`, exactly as `circle_meets_line_finite`
requires) rules out the one genuinely degenerate configuration per `i`: `β i` and `q` both lying in
`span{z, w}`, i.e. the whole affine circle and the whole line living in the same 2-plane. It is
`circle_meets_line_finite`'s own non-degeneracy hypothesis, unchanged; see that file's docstring for
why it cannot be dropped.

Downstream consumers needing only the abstract bounds `cosR < ⟪z, ω⟫ ≤ 1` (as in
`Leaves/Lemma34Part1MeanField.lean`'s use of `exists_pole_in_cap_ne`) can swap to this strengthened
pole primitive as a drop-in: every conjunct of `exists_pole_in_cap_ne`'s conclusion is reproduced
here (norm, cap membership, `≠ v`, `span{z,w}` membership), plus the new colinearity-avoidance
conjunct.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Arc-valued spherical-cap pigeonhole, avoiding a finite family of lines.** Given unit
`z, w` orthonormal, a cap threshold `cosR ∈ [0, 1)`, a forbidden vector `v`, an affine rescaling
`s ≠ 0, q`, and a FINITE family of nonzero "bad" directions `β : ι → Eucl d` (each satisfying
`circle_meets_line_finite`'s own non-degeneracy hypothesis against `z, w, q`), there is a unit
vector `ω` strictly inside the cap `cosR < ⟪z, ω⟫`, distinct from `v`, lying in `span{z, w}`, and
whose affine image `s • ω + q` is never a scalar multiple of any `β i`.

Realised by parametrizing the cap's arc as `ω(θ) = cos θ • z + sin θ • w` for
`θ ∈ (-arccos cosR, arccos cosR)`: the `≠ v` exclusion removes at most one `θ` (any two solutions
share `(cos θ, sin θ)`, forcing them into the same `2π`-coset, and the coset meets this bounded arc
in at most one point), and each `β i` exclusion removes only a finite set of `θ`
(`circle_meets_line_finite`). The arc itself is uncountable (`Set.Ioo_infinite`), so it survives
minus this finite union of finite bad sets. -/
theorem exists_pole_in_cap_avoiding (z w : Eucl d) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0) (cosR : ℝ) (hcosR : cosR ∈ Set.Ico (0 : ℝ) 1)
    (v : Eucl d) (s : ℝ) (hs : s ≠ 0) (q : Eucl d)
    {ι : Type*} [Fintype ι] (β : ι → Eucl d) (hβ : ∀ i, β i ≠ 0)
    (hnondeg : ∀ i, ¬ (β i ∈ Submodule.span ℝ ({z, w} : Set (Eucl d)) ∧
      q ∈ Submodule.span ℝ ({z, w} : Set (Eucl d)))) :
    ∃ ω : Eucl d, ‖ω‖ = 1 ∧ cosR < (⟪z, ω⟫ : ℝ) ∧ ω ≠ v ∧
      ω = (⟪z, ω⟫ : ℝ) • z + (⟪w, ω⟫ : ℝ) • w ∧
      ∀ i, ∀ c : ℝ, s • ω + q ≠ c • β i := by
  obtain ⟨hcosR0, hcosR1⟩ := hcosR
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hwz : (⟪w, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzw
  have hww : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  -- `R := arccos cosR` is the half-width of the arc: `cos θ > cosR` exactly on `(-R, R)`.
  set R : ℝ := Real.arccos cosR with hR
  have hRpos : 0 < R := Real.arccos_pos.mpr hcosR1
  have hcosRle1 : cosR ≤ 1 := le_of_lt hcosR1
  have hcosRge : (-1 : ℝ) ≤ cosR := by linarith
  have hcosReq : Real.cos R = cosR := Real.cos_arccos hcosRge hcosRle1
  have hRlepi : R ≤ Real.pi := Real.arccos_le_pi cosR
  have hcosgt : ∀ θ : ℝ, θ ∈ Set.Ioo (-R) R → cosR < Real.cos θ := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    rw [← hcosReq]
    rcases lt_or_ge θ 0 with hθ0 | hθ0
    · have heq : Real.cos θ = Real.cos (-θ) := (Real.cos_neg θ).symm
      rw [heq]
      exact Real.strictAntiOn_cos (a := -θ) (b := R) ⟨by linarith, by linarith⟩
        ⟨by linarith, hRlepi⟩ (by linarith)
    · exact Real.strictAntiOn_cos (a := θ) (b := R) ⟨hθ0, by linarith⟩ ⟨by linarith, hRlepi⟩ h2
  -- the arc parametrization `ω(θ) = cos θ • z + sin θ • w`.
  set ωf : ℝ → Eucl d := fun θ => Real.cos θ • z + Real.sin θ • w with hωf
  have hnorm : ∀ θ, ‖ωf θ‖ = 1 := by
    intro θ
    have hsq : ‖ωf θ‖ ^ 2 = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [hωf, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hzz, hww, hzw, hwz]
      ring
    calc ‖ωf θ‖ = Real.sqrt (‖ωf θ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 1 := by rw [hsq, add_comm, Real.sin_sq_add_cos_sq]
      _ = 1 := Real.sqrt_one
  have hinnerz : ∀ θ, (⟪z, ωf θ⟫ : ℝ) = Real.cos θ := by
    intro θ; simp only [hωf, inner_add_right, real_inner_smul_right, hzz, hzw]; ring
  have hinnerw : ∀ θ, (⟪w, ωf θ⟫ : ℝ) = Real.sin θ := by
    intro θ; simp only [hωf, inner_add_right, real_inner_smul_right, hwz, hww]; ring
  have hspan : ∀ θ, ωf θ = (⟪z, ωf θ⟫ : ℝ) • z + (⟪w, ωf θ⟫ : ℝ) • w := by
    intro θ; rw [hinnerz, hinnerw]
  -- bad set for `v`: at most one `θ`, by a direct `(cos θ, sin θ)`-sharing + `2π`-coset argument.
  set Sv : Set ℝ := {θ | θ ∈ Set.Ioo (-R) R ∧ ωf θ = v} with hSv
  have hSvfin : Sv.Finite := by
    rcases Set.eq_empty_or_nonempty Sv with hemp | ⟨θ0, hθ0⟩
    · rw [hemp]; exact Set.finite_empty
    · have hsub : Sv ⊆ {θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} := by
        intro θ hθ
        have hcoseq : Real.cos θ = Real.cos θ0 := by
          have := congrArg (fun x : Eucl d => (⟪z, x⟫ : ℝ)) (hθ.2.trans hθ0.2.symm)
          simpa [hinnerz] using this
        have hsineq : Real.sin θ = Real.sin θ0 := by
          have := congrArg (fun x : Eucl d => (⟪w, x⟫ : ℝ)) (hθ.2.trans hθ0.2.symm)
          simpa [hinnerw] using this
        have hexp : Complex.exp (θ * Complex.I) = Complex.exp (θ0 * Complex.I) := by
          rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, hcoseq, hsineq]
        rw [Complex.exp_eq_exp_iff_exists_int] at hexp
        obtain ⟨n, hn⟩ := hexp
        refine ⟨n, ?_⟩
        have h1 : (θ : ℂ) * Complex.I = ((θ0 + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
          push_cast; rw [hn]; ring
        exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1
      have hAP : ({θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} ∩ Set.Icc (-R) R).Finite := by
        have hT : (0 : ℝ) < 2 * Real.pi := by positivity
        set g : ℤ → ℝ := fun n => θ0 + n * (2 * Real.pi) with hg
        have hsub2 : ({θ : ℝ | ∃ n : ℤ, θ = θ0 + n * (2 * Real.pi)} ∩ Set.Icc (-R) R) ⊆
            g '' (Set.Icc (⌊(-R - θ0) / (2 * Real.pi)⌋) (⌈(R - θ0) / (2 * Real.pi)⌉) : Set ℤ) := by
          rintro θ ⟨⟨n, rfl⟩, ⟨hab1, hab2⟩⟩
          refine ⟨n, ⟨?_, ?_⟩, rfl⟩
          · have hx : (-R - θ0) / (2 * Real.pi) ≤ (n : ℝ) := by rw [div_le_iff₀ hT]; linarith
            exact_mod_cast le_trans (Int.floor_le _) hx
          · have hx : (n : ℝ) ≤ (R - θ0) / (2 * Real.pi) := by rw [le_div_iff₀ hT]; linarith
            exact_mod_cast le_trans hx (Int.le_ceil _)
        exact Set.Finite.subset ((Set.finite_Icc _ _).image g) hsub2
      apply Set.Finite.subset hAP
      intro θ hθ
      exact ⟨hsub hθ, le_of_lt hθ.1.1, le_of_lt hθ.1.2⟩
  -- bad set for each `i`: finite, via `circle_meets_line_finite`.
  have hSifin : ∀ i, {θ : ℝ | θ ∈ Set.Icc (-R) R ∧ ∃ c : ℝ, s • ωf θ + q = c • β i}.Finite := by
    intro i
    exact circle_meets_line_finite z w hz hw hzw s hs q (β i) (hβ i) (hnondeg i) (-R) R
  have hBfin : (Sv ∪ ⋃ i, {θ : ℝ | θ ∈ Set.Icc (-R) R ∧ ∃ c : ℝ, s • ωf θ + q = c • β i}).Finite :=
    hSvfin.union (Set.finite_iUnion hSifin)
  -- the arc is uncountable, so it survives minus this finite bad set.
  have hIooInf : (Set.Ioo (-R) R).Infinite := Set.Ioo_infinite (by linarith)
  have hdiffInf := hIooInf.sdiff hBfin
  obtain ⟨θ, hθ⟩ := hdiffInf.nonempty
  obtain ⟨hθIoo, hθnotB⟩ := hθ
  refine ⟨ωf θ, hnorm θ, ?_, ?_, hspan θ, ?_⟩
  · rw [hinnerz]; exact hcosgt θ hθIoo
  · intro hcontra
    apply hθnotB
    left
    exact ⟨hθIoo, hcontra⟩
  · intro i c hcontra
    apply hθnotB
    right
    rw [Set.mem_iUnion]
    exact ⟨i, ⟨Set.Ioo_subset_Icc_self hθIoo, c, hcontra⟩⟩

end MeasureToMeasure.Leaves
