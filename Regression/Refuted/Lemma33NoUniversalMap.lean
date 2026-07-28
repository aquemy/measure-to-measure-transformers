import Regression.NonVacuity.MidLevel

/-!
# `lemma_3_3` has no universal-map (`V = 0`) discharge (finding F28)

Honest-negative route documentation, the same role `HgenRestUnconditionallyFalse.lean` plays for
`lemma_3_4_part2` (F22): a kernel-checked reason why NO future attempt should try to discharge the
unconditional axiom `MeasureToMeasure.Statements.lemma_3_3` with `V = 0` (value-matrix-free)
schedules, and why the cap-separation companion `lemma_3_3_of_cap_separation`
(`MeasureToMeasure/Leaves/Lemma33CapSeparation.lean`) genuinely needs its gate.

**Why `V = 0` schedules are universal maps.** `attnStep_eq_map_blockFlow`
(`MeasureToMeasure/Foundations/AttnStepExistence.lean`) shows a `V = 0` attention piece acts on
EVERY sphere-supported probability input as the pushforward along ONE measure-independent map (the
linear block flow); composing pieces composes the maps. So a `V = 0` schedule `θ` realizes
`attnMeasureFlow θ μ = Measure.map Φ μ` for a single measurable `Φ` shared by all inputs `μ`. The
Lean statement below therefore quantifies over measurable MAPS, keeping it clean; this paragraph
records the schedule connection as documented prose.

**The admissible configuration.** `d = 2`, atoms on `sphere 2 ∩ orthant 2` with exact rationals:
`uA = (3/5, 4/5)`, `uB = (4/5, 3/5)`, `uC = (5/13, 12/13)`. Acted member
`muActed = (δ_uA + δ_uB)/2`, bystander `nuBeta = (δ_uA + δ_uC)/2`. The two-member family
`refFam = ![muActed, nuBeta]` with acted index `j = 0` and colinear companion `ν₀ := muActed`
(`c = 1`) satisfies EVERY hypothesis of `lemma_3_3` -- probability, sphere and orthant support,
pairwise fully-non-colinear barycenters (`(7/10, 7/10)` has equal coordinates, `(32/65, 56/65)`
does not), colinear companion -- all kernel-checked below, so `lemma_3_3` PROMISES a schedule
here for every `T, ε > 0`.

**The obstruction: a shared atom.** `ω̂` is the normalized barycenter of `muActed`, the direction
of the MIDPOINT of `uA` and `uB`, so its two coordinates are equal while `uA` and `uC` each have
unequal coordinates: `uA ≠ ω̂` and `uC ≠ ω̂`, giving
`ε₀ := min (dist uA ω̂) (dist uC ω̂) > 0`. For any measurable `Φ` with
`Measure.map Φ nuBeta = nuBeta` (the fixing clause at the bystander index `i = 1 ≠ j`), pushing
the null set `{uA, uC}ᶜ` back through `Φ` forces `Φ uA ∈ {uA, uC}`; but then
`Measure.map Φ muActed` keeps mass at least `1/2` on `{uA, uC}`, a set disjoint from
`Metric.ball ω̂ ε` once `ε < ε₀` -- so the shrink clause
`supportedIn (Measure.map Φ muActed) (Metric.ball ω̂ ε)` fails for every `ε ∈ (0, ε₀)`. One map
cannot both fix the bystander (which owns the atom `uA`) and evacuate the acted member (which
owns the same atom) into a small ball away from `uA`.

**Consequences.** The fixing and shrink clauses of `lemma_3_3`'s conclusion are jointly
unrealizable by any universal map at this admissible instance, so no `V = 0` schedule can
discharge the unconditional axiom: the paper's `V ≠ 0` `Ψ₁` phase (App. B.2, p.33,
arXiv:2411.04551v3), whose field reads the flowing measure's barycenter and hence acts
differently on different inputs, is ESSENTIAL, confirming the F14 mean-field classification of
`lemma_3_3`. This does NOT refute `lemma_3_3` itself, only the universal-map route to it; the
route is closed permanently. Recorded as finding F28 in RESEARCH.md.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements Regression.NonVacuity
open scoped ENNReal

/-- First shared atom: `(3/5, 4/5)`, on the unit circle, open first quadrant. -/
noncomputable def uA : Eucl 2 := pt (3/5) (4/5)

/-- Second atom of the acted member: `(4/5, 3/5)`. -/
noncomputable def uB : Eucl 2 := pt (4/5) (3/5)

/-- Second atom of the bystander: `(5/13, 12/13)`. -/
noncomputable def uC : Eucl 2 := pt (5/13) (12/13)

/-- The acted member: `(δ_uA + δ_uB)/2`. -/
noncomputable def muActed : Measure (Eucl 2) := twoAtom (1/2) (1/2) uA uB

/-- The bystander: `(δ_uA + δ_uC)/2`. It shares the atom `uA` with the acted member. -/
noncomputable def nuBeta : Measure (Eucl 2) := twoAtom (1/2) (1/2) uA uC

/-- The collapse target of `lemma_3_3`'s conclusion at acted member `muActed`: the normalized
barycenter direction. -/
noncomputable def omegaHat : Eucl 2 :=
  ‖MeasureToMeasure.Leaves.barycenter muActed‖⁻¹ • MeasureToMeasure.Leaves.barycenter muActed

theorem half_add_half : (1/2 : ℝ≥0∞) + 1/2 = 1 := ENNReal.add_halves 1

instance : IsProbabilityMeasure muActed := isProbabilityMeasure_twoAtom half_add_half uA uB

instance : IsProbabilityMeasure nuBeta := isProbabilityMeasure_twoAtom half_add_half uA uC

/-- `orthant 2` is a finite intersection of open coordinate half-spaces, hence measurable. -/
theorem measurableSet_orthant2 : MeasurableSet (orthant 2) := by
  have hrw : orthant 2 = ⋂ j : Fin 2, {x : Eucl 2 | 0 < x j} := by
    ext x; simp only [orthant, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hrw]
  exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const (by fun_prop)

theorem muActed_sphere : supportedIn muActed (MeasureToMeasure.sphere 2) :=
  twoAtom_supportedIn Metric.isClosed_sphere.measurableSet
    (pt_mem_sphere (by norm_num)) (pt_mem_sphere (by norm_num))

theorem muActed_orthant : supportedIn muActed (orthant 2) :=
  twoAtom_supportedIn measurableSet_orthant2
    (pt_mem_orthant (by norm_num) (by norm_num)) (pt_mem_orthant (by norm_num) (by norm_num))

theorem nuBeta_sphere : supportedIn nuBeta (MeasureToMeasure.sphere 2) :=
  twoAtom_supportedIn Metric.isClosed_sphere.measurableSet
    (pt_mem_sphere (by norm_num)) (pt_mem_sphere (by norm_num))

theorem nuBeta_orthant : supportedIn nuBeta (orthant 2) :=
  twoAtom_supportedIn measurableSet_orthant2
    (pt_mem_orthant (by norm_num) (by norm_num)) (pt_mem_orthant (by norm_num) (by norm_num))

/-- The acted barycenter: the midpoint `(7/10, 7/10)`, EQUAL coordinates. -/
theorem bary_muActed : MeasureToMeasure.Leaves.barycenter muActed = pt (7/10) (7/10) := by
  rw [muActed, twoAtom_barycenter (by finiteness) (by finiteness)]
  have h : (1/2 : ℝ≥0∞).toReal = 1/2 := by simp
  rw [h]
  ext i
  fin_cases i <;>
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, uA, uB, pt]
      norm_num

/-- The bystander barycenter: `(32/65, 56/65)`, UNEQUAL coordinates. -/
theorem bary_nuBeta : MeasureToMeasure.Leaves.barycenter nuBeta = pt (32/65) (56/65) := by
  rw [nuBeta, twoAtom_barycenter (by finiteness) (by finiteness)]
  have h : (1/2 : ℝ≥0∞).toReal = 1/2 := by simp
  rw [h]
  ext i
  fin_cases i <;>
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, uA, uC, pt]
      norm_num

/-- Full non-colinearity, acted against bystander: `(7/10, 7/10) ≠ r • (32/65, 56/65)` for every
real `r` (equal against unequal coordinates; `r = 0` is defeated by `7/10 ≠ 0`). -/
theorem muActed_noncolinear_nuBeta : ∀ r : ℝ,
    MeasureToMeasure.Leaves.barycenter muActed ≠
      r • MeasureToMeasure.Leaves.barycenter nuBeta := by
  intro r h
  rw [bary_muActed, bary_nuBeta] at h
  have h0 : (pt (7/10) (7/10) : Eucl 2) 0 = (r • (pt (32/65) (56/65) : Eucl 2)) 0 := by rw [h]
  have h1 : (pt (7/10) (7/10) : Eucl 2) 1 = (r • (pt (32/65) (56/65) : Eucl 2)) 1 := by rw [h]
  simp only [PiLp.smul_apply, smul_eq_mul, pt] at h0 h1
  norm_num at h0 h1
  linarith

/-- Full non-colinearity, bystander against acted. -/
theorem nuBeta_noncolinear_muActed : ∀ r : ℝ,
    MeasureToMeasure.Leaves.barycenter nuBeta ≠
      r • MeasureToMeasure.Leaves.barycenter muActed := by
  intro r h
  rw [bary_muActed, bary_nuBeta] at h
  have h0 : (pt (32/65) (56/65) : Eucl 2) 0 = (r • (pt (7/10) (7/10) : Eucl 2)) 0 := by rw [h]
  have h1 : (pt (32/65) (56/65) : Eucl 2) 1 = (r • (pt (7/10) (7/10) : Eucl 2)) 1 := by rw [h]
  simp only [PiLp.smul_apply, smul_eq_mul, pt] at h0 h1
  norm_num at h0 h1
  linarith

/-- The two-member family `lemma_3_3` is offered: acted member at index `0`, bystander at
index `1`. -/
noncomputable def refFam : Fin 2 → Measure (Eucl 2) := ![muActed, nuBeta]

/-- The family satisfies `lemma_3_3`'s pairwise full-non-colinearity hypothesis. -/
theorem refFam_pairwise_noncolinear :
    Pairwise fun i k => ∀ c : ℝ, MeasureToMeasure.Leaves.barycenter (refFam i) ≠
      c • MeasureToMeasure.Leaves.barycenter (refFam k) := by
  intro i k hik
  fin_cases i <;> fin_cases k <;> simp_all [refFam] <;>
    first
      | exact muActed_noncolinear_nuBeta
      | exact nuBeta_noncolinear_muActed

/-- The colinear-companion hypothesis at `ν₀ := muActed`, acted index `j = 0`, `c = 1`. -/
theorem refFam_colinear_companion :
    ∃ c : ℝ, MeasureToMeasure.Leaves.barycenter muActed =
      c • MeasureToMeasure.Leaves.barycenter (refFam 0) :=
  ⟨1, by simp [refFam]⟩

/-- Both coordinates of `ω̂` agree (it is the normalized MIDPOINT direction of `uA` and `uB`). -/
theorem omegaHat_coords : omegaHat 0 = omegaHat 1 := by
  rw [omegaHat, bary_muActed]
  simp only [PiLp.smul_apply, smul_eq_mul, pt_apply_zero, pt_apply_one]

/-- The shared atom is NOT the collapse target: `uA`'s coordinates `3/5 ≠ 4/5` differ, `ω̂`'s
agree. -/
theorem uA_ne_omegaHat : uA ≠ omegaHat := by
  intro h
  have h0 : uA 0 = omegaHat 0 := by rw [h]
  have h1 : uA 1 = omegaHat 1 := by rw [h]
  have : (3/5 : ℝ) = 4/5 := by
    calc (3/5 : ℝ) = uA 0 := (pt_apply_zero _ _).symm
    _ = omegaHat 1 := by rw [h0, omegaHat_coords]
    _ = uA 1 := h1.symm
    _ = 4/5 := pt_apply_one _ _
  norm_num at this

/-- The bystander's private atom is not the collapse target either: `5/13 ≠ 12/13`. -/
theorem uC_ne_omegaHat : uC ≠ omegaHat := by
  intro h
  have h0 : uC 0 = omegaHat 0 := by rw [h]
  have h1 : uC 1 = omegaHat 1 := by rw [h]
  have : (5/13 : ℝ) = 12/13 := by
    calc (5/13 : ℝ) = uC 0 := (pt_apply_zero _ _).symm
    _ = omegaHat 1 := by rw [h0, omegaHat_coords]
    _ = uC 1 := h1.symm
    _ = 12/13 := pt_apply_one _ _
  norm_num at this

/-- **The route refutation (F28).** No measurable map that fixes the bystander `nuBeta` can push
the acted member `muActed` into the `ε`-ball around `ω̂` for any `ε` below the explicit
`ε₀ = min (dist uA ω̂) (dist uC ω̂) > 0`: fixing `nuBeta` pins `Φ uA` inside `{uA, uC}`, which
keeps at least half of the pushed acted mass on `{uA, uC}`, a set the small ball misses entirely.
Since every `V = 0` schedule acts as one such universal map on all sphere-supported probability
inputs (`attnStep_eq_map_blockFlow`), and this configuration satisfies every hypothesis of
`lemma_3_3` (witnesses above), the axiom's fixing-plus-shrink conclusion is out of reach of the
whole `V = 0` class. -/
theorem lemma33_no_universal_map (Φ : Eucl 2 → Eucl 2) (hΦ : Measurable Φ)
    (hfix : Measure.map Φ nuBeta = nuBeta) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ¬ supportedIn (Measure.map Φ muActed) (Metric.ball omegaHat ε) := by
  refine ⟨min (dist uA omegaHat) (dist uC omegaHat),
    lt_min (dist_pos.mpr uA_ne_omegaHat) (dist_pos.mpr uC_ne_omegaHat), ?_⟩
  intro ε hε hεlt hsupp
  have hS : MeasurableSet ({uA, uC} : Set (Eucl 2)) :=
    (measurableSet_singleton uC).insert uA
  -- Step 1: the fixed bystander pins `Φ uA` inside `{uA, uC}`.
  have hβS : nuBeta ({uA, uC} : Set (Eucl 2))ᶜ = 0 :=
    twoAtom_supportedIn hS (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)
  have hmapβ : nuBeta (Φ ⁻¹' ({uA, uC} : Set (Eucl 2))ᶜ) = 0 := by
    rw [← Measure.map_apply hΦ hS.compl, hfix]
    exact hβS
  have hexp : (1/2 : ℝ≥0∞) * Measure.dirac uA (Φ ⁻¹' ({uA, uC} : Set (Eucl 2))ᶜ)
      + (1/2 : ℝ≥0∞) * Measure.dirac uC (Φ ⁻¹' ({uA, uC} : Set (Eucl 2))ᶜ) = 0 := by
    simpa [nuBeta, twoAtom, Measure.add_apply, Measure.smul_apply, smul_eq_mul] using hmapβ
  have hA0 : Measure.dirac uA (Φ ⁻¹' ({uA, uC} : Set (Eucl 2))ᶜ) = 0 := by
    have h2 := (add_eq_zero.mp hexp).1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hmem : Φ uA ∈ ({uA, uC} : Set (Eucl 2)) := by
    by_contra hnot
    rw [Measure.dirac_apply' _ (hΦ hS.compl),
      Set.indicator_of_mem (Set.mem_preimage.mpr hnot)] at hA0
    norm_num at hA0
  -- Step 2: the acted member keeps mass at least `1/2` on `{uA, uC}`.
  have hmass : (1/2 : ℝ≥0∞) ≤ Measure.map Φ muActed ({uA, uC} : Set (Eucl 2)) := by
    rw [Measure.map_apply hΦ hS, muActed, twoAtom]
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    have hdA : Measure.dirac uA (Φ ⁻¹' ({uA, uC} : Set (Eucl 2))) = 1 := by
      rw [Measure.dirac_apply' _ (hΦ hS)]
      exact Set.indicator_of_mem (Set.mem_preimage.mpr hmem) _
    rw [hdA, mul_one]
    exact le_add_right le_rfl
  -- Step 3: but `{uA, uC}` misses the ball entirely once `ε < ε₀`.
  have hsub : ({uA, uC} : Set (Eucl 2)) ⊆ (Metric.ball omegaHat ε)ᶜ := by
    intro x hx
    rcases hx with rfl | hx
    · exact fun hball => absurd (Metric.mem_ball.mp hball)
        (not_lt.mpr (le_of_lt (lt_of_lt_of_le hεlt (min_le_left _ _))))
    · rcases hx with rfl
      exact fun hball => absurd (Metric.mem_ball.mp hball)
        (not_lt.mpr (le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))))
  have hzero : Measure.map Φ muActed ({uA, uC} : Set (Eucl 2)) = 0 :=
    measure_mono_null hsub hsupp
  rw [hzero] at hmass
  exact absurd hmass (by norm_num)

/-- Satisfiability of the theorem's hypothesis bundle (full application, conclusion ascribed):
the identity map fixes `nuBeta`, so the theorem genuinely fires on at least one map. -/
example : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ¬ supportedIn (Measure.map id muActed) (Metric.ball omegaHat ε) :=
  lemma33_no_universal_map id measurable_id (Measure.map_id)

end Regression.Refuted
