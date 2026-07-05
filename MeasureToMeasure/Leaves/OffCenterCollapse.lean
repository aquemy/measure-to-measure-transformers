import MeasureToMeasure.Leaves.BarycenterNonColinear
import MeasureToMeasure.Leaves.GeodesicHullConvex

/-!
# Leaf (Lemma 3.4 Part 1, Path I): barycenter of the non-self-centered collapse

The App. B.3 Part 1 separation gates a **fixed** cap `{cos R < ⟪z, ·⟫}` (direction `z`, chosen so the
two measures put different mass on it) and collapses that cap's mass onto a **separate** pole `ω = x*`
picked by the pigeonhole. The exact target of that collapse is the pushforward `μ.map g` of the
non-self-centered collapse map

  `g = capCollapseMap z ω cos R = {cos R < ⟪z, ·⟫}.piecewise (fun _ => ω) id`,

which sends the open gate cap to `ω` and fixes everything else. (The self-centered `collapseMap ω cos R`
of `W2Collapse.lean` is the special case `z = ω`; Path I needs the gate direction and the pole to
differ.)

This leaf computes its **barycenter**, the vector the separation argument actually compares:

  `ℰ_{μ.map g} = μ(cap)·ω + ∫_{capᶜ} x dμ`.

The proof is pure measure theory, independent of the flow: `integral_map` change of variables turns
`ℰ_{μ.map g} = ∫ g dμ`, and `integral_add_compl` splits it over the cap and its complement — `g` is
the constant `ω` on the cap (`∫_cap ω = μ(cap)·ω`) and the identity off it. Integrability of `g` comes
from sphere support (`‖g x‖ ≤ max ‖ω‖ 1` a.e.). This is the `ℰ*_μ` whose gap across `μ, ν` the
pigeonhole leaf `exists_mem_ball_barycenter_collapse_ne` (L3a) makes nonzero.
-/

namespace MeasureToMeasure

open MeasureTheory
open MeasureToMeasure.Leaves (barycenter)
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The **non-self-centered collapse map**: send the open gate cap `{cos R < ⟪z, ·⟫}` (direction `z`)
to the pole `ω`, fix everything else. Its pushforward `μ.map (capCollapseMap z ω cos R)` is the exact
target `α_μ` of the App. B.3 Part 1 collapse when the gate and the pole differ; the self-centered
`collapseMap ω cos R` is the case `z = ω`. -/
noncomputable def capCollapseMap (z ω : Eucl d) (cosR : ℝ) : Eucl d → Eucl d :=
  {x | cosR < (⟪z, x⟫ : ℝ)}.piecewise (fun _ => ω) id

/-- **Barycenter of the non-self-centered collapse.** For a sphere-supported probability measure `μ`,
the barycenter of the collapsed measure splits into the cap mass concentrated at the pole plus the
untouched tail: `ℰ_{μ.map (capCollapseMap z ω cos R)} = μ(cap)·ω + ∫_{capᶜ} x dμ`, where
`cap = {cos R < ⟪z, ·⟫}`. Pure change of variables (`integral_map`) plus set additivity
(`integral_add_compl`); `g` is `ω` on the cap and `id` off it. -/
theorem barycenter_map_capCollapse {z ω : Eucl d} {cosR : ℝ}
    {μ : Measure (Eucl d)} [IsProbabilityMeasure μ] (hμs : μ (sphere d)ᶜ = 0) :
    barycenter (μ.map (capCollapseMap z ω cosR))
      = (μ {x | cosR < (⟪z, x⟫ : ℝ)}).toReal • ω
        + ∫ x in {x | cosR < (⟪z, x⟫ : ℝ)}ᶜ, x ∂μ := by
  set S : Set (Eucl d) := {x | cosR < (⟪z, x⟫ : ℝ)} with hS
  -- measurability of the gate cap and the collapse map
  have hcont : Continuous (fun x : Eucl d => (⟪z, x⟫ : ℝ)) := continuous_const.inner continuous_id
  have hSM : MeasurableSet S := hcont.measurable measurableSet_Ioi
  have hgmeas : Measurable (capCollapseMap z ω cosR) :=
    Measurable.piecewise hSM measurable_const measurable_id
  -- μ-a.e. every point is on the sphere, so `‖g x‖ ≤ max ‖ω‖ 1`
  have hae : ∀ᵐ x ∂μ, x ∈ sphere d := ae_iff.mpr hμs
  have hgInt : Integrable (capCollapseMap z ω cosR) μ := by
    refine Integrable.mono' (integrable_const (max ‖ω‖ 1)) hgmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with x hx
    by_cases hxS : cosR < (⟪z, x⟫ : ℝ)
    · have hgx : capCollapseMap z ω cosR x = ω := Set.piecewise_eq_of_mem _ _ _ hxS
      rw [hgx]; exact le_max_left _ _
    · have hgx : capCollapseMap z ω cosR x = x := Set.piecewise_eq_of_notMem _ _ _ hxS
      rw [hgx, norm_eq_one_of_mem_sphere hx]; exact le_max_right _ _
  -- barycenter = ∫ g dμ (change of variables), then split over the cap and its complement
  have hcov : barycenter (μ.map (capCollapseMap z ω cosR))
      = ∫ x, capCollapseMap z ω cosR x ∂μ := by
    rw [barycenter]
    exact integral_map hgmeas.aemeasurable aestronglyMeasurable_id
  rw [hcov, ← integral_add_compl hSM hgInt]
  congr 1
  · have hcap : ∫ x in S, capCollapseMap z ω cosR x ∂μ = ∫ _ in S, ω ∂μ :=
      setIntegral_congr_fun hSM (fun x hx => Set.piecewise_eq_of_mem _ _ _ hx)
    rw [hcap, setIntegral_const, measureReal_def]
  · exact setIntegral_congr_fun hSM.compl (fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx)

end MeasureToMeasure
