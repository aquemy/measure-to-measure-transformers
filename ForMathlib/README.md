# ForMathlib -- Mathlib-ready staging

Kernel-clean, general-purpose leaves shaped so they *could* be upstreamed to Mathlib: minimal
imports (only Mathlib, never the project prelude), generic names, a namespace mirroring the theory
path, conformant style, passing linters. **Preparation only** -- nothing here has been contributed to
Mathlib; upstreaming is a human decision, not something the pipeline does on its own.

These are re-statements of project leaves, generalized away from the paper's concrete
`Eucl d = EuclideanSpace ℝ (Fin d)` / `sphere d` prelude to an arbitrary real inner product space,
and re-based on Mathlib's own vocabulary (e.g. the geodesic distance is bridged to
`InnerProductGeometry.angle` rather than shadowed). The kernel-checked originals live under
`MeasureToMeasure/`.

Readiness checklist (see the `lean-math:mathlib-ready` skill and its
`references/reusable-blueprints.md`):

- [x] `#print axioms` is `clean` (only `propext` / `Classical.choice` / `Quot.sound`)
- [x] Mathlib naming (snake_case term lemmas / UpperCamelCase types / lowerCamelCase data;
      conclusion-first `conclusion_of_hyp1_of_hyp2`) and a namespace mirroring the theory path
- [x] Builds on Mathlib definitions (bridge lemma if a bespoke def is unavoidable:
      `tangentialProjector_eq_starProjection` ties the projector to `Submodule.starProjection`)
- [x] Minimal imports; no project-prelude dependency
- [x] Apache-2.0 header + `Authors:` line; module + declaration docstrings
- [ ] Linters clean; lines <= 100 cols (lines checked locally; Mathlib's linter suite not yet run)

## Staged

All three files generalize to `{E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]` and are
`#print axioms`-clean.

| File / declaration | Statement | Imports | Readiness |
| --- | --- | --- | --- |
| `TangentialProjector.lean` -- `InnerProductGeometry.tangentialProjector` (+ `_apply`, `_add`, `_smul`, `_self_of_norm_eq_one`, `_symm`, `_idem_of_norm_eq_one`, `inner_tangentialProjector_self_eq_norm_sq_sub_inner_sq`, `tangentialProjector_eq_starProjection`) | The rank-one-complement projector `P_x v = v - ⟪x,v⟫•x` and its identities (linearity, annihilates a unit `x`, self-adjoint, idempotent, `⟪P_x v,v⟫ = ‖v‖²-⟪x,v⟫²`), bridged to Mathlib's `(ℝ ∙ x)ᗮ.starProjection` | `Mathlib.Analysis.InnerProductSpace.Basic`, `Mathlib.Analysis.InnerProductSpace.Projection.Basic` | ready; bridge lemma ties the closed form to the bundled `Submodule.starProjection` API |
| `UnitSphereGeodesic.lean` -- `InnerProductGeometry.{inner_le_one_of_norm_eq_one, neg_one_le_inner_of_norm_eq_one, angle_eq_arccos_inner_of_norm_eq_one, cos_angle_of_norm_eq_one}` | On the unit sphere the paper's `arccos⟪x,y⟫` **is** Mathlib's `InnerProductGeometry.angle`; plus the Cauchy-Schwarz bounds `⟪x,y⟫ ∈ [-1,1]` | `Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic` | ready; reuses `angle`, does not shadow it |
| `SeparatingHyperplane.lean` -- `InnerProductGeometry.inner_lt_cos_of_lt_angle` | `0 ≤ θ`, `θ < angle ω x` ⟹ `⟪ω,x⟫ < cos θ` for unit vectors (cosine strictly antitone on `[0,π]`); the paper-constant specialization (`θ = π/8 + τ`) lives in `MeasureToMeasure/Leaves/SeparatingHyperplane.lean` | `ForMathlib.UnitSphereGeodesic` | ready; constant-free threshold form |

## Candidates under evaluation (not staged)

- **Barycenter non-colinearity** (`MeasureToMeasure/Leaves/BarycenterNonColinear.lean`,
  `barycenter_noncolinear_of_disjoint_hull` and `..._general`). The finite/empirical core
  (conical spans + `SameRay`) generalizes cleanly, but it is more special-purpose than the spherical-
  geometry cluster above, and the general-measure half depends on Bochner integration
  (`Convex.integral_mem`). Left in-project pending a decision on whether the abstraction earns a place
  in Mathlib; not staged here, to avoid a scattered dump of paper-specific lemmas.
