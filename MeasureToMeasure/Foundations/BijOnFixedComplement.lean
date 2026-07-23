import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Function

/-!
# A bijection fixing a complement maps the target set into itself

A generic, project-independent set-theory fact: if `f` is a bijection of `S` onto itself and `f`
fixes every point of `S \ U` (the "bystanders"), then `f` maps `U` into `U`. Equivalently, points
whose supports sit entirely outside `U` never wander into `U` under `f`, so `f` cannot "smuggle" a
point of `U` out of `U` by routing it through the fixed complement and back.

This is the set-theoretic core needed for `disentangle_insert_colinear`: a permutation of the full
point family that fixes every bystander (point outside the region of interest `U`) must send the
region `U` back into itself, not scatter its points among the bystanders.
-/

namespace Set

/-- If `f` is a bijection of `S` onto itself and `f` fixes every point of `S \ U` pointwise, then
`f` maps `U` into `U`. -/
theorem BijOn.mapsTo_of_eqOn_compl {α : Type*} {f : α → α} {S U : Set α}
    (hf : Set.BijOn f S S) (hfix : Set.EqOn f id (S \ U)) (hUS : U ⊆ S) :
    Set.MapsTo f U U := by
  intro x hxU
  by_contra hxnU
  have hxS := hUS hxU
  have hfxS := hf.mapsTo hxS
  have hfxSU : f x ∈ S \ U := ⟨hfxS, hxnU⟩
  have hfeq : f (f x) = f x := hfix hfxSU
  have hxeq : f x = x := hf.injOn hfxS hxS hfeq
  rw [hxeq] at hfxSU
  exact hfxSU.2 hxU

end Set
