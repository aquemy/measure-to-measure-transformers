import Regression.OldStatements

/-!
# F11: `lemma_5_1` without the disjoint-supports hypotheses is false

Two identical Dirac sources with two distinct Dirac targets are pairwise matchable (identity map,
constant map), but a single map `ψ` would have to send the shared atom to both targets at once.
Repaired in PR #64 (finding F11); the conclusion here is the current `Measurable ψ` form (the
historical `Function.Bijective ψ` was itself unsatisfiable, finding F13).
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure

/-- The two target points `0` and `e₀` of `ℝ¹`. -/
noncomputable def p0 : Eucl 1 := 0

/-- See `p0`. -/
noncomputable def p1 : Eucl 1 := EuclideanSpace.single 0 (1 : ℝ)

/-- The two chosen points are distinct (their first coordinates differ). -/
theorem p0_ne_p1 : p0 ≠ p1 := by
  intro h
  have h0 := congrFun (congrArg (fun x : Eucl 1 => (x : Fin 1 → ℝ)) h) 0
  simp [p0, p1] at h0

/-- F11: `lemma_5_1` without disjoint supports is false -- the shared-atom counterexample. -/
theorem oldLemma51_false (ax : Regression.OldLemma51Sig) : False := by
  have hmatch : ∀ i : Fin 2,
      ∃ Ti : Eucl 1 → Eucl 1,
        ((fun _ : Fin 2 => Measure.dirac p0) i).map Ti = (![Measure.dirac p0,
          Measure.dirac p1]) i := by
    intro i
    fin_cases i
    · exact ⟨id, by simp⟩
    · refine ⟨fun _ => p1, ?_⟩
      simp
  obtain ⟨ψ, _hψm, hψ⟩ := ax (fun _ : Fin 2 => Measure.dirac p0)
    (![Measure.dirac p0, Measure.dirac p1]) hmatch
  have h0 := hψ 0
  have h1 := hψ 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  have hdd : (Measure.dirac p0 : Measure (Eucl 1)) = Measure.dirac p1 := h0.symm.trans h1
  have heval := congrArg (fun m : Measure (Eucl 1) => m {p1}) hdd
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Set.indicator_of_notMem (by simpa using p0_ne_p1),
    Set.indicator_of_mem (Set.mem_singleton _)] at heval
  simp at heval

end Regression.Refuted
