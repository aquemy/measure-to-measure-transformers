import MeasureToMeasure.Foundations.GatedBlock
import MeasureToMeasure.Axioms.ContinuityEquation

/-!
# Leaf L2 (Lemma 3.4): a gated block fixes every point off its cap

The fixing clause of Lemma 3.4 (eq. (3.2), F17-repaired to an open carrier `U`) needs the linear
flow to be the identity away from where the two measures live. The gated perceptron field
`gatedField z ω cosR = gateFactor · P_x^⊥ ω` carries the ReLU gate `reluGate z cosR x = (⟪z,x⟫ - cosR)₊`,
which **vanishes off the cap** `{x | cos R < ⟪z,x⟫}`: where `⟪z,x⟫ ≤ cos R` the gate is `0`, so the
field is `0`, so (a single such block being `Parked` there) the flow fixes the point.

Choosing the cap inside the open carrier `U` (`{x | cos R < ⟪z,x⟫} ⊆ U`) then makes the flow the
identity on `U`ᶜ ⊇ (sphere ∖ U), which is exactly the fixing clause. The off-cap vanishing lemmas are
also the basic parking facts reused wherever a gated block must leave a region untouched.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- Off the cap the ReLU gate vanishes: `⟪z,x⟫ ≤ cos R ⇒ reluGate z cosR x = 0`. -/
theorem reluGate_eq_zero_of_inner_le {z : Eucl d} {cosR : ℝ} {x : Eucl d}
    (h : (⟪z, x⟫ : ℝ) ≤ cosR) : reluGate z cosR x = 0 := by
  unfold reluGate
  exact max_eq_left (by linarith)

/-- Off the cap the full gate scalar vanishes (`gateFactor = normCutoff · reluGate`). -/
theorem gateFactor_eq_zero_of_inner_le {z : Eucl d} {cosR : ℝ} {x : Eucl d}
    (h : (⟪z, x⟫ : ℝ) ≤ cosR) : gateFactor z cosR x = 0 := by
  rw [gateFactor, reluGate_eq_zero_of_inner_le h, mul_zero]

/-- Off the cap the gated field vanishes (`gatedField = gateFactor • P_x^⊥ ω`). -/
theorem gatedField_eq_zero_of_inner_le {z ω : Eucl d} {cosR : ℝ} {x : Eucl d}
    (h : (⟪z, x⟫ : ℝ) ≤ cosR) : gatedField z ω cosR x = 0 := by
  rw [gatedField, gateFactor_eq_zero_of_inner_le h, zero_smul]

/-- **L2 (fixing clause).** A single gated block fixes every point off its cap: where `⟪z,x⟫ ≤ cos R`
the field vanishes, so the block is `Parked` there and the flow leaves `x` invariant. With the cap
chosen inside an open carrier `U`, this delivers the F17-repaired fixing clause `flowMap = id` on
`U`ᶜ. -/
theorem flowMap_gatedBlock_id_of_inner_le {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) {x : Eucl d} (h : (⟪z, x⟫ : ℝ) ≤ cosR) :
    flowMap [gatedBlock hz hω hcosR hT] t x = x := by
  refine Axioms.flowMap_id_on_parked _ t (S := {y | (⟪z, y⟫ : ℝ) ≤ cosR}) ?_ h
  intro b hb y hy
  rw [List.mem_singleton] at hb
  subst hb
  exact gatedField_eq_zero_of_inner_le hy

end MeasureToMeasure
