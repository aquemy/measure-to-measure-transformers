import MeasureToMeasure.Foundations.FlowMap

/-!
# Leaf (Lemma 3.4 Part 1, Path I assembly): stacking identical blocks lengthens the flow time

`flowMap θ t` runs **every** block of `θ` for the *same* duration `t` (`flowMap_cons`), and a single
block's point flow is an additive one-parameter group (`Block.blockFlow_add`). So `n` stacked copies
of one block `b`, each run for `t`, compose to `b` run for `n · t`:

  `flowMap (List.replicate n b) t = b.blockFlow (n · t)`.

This is exactly the device that lets a **fixed** flow time `t` realise an **arbitrarily long**
effective reach: the paper's App. B.3 collapse ("take `T` large enough") is recovered, at the fixed
`T` the theorem `lemma_3_4_part1` hands us, by stacking enough identical gated blocks. Equivalently
`flowMap (List.replicate n b) t = flowMap [b] (n · t)`.
-/

namespace MeasureToMeasure

variable {d : ℕ}

/-- **Block stacking = time scaling.** `n` copies of a block `b`, each flowed for `t`, compose to `b`
flowed for `n · t`. Proof: induction on `n` with the flow semigroup law `blockFlow_add`. -/
theorem flowMap_replicate (b : Block d) (n : ℕ) (t : ℝ) :
    flowMap (List.replicate n b) t = b.blockFlow ((n : ℝ) * t) := by
  induction n with
  | zero =>
    rw [List.replicate_zero, flowMap_nil, Nat.cast_zero, zero_mul, Block.blockFlow_zero_eq_id]
  | succ k ih =>
    rw [List.replicate_succ, flowMap_cons, ih]
    funext x
    show b.blockFlow ((k : ℝ) * t) (b.blockFlow t x) = b.blockFlow (((k + 1 : ℕ) : ℝ) * t) x
    rw [Block.blockFlow_add]
    congr 1
    push_cast; ring

/-- The stacked schedule equals a single block flowed for `n · t` (the `[b]` form used to reuse the
single-block collapse estimates at the lengthened time). -/
theorem flowMap_replicate_eq_singleton (b : Block d) (n : ℕ) (t : ℝ) :
    flowMap (List.replicate n b) t = flowMap [b] ((n : ℝ) * t) := by
  rw [flowMap_replicate, flowMap_cons, flowMap_nil, Function.id_comp]

end MeasureToMeasure
