import Circ.AC0.Defs
import Circ.Internal.AC0
import Circ.XOR

/-! # AC0 — The AC0 Complexity Class

This module re-exports the AC0 definitions and main results.

## Definitions (from `Circ.AC0.Defs`)

* `BoolFunFamily` — a family of Boolean functions indexed by input length
* `InAC0` — predicate: the family is in AC0 (constant depth, polynomial size,
  unbounded fan-in AND/OR)
* `InAC0NF` — predicate: the family is computed by constant-depth,
  polynomial-leaf-count ACNF trees

## Main results (from `Circ.Internal.AC0`)

* `Gate.dedup` / `Circuit.dedup` — gate and circuit deduplication
* `Circuit.dedup_eval` — deduplication preserves evaluation
* `Circuit.dedup_depth_le` — depth does not increase after deduplication
* `Circuit.dedup_maxFanIn_le` — maxFanIn ≤ 2 * (N + G) after deduplication
* `InAC0_implies_InAC0NF` — every AC0 family is in AC0NF
* `not_InAC0NF_implies_not_InAC0` — contrapositive for lower bounds
* `parity_not_in_AC0` — the parity function is not in AC0
-/

/-- The parity (XOR) function family: the `N`-input XOR for each input length. -/
def parityFamily : BoolFunFamily := fun N => Schnorr.xorBool N

/-- **Parity is not in AC0** (Furst–Saxe–Sipser / Håstad).

The N-input XOR function cannot be computed by any constant-depth,
polynomial-size family of unbounded-fan-in AND/OR circuits. -/
theorem parity_not_in_AC0 : ¬InAC0 parityFamily := by
  sorry
