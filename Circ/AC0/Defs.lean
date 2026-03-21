import Circ.NF.Defs
import Circ.AON.Defs
import Circ.Internal.ACNFTree

/-! # AC0 — Core Definitions

This module defines the AC0 circuit complexity class.

## Main definitions

* `InAC0` — predicate: the family is in AC0 (constant depth, polynomial size,
  unbounded fan-in AND/OR)

## Re-exported from imports

* `BoolFunFamily` (from `Circ.Basic`) — a family of Boolean functions indexed by input length
* `InAC0NFTree` (from `Circ.Internal.ACNFTree`) — predicate: the family is computed by
  constant-depth, polynomial-leaf-count ACNF trees
-/

/-- A Boolean function family is in **AC0** if there exist constants `d`
(depth bound) and `c` (size exponent) such that for every input length
`N ≥ 1`, some unbounded-fan-in AND/OR circuit of depth at most `d` and
size at most `N ^ c` computes `f N`.

This captures the standard definition of AC0:
- **Constant depth**: the circuit depth does not grow with `N`.
- **Polynomial size**: the number of gates is bounded by a polynomial in `N`.
- **Unbounded fan-in**: AND and OR gates may have arbitrarily many inputs.
- **Free negation**: each gate input carries a negation flag (standard in
  circuit complexity). -/
def InAC0 (f : BoolFunFamily) : Prop :=
  ∃ (d c : Nat), ∀ (N : Nat) [NeZero N],
    ∃ (G : Nat) (circ : Circuit Basis.unboundedAON N 1 G),
      circ.depth ≤ d ∧ circ.size ≤ N ^ c ∧
      (fun x => (circ.eval x) 0) = f N
