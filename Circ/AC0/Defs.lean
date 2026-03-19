import Circ.NF.Defs

/-! # AC0 — Core Definitions

This module defines the AC0 circuit complexity class and its alternating
normal form variant AC0NF.

## Main definitions

* `BoolFunFamily` — a family of Boolean functions indexed by input length
* `InAC0` — predicate: the family is in AC0 (constant depth, polynomial size,
  unbounded fan-in AND/OR)
* `InAC0NF` — predicate: the family is computed by constant-depth,
  polynomial-leaf-count ACNF trees
-/

/-- A family of Boolean functions indexed by input length `N`.

Each member maps `N`-bit strings to a single output bit. This is the standard
object of study in circuit complexity: we ask how the resources needed to
compute `f N` grow with `N`. -/
def BoolFunFamily := (N : Nat) → BitString N → Bool

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

/-- A Boolean function family is in **AC0NF** if there exist constants `d`
(depth bound) and `c` (leaf-count exponent) such that for every input length
`N ≥ 1`, some ACNF tree of depth at most `d` and leaf count at most `N ^ c`
computes `f N`.

This is the normal-form analogue of `InAC0`: every AC0 circuit can be unrolled
into an ACNF tree (via `Circuit.toACNF`) with depth preserved and leaf count
polynomial in the circuit size. Therefore `InAC0 f → InAC0NF f`, and lower
bounds proved against ACNF trees transfer to AC0. -/
def InAC0NF (f : BoolFunFamily) : Prop :=
  ∃ (d c : Nat), ∀ (N : Nat) [NeZero N],
    ∃ (b : Bool) (acnf : ACNF N b),
      acnf.depth ≤ d ∧ acnf.leafCount ≤ N ^ c ∧
      acnf.eval = f N
