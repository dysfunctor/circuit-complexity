import Circ.NF.Defs
import Circ.AON.Defs

/-! # Alternating Normal Form — Core Definitions

This module defines alternating normal form trees (alternating AND/OR layers with
literal leaves), used in the Håstad switching lemma proof for AC0 lower bounds on parity.

## Main definitions

* `ACNF` — inductive tree: `lit`, `and`, or `or`
* `ACNF.eval` — evaluate on a `BitString N`
* `ACNF.depth` — longest root-to-leaf path length
* `ACNF.size` — number of internal (non-literal) nodes
* `ACNF.rootOp` — the operation at the root (`none` for literals)
* `ACNF.isAlternating` — no same-op parent-child pairs
* `ACNF.normalize` — collapse consecutive same-op gates
* `CNF.toACNF` / `DNF.toACNF` — embed 2-level normal forms
-/

/-- An alternating normal form tree over `N` Boolean variables.

Layer 0 consists of literals (variable with polarity).
Internal nodes are AND or OR gates with a list of children.
This is a tree (fan-out 1): each subtree appears under exactly one parent. -/
inductive ACNF (N : Nat) where
  | lit (l : Literal N)
  | and (children : List (ACNF N))
  | or (children : List (ACNF N))
  deriving Repr

namespace ACNF

variable {N : Nat}

/-! ## Evaluation -/

/-- Evaluate an ACNF tree on a bit assignment.

AND = conjunction of children (empty AND = `true`).
OR = disjunction of children (empty OR = `false`). -/
def eval : ACNF N → BitString N → Bool
  | .lit l, x => l.eval x
  | .and children, x => evalAll children x
  | .or children, x => evalAny children x
where
  /-- Evaluate a list of children under AND (all must be true). -/
  evalAll : List (ACNF N) → BitString N → Bool
    | [], _ => true
    | c :: cs, x => c.eval x && evalAll cs x
  /-- Evaluate a list of children under OR (at least one must be true). -/
  evalAny : List (ACNF N) → BitString N → Bool
    | [], _ => false
    | c :: cs, x => c.eval x || evalAny cs x

/-! ## Depth -/

/-- The depth of an ACNF tree: longest root-to-leaf path.

Literals have depth 0. An AND/OR node has depth 1 + max of children depths. -/
def depth : ACNF N → Nat
  | .lit _ => 0
  | .and children => 1 + depthList children
  | .or children => 1 + depthList children
where
  /-- Maximum depth across a list of children. -/
  depthList : List (ACNF N) → Nat
    | [] => 0
    | c :: cs => max c.depth (depthList cs)

/-! ## Size -/

/-- The number of internal (AND/OR) nodes in an ACNF tree.

Literals contribute 0. Each AND/OR node contributes 1 plus the sizes of its children. -/
def size : ACNF N → Nat
  | .lit _ => 0
  | .and children => 1 + sizeList children
  | .or children => 1 + sizeList children
where
  /-- Sum of sizes across a list of children. -/
  sizeList : List (ACNF N) → Nat
    | [] => 0
    | c :: cs => c.size + sizeList cs

/-! ## Root operation -/

/-- The operation at the root of an ACNF tree, or `none` for a literal. -/
def rootOp : ACNF N → Option AONOp
  | .lit _ => none
  | .and _ => some .and
  | .or _ => some .or

/-! ## Alternating check -/

/-- An ACNF tree is alternating if no AND node has an AND child and
no OR node has an OR child (recursively).

Literals are always alternating. -/
def isAlternating : ACNF N → Bool
  | .lit _ => true
  | .and children => isAlternatingAndList children
  | .or children => isAlternatingOrList children
where
  /-- Check all children are alternating and none is an AND node (for AND parent). -/
  isAlternatingAndList : List (ACNF N) → Bool
    | [] => true
    | c :: cs => (c.rootOp != some AONOp.and && c.isAlternating) && isAlternatingAndList cs
  /-- Check all children are alternating and none is an OR node (for OR parent). -/
  isAlternatingOrList : List (ACNF N) → Bool
    | [] => true
    | c :: cs => (c.rootOp != some AONOp.or && c.isAlternating) && isAlternatingOrList cs

/-! ## Normalization -/

/-- Normalize an ACNF tree by collapsing consecutive same-op gates bottom-up.

For example, `AND(a, AND(b, c), d)` becomes `AND(a, b, c, d)`.
Children are normalized first (recursively), then same-op children are
flattened into the parent's child list. -/
def normalize : ACNF N → ACNF N
  | .lit l => .lit l
  | .and children =>
    .and (normalizeAndFlatten children)
  | .or children =>
    .or (normalizeOrFlatten children)
where
  /-- Normalize children and flatten any AND children into the parent AND. -/
  normalizeAndFlatten : List (ACNF N) → List (ACNF N)
    | [] => []
    | c :: cs =>
      match c.normalize with
      | .and grandchildren => grandchildren ++ normalizeAndFlatten cs
      | other => other :: normalizeAndFlatten cs
  /-- Normalize children and flatten any OR children into the parent OR. -/
  normalizeOrFlatten : List (ACNF N) → List (ACNF N)
    | [] => []
    | c :: cs =>
      match c.normalize with
      | .or grandchildren => grandchildren ++ normalizeOrFlatten cs
      | other => other :: normalizeOrFlatten cs

/-! ## Conversion from CNF/DNF -/

end ACNF

/-- Convert a CNF formula to an ACNF tree.

A CNF `∧ᵢ (∨ⱼ lᵢⱼ)` becomes `AND [OR [lit lᵢⱼ, ...], ...]`. -/
def CNF.toACNF (φ : CNF N) : ACNF N :=
  .and (φ.clauses.map fun clause =>
    .or (clause.map fun l => .lit l))

/-- Convert a DNF formula to an ACNF tree.

A DNF `∨ᵢ (∧ⱼ lᵢⱼ)` becomes `OR [AND [lit lᵢⱼ, ...], ...]`. -/
def DNF.toACNF (φ : DNF N) : ACNF N :=
  .or (φ.terms.map fun term =>
    .and (term.map fun l => .lit l))
