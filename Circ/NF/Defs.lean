import Circ.Basic
import Circ.AON.Defs

/-! # Normal Forms — Core Definitions

This module defines Conjunctive Normal Form (CNF) and Disjunctive Normal Form (DNF)
Boolean formulas over `N` variables, together with their evaluation semantics,
complexity measures, and De Morgan negation duality.

## Main definitions

* `Literal` — a Boolean variable with a polarity flag (positive or negative)
* `CNF` — a conjunction of clauses (each clause is a disjunction of literals)
* `DNF` — a disjunction of terms (each term is a conjunction of literals)
* `CNF.complexity` — the number of clauses in a CNF formula
* `DNF.complexity` — the number of terms in a DNF formula
* `CNF.neg` / `DNF.neg` — De Morgan negation (CNF ↔ DNF)
-/

/-- A literal: a Boolean variable (by index) together with a polarity flag.

`polarity = true` represents the positive literal xᵢ;
`polarity = false` represents the negative literal ¬xᵢ. -/
structure Literal (N : Nat) where
  var : Fin N
  /-- `true` = positive literal (xᵢ); `false` = negative literal (¬xᵢ). -/
  polarity : Bool
  deriving DecidableEq, Repr

/-- Evaluate a literal on a bit assignment. -/
def Literal.eval (l : Literal N) (x : BitString N) : Bool :=
  if l.polarity then x l.var else !x l.var

/-- Negate a literal by flipping its polarity. -/
def Literal.neg (l : Literal N) : Literal N :=
  { l with polarity := !l.polarity }

/-- Negating a literal negates its evaluation. -/
theorem Literal.eval_neg (l : Literal N) (x : BitString N) :
    l.neg.eval x = !(l.eval x) := by
  simp [Literal.neg, Literal.eval]
  cases l.polarity <;> simp

/-! ## CNF -/

/--
A CNF (Conjunctive Normal Form) formula over `N` Boolean variables.

A CNF is a conjunction of clauses, where each clause is a disjunction of literals.
-/
structure CNF (N : Nat) where
  /-- The clauses of the formula. Each clause is a list of literals. -/
  clauses : List (List (Literal N))
  deriving Repr

namespace CNF

/-- A CNF formula evaluates to `true` iff every clause contains at least one
satisfied literal. -/
def eval (φ : CNF N) (x : BitString N) : Bool :=
  φ.clauses.all fun clause => clause.any fun l => l.eval x

/-- The complexity of a CNF formula is its number of clauses. -/
def complexity (φ : CNF N) : Nat := φ.clauses.length

end CNF

/-! ## DNF -/

/--
A DNF (Disjunctive Normal Form) formula over `N` Boolean variables.

A DNF is a disjunction of terms, where each term is a conjunction of literals.
-/
structure DNF (N : Nat) where
  /-- The terms of the formula. Each term is a list of literals. -/
  terms : List (List (Literal N))
  deriving Repr

namespace DNF

/-- A DNF formula evaluates to `true` iff at least one term has all its
literals satisfied. -/
def eval (φ : DNF N) (x : BitString N) : Bool :=
  φ.terms.any fun term => term.all fun l => l.eval x

/-- The complexity of a DNF formula is its number of terms. -/
def complexity (φ : DNF N) : Nat := φ.terms.length

end DNF

/-! ## De Morgan Negation Duality -/

/-- Negate a CNF formula by flipping all literal polarities, producing a DNF.
By De Morgan's laws, `¬(∧ᵢ ∨ⱼ lᵢⱼ) = ∨ᵢ ∧ⱼ ¬lᵢⱼ`. -/
def CNF.neg (φ : CNF N) : DNF N :=
  ⟨φ.clauses.map (fun clause => clause.map Literal.neg)⟩

/-- Negate a DNF formula by flipping all literal polarities, producing a CNF.
By De Morgan's laws, `¬(∨ᵢ ∧ⱼ lᵢⱼ) = ∧ᵢ ∨ⱼ ¬lᵢⱼ`. -/
def DNF.neg (φ : DNF N) : CNF N :=
  ⟨φ.terms.map (fun term => term.map Literal.neg)⟩

/-- Negating a CNF formula negates its evaluation (De Morgan duality). -/
theorem CNF.eval_neg (φ : CNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [CNF.neg, DNF.eval, CNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]

/-- Negating a DNF formula negates its evaluation (De Morgan duality). -/
theorem DNF.eval_neg (φ : DNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [DNF.neg, CNF.eval, DNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]

/-- Negating a CNF preserves complexity. -/
theorem CNF.neg_complexity (φ : CNF N) : φ.neg.complexity = φ.complexity := by
  simp [CNF.neg, DNF.complexity, CNF.complexity, List.length_map]

/-! ## Alternating Normal Form

Alternating normal form trees with AND/OR layers and literal leaves,
used in the Håstad switching lemma proof for AC0 lower bounds on parity.

`ACNFTree` is the raw (possibly non-alternating) tree. The public `ACNF`
type wraps it with a proof of the alternating condition. -/

/-- A raw AND/OR/literal tree over `N` Boolean variables.

Layer 0 consists of literals (variable with polarity).
Internal nodes are AND or OR gates with a list of children.
This tree may or may not satisfy the alternating condition; use `ACNF`
for the guaranteed-alternating wrapper. -/
inductive ACNFTree (N : Nat) where
  | lit (l : Literal N)
  | and (children : List (ACNFTree N))
  | or (children : List (ACNFTree N))
  deriving Repr

namespace ACNFTree

variable {N : Nat}

/-! ## Evaluation -/

/-- Evaluate an AND/OR tree on a bit assignment.

AND = conjunction of children (empty AND = `true`).
OR = disjunction of children (empty OR = `false`). -/
def eval : ACNFTree N → BitString N → Bool
  | .lit l, x => l.eval x
  | .and children, x => evalAll children x
  | .or children, x => evalAny children x
where
  /-- Evaluate a list of children under AND (all must be true). -/
  evalAll : List (ACNFTree N) → BitString N → Bool
    | [], _ => true
    | c :: cs, x => c.eval x && evalAll cs x
  /-- Evaluate a list of children under OR (at least one must be true). -/
  evalAny : List (ACNFTree N) → BitString N → Bool
    | [], _ => false
    | c :: cs, x => c.eval x || evalAny cs x

/-! ## Depth -/

/-- The depth of an ACNFTree tree: longest root-to-leaf path.

Literals have depth 0. An AND/OR node has depth 1 + max of children depths. -/
def depth : ACNFTree N → Nat
  | .lit _ => 0
  | .and children => 1 + depthList children
  | .or children => 1 + depthList children
where
  /-- Maximum depth across a list of children. -/
  depthList : List (ACNFTree N) → Nat
    | [] => 0
    | c :: cs => max c.depth (depthList cs)

/-! ## Size -/

/-- The number of internal (AND/OR) nodes in an ACNFTree tree.

Literals contribute 0. Each AND/OR node contributes 1 plus the sizes of its children. -/
def size : ACNFTree N → Nat
  | .lit _ => 0
  | .and children => 1 + sizeList children
  | .or children => 1 + sizeList children
where
  /-- Sum of sizes across a list of children. -/
  sizeList : List (ACNFTree N) → Nat
    | [] => 0
    | c :: cs => c.size + sizeList cs

/-! ## Leaf count -/

/-- The number of literal leaves in an ACNFTree tree.

Used for the polynomial size bound in the circuit-to-ACNFTree conversion. -/
def leafCount : ACNFTree N → Nat
  | .lit _ => 1
  | .and children => leafCountList children
  | .or children => leafCountList children
where
  /-- Sum of leaf counts across a list of children. -/
  leafCountList : List (ACNFTree N) → Nat
    | [] => 0
    | c :: cs => c.leafCount + leafCountList cs

/-! ## Root operation -/

/-- The operation at the root of an ACNFTree tree, or `none` for a literal. -/
def rootOp : ACNFTree N → Option AONOp
  | .lit _ => none
  | .and _ => some .and
  | .or _ => some .or

/-! ## Alternating check -/

/-- An ACNFTree tree is alternating if no AND node has an AND child and
no OR node has an OR child (recursively).

Literals are always alternating. -/
def isAlternating : ACNFTree N → Bool
  | .lit _ => true
  | .and children => isAlternatingAndList children
  | .or children => isAlternatingOrList children
where
  /-- Check all children are alternating and none is an AND node (for AND parent). -/
  isAlternatingAndList : List (ACNFTree N) → Bool
    | [] => true
    | c :: cs => (c.rootOp != some AONOp.and && c.isAlternating) && isAlternatingAndList cs
  /-- Check all children are alternating and none is an OR node (for OR parent). -/
  isAlternatingOrList : List (ACNFTree N) → Bool
    | [] => true
    | c :: cs => (c.rootOp != some AONOp.or && c.isAlternating) && isAlternatingOrList cs

/-! ## Normalization -/

/-- Normalize a tree by collapsing consecutive same-op gates bottom-up.

For example, `AND(a, AND(b, c), d)` becomes `AND(a, b, c, d)`.
Children are normalized first (recursively), then same-op children are
flattened into the parent's child list. -/
def normalize : ACNFTree N → ACNFTree N
  | .lit l => .lit l
  | .and children =>
    .and (normalizeAndFlatten children)
  | .or children =>
    .or (normalizeOrFlatten children)
where
  /-- Normalize children and flatten any AND children into the parent AND. -/
  normalizeAndFlatten : List (ACNFTree N) → List (ACNFTree N)
    | [] => []
    | c :: cs =>
      match c.normalize with
      | .and grandchildren => grandchildren ++ normalizeAndFlatten cs
      | other => other :: normalizeAndFlatten cs
  /-- Normalize children and flatten any OR children into the parent OR. -/
  normalizeOrFlatten : List (ACNFTree N) → List (ACNFTree N)
    | [] => []
    | c :: cs =>
      match c.normalize with
      | .or grandchildren => grandchildren ++ normalizeOrFlatten cs
      | other => other :: normalizeOrFlatten cs

/-! ## Conversion from CNF/DNF -/

end ACNFTree

/-- Convert a CNF formula to a raw AND/OR tree.

A CNF `∧ᵢ (∨ⱼ lᵢⱼ)` becomes `AND [OR [lit lᵢⱼ, ...], ...]`. -/
def CNF.toACNFTree (φ : CNF N) : ACNFTree N :=
  .and (φ.clauses.map fun clause =>
    .or (clause.map fun l => .lit l))

/-- Convert a DNF formula to a raw AND/OR tree.

A DNF `∨ᵢ (∧ⱼ lᵢⱼ)` becomes `OR [AND [lit lᵢⱼ, ...], ...]`. -/
def DNF.toACNFTree (φ : DNF N) : ACNFTree N :=
  .or (φ.terms.map fun term =>
    .and (term.map fun l => .lit l))

/-! ## ACNF: Alternating Circuit Normal Form -/

/-- An alternating normal form tree, indexed by a `Bool` tracking the root gate type.

`ACNF N true` is an AND-rooted (or literal) tree; `ACNF N false` is OR-rooted
(or literal). Children of an AND node must be OR-rooted or literal, and vice versa.
This alternation invariant is enforced by construction: an AND node contains
`List (ACNF N false)` children, ensuring each child is OR-rooted or a literal.

Use `CNF.toACNF` / `DNF.toACNF` for direct construction from normal forms, or
`Circuit.toACNF` (via normalization) for general circuits. -/
inductive ACNF (N : Nat) : Bool → Type where
  /-- A literal leaf. Can appear at any polarity index. -/
  | lit : Literal N → ACNF N isAnd
  /-- An AND gate whose children are OR-rooted or literal. -/
  | and : List (ACNF N false) → ACNF N true
  /-- An OR gate whose children are AND-rooted or literal. -/
  | or  : List (ACNF N true) → ACNF N false

namespace ACNF

variable {N : Nat}

/-- Evaluate an ACNF tree on a bit assignment.

AND = conjunction of children (empty AND = `true`).
OR = disjunction of children (empty OR = `false`). -/
def eval : ACNF N b → BitString N → Bool
  | .lit l, x => l.eval x
  | .and children, x => evalAll children x
  | .or children, x => evalAny children x
where
  /-- Evaluate a list of children under AND (all must be true). -/
  evalAll : List (ACNF N false) → BitString N → Bool
    | [], _ => true
    | c :: cs, x => c.eval x && evalAll cs x
  /-- Evaluate a list of children under OR (at least one must be true). -/
  evalAny : List (ACNF N true) → BitString N → Bool
    | [], _ => false
    | c :: cs, x => c.eval x || evalAny cs x

/-- The depth of an ACNF tree: longest root-to-leaf path.

Literals have depth 0. An AND/OR node has depth 1 + max of children depths. -/
def depth : ACNF N b → Nat
  | .lit _ => 0
  | .and children => 1 + depthAll children
  | .or children => 1 + depthAny children
where
  /-- Maximum depth across AND children. -/
  depthAll : List (ACNF N false) → Nat
    | [] => 0
    | c :: cs => max c.depth (depthAll cs)
  /-- Maximum depth across OR children. -/
  depthAny : List (ACNF N true) → Nat
    | [] => 0
    | c :: cs => max c.depth (depthAny cs)

/-- The number of internal (AND/OR) nodes. -/
def size : ACNF N b → Nat
  | .lit _ => 0
  | .and children => 1 + sizeAll children
  | .or children => 1 + sizeAny children
where
  /-- Sum of sizes across AND children. -/
  sizeAll : List (ACNF N false) → Nat
    | [] => 0
    | c :: cs => c.size + sizeAll cs
  /-- Sum of sizes across OR children. -/
  sizeAny : List (ACNF N true) → Nat
    | [] => 0
    | c :: cs => c.size + sizeAny cs

/-- The number of literal leaves. -/
def leafCount : ACNF N b → Nat
  | .lit _ => 1
  | .and children => leafCountAll children
  | .or children => leafCountAny children
where
  /-- Sum of leaf counts across AND children. -/
  leafCountAll : List (ACNF N false) → Nat
    | [] => 0
    | c :: cs => c.leafCount + leafCountAll cs
  /-- Sum of leaf counts across OR children. -/
  leafCountAny : List (ACNF N true) → Nat
    | [] => 0
    | c :: cs => c.leafCount + leafCountAny cs

end ACNF

/-! ## Direct construction from CNF/DNF -/

/-- Convert a CNF formula directly to an AND-rooted ACNF tree.

A CNF `∧ᵢ (∨ⱼ lᵢⱼ)` becomes `AND [OR [lit lᵢⱼ, ...], ...]`. -/
def CNF.toACNF (φ : CNF N) : ACNF N true :=
  .and (φ.clauses.map fun clause =>
    .or (clause.map fun l => .lit l))

/-- Convert a DNF formula directly to an OR-rooted ACNF tree.

A DNF `∨ᵢ (∧ⱼ lᵢⱼ)` becomes `OR [AND [lit lᵢⱼ, ...], ...]`. -/
def DNF.toACNF (φ : DNF N) : ACNF N false :=
  .or (φ.terms.map fun term =>
    .and (term.map fun l => .lit l))
