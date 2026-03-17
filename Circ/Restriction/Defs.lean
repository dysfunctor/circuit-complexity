import Circ.NF.Defs

/-! # Random Restriction Machinery — Core Definitions

This module defines restrictions (partial assignments) on Boolean variables
and operations for applying them to CNF/DNF formulas.

## Main definitions

* `Restriction` — partial assignment: each variable is either fixed to a Bool or left free
* `Restriction.freeVars` / `numFree` — the set and count of free (unassigned) variables
* `Restriction.applyLit` — resolve a literal under a restriction
* `Restriction.applyCNF` / `applyDNF` — simplify formulas under a restriction
* `CNF.width` / `DNF.width` — maximum clause/term size
* `CNF.isKCNF` / `DNF.isKDNF` — bounded-width predicates
-/

/-- A restriction (partial assignment) on `N` Boolean variables.

`assign i = none` means variable `i` is free (unassigned).
`assign i = some b` means variable `i` is fixed to `b`. -/
structure Restriction (N : Nat) where
  assign : Fin N → Option Bool
  deriving DecidableEq

namespace Restriction

variable {N : Nat}

/-- The set of free (unassigned) variables under this restriction. -/
def freeVars (ρ : Restriction N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ρ.assign i = none)

/-- The number of free variables under this restriction. -/
def numFree (ρ : Restriction N) : Nat :=
  ρ.freeVars.card

/-- The identity restriction: all variables are free. -/
def id : Restriction N where
  assign _ := none

/-- A total restriction: all variables are fixed according to a BitString. -/
def total (x : BitString N) : Restriction N where
  assign i := some (x i)

/-- An assignment `x` is consistent with restriction `ρ` if every fixed variable
agrees with `x`. -/
def Consistent (ρ : Restriction N) (x : BitString N) : Prop :=
  ∀ i : Fin N, ∀ b : Bool, ρ.assign i = some b → x i = b

/-- Resolve a literal under a restriction.

Returns `none` if the variable is free, or `some b` where `b` is the
truth value of the literal given the fixed assignment. -/
def applyLit (ρ : Restriction N) (l : Literal N) : Option Bool :=
  match ρ.assign l.var with
  | none => none
  | some b => some (if l.polarity then b else !b)

/-- Apply a restriction to a CNF clause (disjunction of literals).

If any literal resolves to `true`, the clause is trivially satisfied
and we return `none` (the clause can be dropped).
Otherwise, we return `some` of the surviving free literals. -/
def applyClause (ρ : Restriction N) (clause : List (Literal N)) :
    Option (List (Literal N)) :=
  if clause.any (fun l => ρ.applyLit l = some true) then
    none  -- clause is trivially true, drop it
  else
    some (clause.filter (fun l => ρ.applyLit l = none))

/-- Apply a restriction to a DNF term (conjunction of literals).

If any literal resolves to `false`, the term is trivially falsified
and we return `none` (the term can be dropped).
Otherwise, we return `some` of the surviving free literals. -/
def applyTerm (ρ : Restriction N) (term : List (Literal N)) :
    Option (List (Literal N)) :=
  if term.any (fun l => ρ.applyLit l = some false) then
    none  -- term is trivially false, drop it
  else
    some (term.filter (fun l => ρ.applyLit l = none))

/-- Apply a restriction to a CNF formula.

Drops trivially true clauses and removes resolved literals from
surviving clauses. -/
def applyCNF (ρ : Restriction N) (φ : CNF N) : CNF N :=
  ⟨φ.clauses.filterMap (ρ.applyClause)⟩

/-- Apply a restriction to a DNF formula.

Drops trivially false terms and removes resolved literals from
surviving terms. -/
def applyDNF (ρ : Restriction N) (φ : DNF N) : DNF N :=
  ⟨φ.terms.filterMap (ρ.applyTerm)⟩

end Restriction

/-! ## Width of CNF/DNF formulas -/

namespace CNF

/-- The width of a CNF formula: the maximum number of literals in any clause.
Returns 0 for an empty CNF. -/
def width (φ : CNF N) : Nat :=
  φ.clauses.foldl (fun acc clause => max acc clause.length) 0

/-- A CNF formula is k-CNF if every clause has at most `k` literals. -/
def isKCNF (φ : CNF N) (k : Nat) : Prop :=
  ∀ clause ∈ φ.clauses, clause.length ≤ k

instance : DecidablePred (CNF.isKCNF (N := N) · k) := by
  intro φ
  unfold isKCNF
  exact List.decidableBAll _ _

end CNF

namespace DNF

/-- The width of a DNF formula: the maximum number of literals in any term.
Returns 0 for an empty DNF. -/
def width (φ : DNF N) : Nat :=
  φ.terms.foldl (fun acc term => max acc term.length) 0

/-- A DNF formula is k-DNF if every term has at most `k` literals. -/
def isKDNF (φ : DNF N) (k : Nat) : Prop :=
  ∀ term ∈ φ.terms, term.length ≤ k

instance : DecidablePred (DNF.isKDNF (N := N) · k) := by
  intro φ
  unfold isKDNF
  exact List.decidableBAll _ _

end DNF
