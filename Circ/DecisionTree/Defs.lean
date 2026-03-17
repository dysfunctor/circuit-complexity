import Circ.NF.Defs

/-! # Decision Trees — Core Definitions

This module defines binary decision trees over `N` Boolean variables,
together with their evaluation semantics, depth measure, and
conversions to CNF/DNF normal forms.

## Main definitions

* `DecisionTree` — inductive type: `leaf` or `query`
* `DecisionTree.eval` — evaluate on a `BitString N`
* `DecisionTree.depth` — maximum root-to-leaf path length
* `DecisionTree.toDNF` — collect root-to-true-leaf paths as DNF terms
* `DecisionTree.toCNF` — collect root-to-false-leaf paths (negated) as CNF clauses
-/

/-- A binary decision tree over `N` Boolean variables.

A `leaf` returns a fixed value. A `query` reads variable `var` and
branches to `ifFalse` (when `x var = false`) or `ifTrue` (when `x var = true`). -/
inductive DecisionTree (N : Nat) where
  | leaf (val : Bool) : DecisionTree N
  | query (var : Fin N) (ifFalse ifTrue : DecisionTree N) : DecisionTree N
  deriving Repr

namespace DecisionTree

variable {N : Nat}

/-- Evaluate a decision tree on a bit assignment. -/
def eval : DecisionTree N → BitString N → Bool
  | .leaf val, _ => val
  | .query var ifFalse ifTrue, x =>
    if x var then ifTrue.eval x else ifFalse.eval x

/-- The depth of a decision tree: the length of the longest root-to-leaf path. -/
def depth : DecisionTree N → Nat
  | .leaf _ => 0
  | .query _ ifFalse ifTrue => 1 + max ifFalse.depth ifTrue.depth

/-- Collect all root-to-true-leaf paths as DNF terms.

Each path records the literals encountered: querying variable `i` with
branch `true` contributes positive literal `⟨i, true⟩`, and branch `false`
contributes negative literal `⟨i, false⟩`. -/
def toDNF : DecisionTree N → DNF N
  | .leaf true => ⟨[[]]⟩  -- one empty term (tautologically true)
  | .leaf false => ⟨[]⟩    -- no terms (tautologically false)
  | .query var ifFalse ifTrue =>
    let trueTerms := ifTrue.toDNF.terms.map (fun term => ⟨var, true⟩ :: term)
    let falseTerms := ifFalse.toDNF.terms.map (fun term => ⟨var, false⟩ :: term)
    ⟨falseTerms ++ trueTerms⟩

/-- Collect all root-to-false-leaf paths (negated) as CNF clauses.

Each path to a `false` leaf gives a clause: if the path queries variable `i`
going right (true branch), we add negative literal `⟨i, false⟩` to the clause
(the opposite polarity), so the clause is falsified exactly on that path. -/
def toCNF : DecisionTree N → CNF N
  | .leaf false => ⟨[[]]⟩  -- one empty clause (tautologically false)
  | .leaf true => ⟨[]⟩     -- no clauses (tautologically true)
  | .query var ifFalse ifTrue =>
    let trueClauses := ifTrue.toCNF.clauses.map (fun cl => ⟨var, false⟩ :: cl)
    let falseClauses := ifFalse.toCNF.clauses.map (fun cl => ⟨var, true⟩ :: cl)
    ⟨falseClauses ++ trueClauses⟩

end DecisionTree
