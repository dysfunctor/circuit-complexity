import Circ.Restriction.Defs
import Circ.Internal.Restriction

/-! # Restrictions on Boolean Formulas

A `Restriction N` is a partial assignment of Boolean variables: each of the
`N` variables is either fixed to a specific Boolean value or left free.
Applying a restriction to a CNF or DNF formula simplifies it by resolving
fixed literals and dropping trivially satisfied/falsified clauses/terms.

## Definitions (from `Circ.Restriction.Defs`)

* `Restriction` — partial assignment: `assign : Fin N → Option Bool`
* `Restriction.freeVars` / `numFree` — free variable set and count
* `Restriction.applyCNF` / `applyDNF` — simplify formulas under a restriction
* `CNF.width` / `DNF.width` — maximum clause/term size
* `CNF.isKCNF` / `DNF.isKDNF` — bounded-width predicates

## Main results (from `Circ.Internal.Restriction`)

* `Restriction.applyCNF_eval` — restriction preserves CNF evaluation on consistent assignments
* `Restriction.applyDNF_eval` — restriction preserves DNF evaluation on consistent assignments
* `Restriction.applyCNF_isKCNF` — restriction preserves k-CNF property
* `Restriction.applyDNF_isKDNF` — restriction preserves k-DNF property
-/
