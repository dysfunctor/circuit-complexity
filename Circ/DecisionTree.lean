import Circ.DecisionTree.Defs
import Circ.Internal.DecisionTree

/-! # Decision Trees

A `DecisionTree N` is a binary decision tree over `N` Boolean variables.
Each internal node queries a variable and branches; each leaf holds a
Boolean value.

## Definitions (from `Circ.DecisionTree.Defs`)

* `DecisionTree` — inductive type: `leaf` or `query`
* `DecisionTree.eval` — evaluate on a `BitString N`
* `DecisionTree.depth` — maximum root-to-leaf path length
* `DecisionTree.toDNF` / `toCNF` — convert to normal form

## Main results (from `Circ.Internal.DecisionTree`)

* `DecisionTree.eval_eq_toDNF_eval` — toDNF is semantically correct
* `DecisionTree.eval_eq_toCNF_eval` — toCNF is semantically correct
* `DecisionTree.toDNF_width_le_depth` — toDNF of depth-s tree is an s-DNF
* `DecisionTree.toCNF_width_le_depth` — toCNF of depth-s tree is an s-CNF
-/
