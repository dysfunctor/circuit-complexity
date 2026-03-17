import Circ.ACNF.Defs
import Circ.Internal.ACNF

/-! # Alternating Normal Form

This module provides the alternating normal form tree type and normalization results.

## Definitions (from `Circ.ACNF.Defs`)

* `ACNF` — inductive tree: `lit`, `and`, or `or`
* `ACNF.eval` — evaluate on a `BitString N`
* `ACNF.depth` — longest root-to-leaf path length
* `ACNF.size` — number of internal (AND/OR) nodes
* `ACNF.leafCount` — number of literal leaves
* `ACNF.rootOp` — the operation at the root (`none` for literals)
* `ACNF.isAlternating` — no same-op parent-child pairs
* `ACNF.normalize` — collapse consecutive same-op gates
* `CNF.toACNF` / `DNF.toACNF` — embed 2-level normal forms
* `Circuit.wireToACNF` — convert a circuit wire to ACNF with polarity
* `Circuit.toACNF` — convert a single-output unbounded AND/OR circuit to ACNF
* `Circuit.maxFanIn` — maximum fan-in across all gates

## Main results (from `Circ.Internal.ACNF`)

* `ACNF.normalize_eval` — normalization preserves evaluation
* `ACNF.normalize_depth_le` — normalization does not increase depth
* `ACNF.normalize_isAlternating` — normalization produces alternating trees
* `CNF.toACNF_eval` — CNF to ACNF preserves evaluation
* `DNF.toACNF_eval` — DNF to ACNF preserves evaluation
* `Circuit.wireToACNF_eval` — wire-to-ACNF preserves evaluation (with polarity)
* `Circuit.toACNF_eval` — circuit-to-ACNF preserves evaluation
* `Circuit.toACNF_depth_le` — ACNF depth ≤ circuit depth
* `Circuit.toACNF_normalize_eval` — normalized ACNF preserves evaluation
* `Circuit.toACNF_normalize_depth_le` — normalized ACNF depth ≤ circuit depth
* `Circuit.toACNF_normalize_isAlternating` — normalized ACNF is alternating
* `Circuit.toACNF_leafCount_le` — ACNF leaf count ≤ maxFanIn ^ depth
-/
