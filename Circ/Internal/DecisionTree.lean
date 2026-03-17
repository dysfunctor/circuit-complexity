import Circ.DecisionTree.Defs
import Circ.Restriction.Defs

/-! # Internal: Decision Tree Conversion Correctness

This internal module proves that the `toDNF` and `toCNF` conversions on
decision trees are semantically correct and produce bounded-width formulas.

## Main results

* `DecisionTree.eval_eq_toDNF_eval` — `toDNF` preserves evaluation semantics.
* `DecisionTree.eval_eq_toCNF_eval` — `toCNF` preserves evaluation semantics.
* `DecisionTree.toDNF_width_le_depth` — terms of `toDNF` have at most `depth` literals.
* `DecisionTree.toCNF_width_le_depth` — clauses of `toCNF` have at most `depth` literals.
-/

/-! ## Helper lemmas -/

private lemma literal_eval_true (var : Fin N) (x : BitString N) :
    (Literal.mk var true).eval x = x var := by
  simp [Literal.eval]

private lemma literal_eval_false (var : Fin N) (x : BitString N) :
    (Literal.mk var false).eval x = !x var := by
  simp [Literal.eval]

namespace DecisionTree

variable {N : Nat}

/-- `toDNF` preserves evaluation: `t.toDNF.eval x = t.eval x`. -/
theorem eval_eq_toDNF_eval (t : DecisionTree N) (x : BitString N) :
    t.toDNF.eval x = t.eval x := by
  induction t with
  | leaf val => cases val <;> simp [toDNF, eval, DNF.eval]
  | query var ifFalse ifTrue ihF ihT =>
    simp only [toDNF, eval, DNF.eval]
    rw [List.any_append, List.any_map, List.any_map]
    simp only [Function.comp_def, List.all_cons,
      literal_eval_false, literal_eval_true]
    cases hv : x var <;> simp_all [DNF.eval]

/-- `toCNF` preserves evaluation: `t.toCNF.eval x = t.eval x`. -/
theorem eval_eq_toCNF_eval (t : DecisionTree N) (x : BitString N) :
    t.toCNF.eval x = t.eval x := by
  induction t with
  | leaf val => cases val <;> simp [toCNF, eval, CNF.eval]
  | query var ifFalse ifTrue ihF ihT =>
    simp only [toCNF, eval, CNF.eval]
    rw [List.all_append, List.all_map, List.all_map]
    simp only [Function.comp_def, List.any_cons,
      literal_eval_false, literal_eval_true]
    cases hv : x var <;> simp_all [CNF.eval, List.all_eq_true]

/-- The DNF produced by `toDNF` is k-DNF where k = depth. -/
theorem toDNF_width_le_depth (t : DecisionTree N) :
    t.toDNF.isKDNF t.depth := by
  induction t with
  | leaf val => cases val <;> simp [toDNF, depth, DNF.isKDNF]
  | query var ifFalse ifTrue ihF ihT =>
    simp only [toDNF, depth, DNF.isKDNF]
    intro term hmem
    rw [List.mem_append] at hmem
    cases hmem with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      simp only [List.length_cons]
      have := ihF t ht
      have := Nat.le_max_left ifFalse.depth ifTrue.depth
      omega
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      simp only [List.length_cons]
      have := ihT t ht
      have := Nat.le_max_right ifFalse.depth ifTrue.depth
      omega

/-- The CNF produced by `toCNF` is k-CNF where k = depth. -/
theorem toCNF_width_le_depth (t : DecisionTree N) :
    t.toCNF.isKCNF t.depth := by
  induction t with
  | leaf val => cases val <;> simp [toCNF, depth, CNF.isKCNF]
  | query var ifFalse ifTrue ihF ihT =>
    simp only [toCNF, depth, CNF.isKCNF]
    intro clause hmem
    rw [List.mem_append] at hmem
    cases hmem with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨c, hc, rfl⟩ := h
      simp only [List.length_cons]
      have := ihF c hc
      have := Nat.le_max_left ifFalse.depth ifTrue.depth
      omega
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨c, hc, rfl⟩ := h
      simp only [List.length_cons]
      have := ihT c hc
      have := Nat.le_max_right ifFalse.depth ifTrue.depth
      omega

end DecisionTree
