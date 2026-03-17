import Circ.Restriction.Defs
import Circ.DecisionTree.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

open Classical in
noncomputable section

/-! # Switching Lemma — Statement (sorry'd)

This module states Håstad's switching lemma in its combinatorial counting form.
The proof is deferred (`sorry`) as it requires substantial probabilistic/combinatorial
machinery.

## Main definitions

* `restrictionsWithFreeSet` — the set of all restrictions leaving exactly variables in `S` free
* `hasSmallDecisionTree` — existential: the formula can be computed by a depth-≤-s decision tree

## Main result

* `switching_lemma` — the fraction of restrictions under which a k-DNF fails to
  collapse to a depth-s decision tree is at most `(5k / |S|)^s`
-/

open Finset in
/-- The set of all restrictions on `N` variables that leave exactly the variables
in `S ⊆ Fin N` free (unassigned), and fix all others to some Boolean value. -/
def restrictionsWithFreeSet (N : Nat) (S : Finset (Fin N)) : Finset (Restriction N) :=
  (Fintype.piFinset (fun i =>
    if i ∈ S then {none}
    else {some true, some false})).map
    ⟨fun f => ⟨f⟩, fun _ _ h => by cases h; rfl⟩

/-- A CNF formula has a small decision tree if there exists a decision tree of
depth at most `s` that computes the same function. -/
def CNF.hasSmallDecisionTree (φ : CNF N) (s : Nat) : Prop :=
  ∃ t : DecisionTree N, t.depth ≤ s ∧ ∀ x, φ.eval x = t.eval x

/-- A DNF formula has a small decision tree if there exists a decision tree of
depth at most `s` that computes the same function. -/
def DNF.hasSmallDecisionTree (φ : DNF N) (s : Nat) : Prop :=
  ∃ t : DecisionTree N, t.depth ≤ s ∧ ∀ x, φ.eval x = t.eval x

/-- The number of restrictions with free set `S` is `2^(N - |S|)`:
each non-free variable can be set to `true` or `false`. -/
theorem restrictionsWithFreeSet_card (N : Nat) (S : Finset (Fin N)) :
    (restrictionsWithFreeSet N S).card = 2 ^ (Fintype.card (Fin N) - S.card) := by
  simp only [restrictionsWithFreeSet, Finset.card_map, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton,
    Finset.card_pair (by decide : (some true : Option Bool) ≠ some false)]
  rw [Finset.prod_ite (fun _ => 1) (fun _ => 2)]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const, Finset.filter_not,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 1; exact Finset.card_univ_diff S

/-- **Håstad's Switching Lemma** (combinatorial counting form).

For a k-DNF formula `φ` and a set `S` of free variables, the number of
restrictions (leaving exactly `S` free) under which `φ` does *not* collapse
to a depth-`s` decision tree is at most `(5k)^s / |S|^s` times the total
number of such restrictions.

Equivalently: `Pr_ρ[DT-depth(φ↾ρ) > s] ≤ (5k / |S|)^s`. -/
theorem switching_lemma (φ : DNF N) (k s : Nat) (S : Finset (Fin N))
    (hk : φ.isKDNF k) :
    ((restrictionsWithFreeSet N S).filter
      (fun ρ => ¬(Restriction.applyDNF ρ φ).hasSmallDecisionTree s)).card
      * S.card ^ s
    ≤ (5 * k) ^ s * (restrictionsWithFreeSet N S).card := by
  sorry
