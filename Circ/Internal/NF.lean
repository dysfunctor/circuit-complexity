import Circ.NF.Defs
import Circ.AON.Defs
import Mathlib.Data.Fintype.BigOperators

/-! # Internal: Normal Form Proof Machinery

This internal module contains the proof infrastructure for CNF/DNF:

* **Circuit embedding**: `CNF.toCircuit` and `DNF.toCircuit` embed normal form
  formulas as 2-level circuits over `Basis.unboundedAON`, together with
  correctness (`eval_toCircuit`) and size (`size_toCircuit`) proofs.

* **Lower bound machinery**: `DNF.flip_complexity_lb` shows that any DNF
  computing a flip-sensitive function on `N` variables needs at least `2^{N-1}`
  terms. Key lemmas include `term_mentions_all`, `full_term_unique`, and
  `card_true_of_flip_sensitive`.

The public interface re-exports the main theorems from `Circ.NF`.
-/

/-! ## Helper lemmas for toCircuit correctness -/

private lemma xor_neg_polarity_eq_eval (l : Literal N) (x : BitString N) :
    (!l.polarity).xor (x l.var) = l.eval x := by
  simp [Literal.eval]; cases l.polarity <;> simp

private lemma foldl_bor_eq_true (n : Nat) (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc || g i) false = true) ↔ (∃ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    constructor
    · intro h
      rw [Bool.or_eq_true] at h
      cases h with
      | inl h => rw [ih] at h; obtain ⟨j, hj⟩ := h; exact ⟨j.castSucc, hj⟩
      | inr h => exact ⟨Fin.last n, h⟩
    · intro ⟨i, hi⟩
      rw [Bool.or_eq_true]
      rcases Fin.lastCases (motive := fun i => (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n)
        (Or.inr rfl) (fun j => Or.inl ⟨j, rfl⟩) i with ⟨j, rfl⟩ | rfl
      · left; rw [ih]; exact ⟨j, hi⟩
      · right; exact hi

private lemma foldl_band_eq_true (n : Nat) (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc && g i) true = true) ↔ (∀ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]; constructor
    · intro h; rw [Bool.and_eq_true] at h; obtain ⟨h1, h2⟩ := h
      rw [ih] at h1; intro i; exact Fin.lastCases h2 (fun j => h1 j) i
    · intro h; rw [Bool.and_eq_true]
      exact ⟨(ih _).mpr (fun j => h j.castSucc), h (Fin.last n)⟩

private lemma foldl_bor_eq_list_any {α : Type} (l : List α) (p : α → Bool) :
    Fin.foldl l.length (fun acc (i : Fin l.length) => acc || p (l.get i)) false = l.any p := by
  have h_iff : (Fin.foldl l.length (fun acc i => acc || p (l.get i)) false = true) ↔
      (l.any p = true) := by
    rw [foldl_bor_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨l.get i, List.get_mem l i, hi⟩
    · rintro ⟨a, ha, hp⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      exact ⟨i, hp⟩
  cases h1 : Fin.foldl l.length (fun acc i => acc || p (l.get i)) false <;>
    cases h2 : l.any p <;> simp_all

private lemma foldl_band_eq_list_all {α : Type} (l : List α) (p : α → Bool) :
    Fin.foldl l.length (fun acc (i : Fin l.length) => acc && p (l.get i)) true = l.all p := by
  have h_iff : (Fin.foldl l.length (fun acc i => acc && p (l.get i)) true = true) ↔
      (l.all p = true) := by
    rw [foldl_band_eq_true, List.all_eq_true]
    constructor
    · intro h a ha
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      exact h i
    · intro h i; exact h (l.get i) (List.get_mem l i)
  cases h1 : Fin.foldl l.length (fun acc i => acc && p (l.get i)) true <;>
    cases h2 : l.all p <;> simp_all

/-! ## CNF circuit embedding -/

namespace CNF

/-- Embed a CNF formula as a 2-level AND-of-ORs circuit over `Basis.unboundedAON`.

The circuit has `φ.complexity` internal OR gates (one per clause) and a single
output AND gate. Each OR gate reads only primary input wires, with the `negated`
flag encoding literal polarity. The circuit size is `φ.complexity + 1`. -/
def toCircuit {N : Nat} [NeZero N] (φ : CNF N) :
    Circuit Basis.unboundedAON N 1 φ.complexity where
  gates i :=
    let clause := φ.clauses.get ⟨i.val, i.isLt⟩
    { op := .or
      fanIn := clause.length
      arityOk := trivial
      inputs := fun j => ⟨(clause.get j).var.val, by
        have := (clause.get j).var.isLt; omega⟩
      negated := fun j => !(clause.get j).polarity }
  outputs _ :=
    { op := .and
      fanIn := φ.complexity
      arityOk := trivial
      inputs := fun j => ⟨N + j.val, by omega⟩
      negated := fun _ => false }
  acyclic i j :=
    Nat.lt_of_lt_of_le
      ((φ.clauses.get ⟨i.val, i.isLt⟩).get ⟨j.val, j.isLt⟩).var.isLt
      (Nat.le_add_right N i.val)

private lemma wireValue_gate [NeZero N] (φ : CNF N) (x : BitString N) (i : Fin φ.complexity) :
    φ.toCircuit.wireValue x ⟨N + i.val, by omega⟩ =
      (φ.clauses.get ⟨i.val, i.isLt⟩).any (fun l => l.eval x) := by
  have hge : ¬ ((⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val < N) := by simp
  rw [Circuit.wireValue_ge _ x _ hge]
  -- Normalize gate index
  have hgi : φ.toCircuit.gates ⟨(⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val - N,
    (by omega)⟩ = φ.toCircuit.gates i := by congr 1; ext; simp
  rw [hgi]
  -- Unfold gate definition
  simp only [toCircuit, Gate.eval, Basis.unboundedAON, AONOp.eval]
  -- Handle wireValue for primary inputs + xor-negation inside foldl
  conv_lhs => arg 2; ext acc j; arg 2; arg 2
              rw [Circuit.wireValue_lt _ _ _
                ((φ.clauses.get ⟨↑i, i.isLt⟩).get j).var.isLt]
  conv_lhs => arg 2; ext acc j; arg 2
              rw [xor_neg_polarity_eq_eval]
  exact foldl_bor_eq_list_any (φ.clauses.get ⟨↑i, i.isLt⟩) (fun l => l.eval x)

/-- The circuit produced by `toCircuit` correctly computes the CNF formula. -/
theorem eval_toCircuit [NeZero N] (φ : CNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by
  funext x
  simp only [Circuit.eval, eval, toCircuit, Gate.eval, Basis.unboundedAON, Bool.false_xor,
    AONOp.eval]
  -- Convert struct-literal wireValue back to φ.toCircuit form for wireValue_gate
  change Fin.foldl φ.complexity
    (fun acc j => acc && φ.toCircuit.wireValue x ⟨N + j.val, by omega⟩) true =
    φ.clauses.all (fun clause => clause.any fun l => l.eval x)
  conv_lhs => arg 2; ext acc j; arg 2; rw [wireValue_gate φ x j]
  exact foldl_band_eq_list_all φ.clauses (fun clause => clause.any fun l => l.eval x)

/-- The circuit size of `toCircuit` is `φ.complexity + 1`. -/
theorem size_toCircuit [NeZero N] (φ : CNF N) :
    φ.toCircuit.size = φ.complexity + 1 := rfl

end CNF

/-! ## DNF circuit embedding -/

namespace DNF

/-- Embed a DNF formula as a 2-level OR-of-ANDs circuit over `Basis.unboundedAON`.

The circuit has `φ.complexity` internal AND gates (one per term) and a single
output OR gate. Each AND gate reads only primary input wires, with the `negated`
flag encoding literal polarity. The circuit size is `φ.complexity + 1`. -/
def toCircuit {N : Nat} [NeZero N] (φ : DNF N) :
    Circuit Basis.unboundedAON N 1 φ.complexity where
  gates i :=
    let term := φ.terms.get ⟨i.val, i.isLt⟩
    { op := .and
      fanIn := term.length
      arityOk := trivial
      inputs := fun j => ⟨(term.get j).var.val, by
        have := (term.get j).var.isLt; omega⟩
      negated := fun j => !(term.get j).polarity }
  outputs _ :=
    { op := .or
      fanIn := φ.complexity
      arityOk := trivial
      inputs := fun j => ⟨N + j.val, by omega⟩
      negated := fun _ => false }
  acyclic i j :=
    Nat.lt_of_lt_of_le
      ((φ.terms.get ⟨i.val, i.isLt⟩).get ⟨j.val, j.isLt⟩).var.isLt
      (Nat.le_add_right N i.val)

private lemma wireValue_gate [NeZero N] (φ : DNF N) (x : BitString N) (i : Fin φ.complexity) :
    φ.toCircuit.wireValue x ⟨N + i.val, by omega⟩ =
      (φ.terms.get ⟨i.val, i.isLt⟩).all (fun l => l.eval x) := by
  have hge : ¬ ((⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val < N) := by simp
  rw [Circuit.wireValue_ge _ x _ hge]
  -- Normalize gate index
  have hgi : φ.toCircuit.gates ⟨(⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val - N,
    (by omega)⟩ = φ.toCircuit.gates i := by congr 1; ext; simp
  rw [hgi]
  -- Unfold gate definition
  simp only [toCircuit, Gate.eval, Basis.unboundedAON, AONOp.eval]
  -- Handle wireValue for primary inputs + xor-negation inside foldl
  conv_lhs => arg 2; ext acc j; arg 2; arg 2
              rw [Circuit.wireValue_lt _ _ _
                ((φ.terms.get ⟨↑i, i.isLt⟩).get j).var.isLt]
  conv_lhs => arg 2; ext acc j; arg 2
              rw [xor_neg_polarity_eq_eval]
  exact foldl_band_eq_list_all (φ.terms.get ⟨↑i, i.isLt⟩) (fun l => l.eval x)

/-- The circuit produced by `toCircuit` correctly computes the DNF formula. -/
theorem eval_toCircuit [NeZero N] (φ : DNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by
  funext x
  simp only [Circuit.eval, eval, toCircuit, Gate.eval, Basis.unboundedAON, Bool.false_xor,
    AONOp.eval]
  -- Convert struct-literal wireValue back to φ.toCircuit form for wireValue_gate
  change Fin.foldl φ.complexity
    (fun acc j => acc || φ.toCircuit.wireValue x ⟨N + j.val, by omega⟩) false =
    φ.terms.any (fun term => term.all fun l => l.eval x)
  conv_lhs => arg 2; ext acc j; arg 2; rw [wireValue_gate φ x j]
  exact foldl_bor_eq_list_any φ.terms (fun term => term.all fun l => l.eval x)

/-- The circuit size of `toCircuit` is `φ.complexity + 1`. -/
theorem size_toCircuit [NeZero N] (φ : DNF N) :
    φ.toCircuit.size = φ.complexity + 1 := rfl

end DNF

/-! ## CNF/DNF Lower Bound for Flip-Sensitive Functions -/

/-- A literal that doesn't mention variable `i` evaluates the same when `i` is flipped. -/
private lemma Literal.eval_update_ne {l : Literal N} {i : Fin N} (hne : l.var ≠ i)
    (x : BitString N) (b : Bool) :
    l.eval (Function.update x i b) = l.eval x := by
  simp [Literal.eval]
  rw [Function.update_of_ne hne]

/-- If a term (conjunction of literals) doesn't mention variable `i`,
then flipping `i` doesn't change whether the term is satisfied. -/
private lemma term_eval_update {term : List (Literal N)} {i : Fin N}
    (hmiss : ∀ l ∈ term, l.var ≠ i) (x : BitString N) (b : Bool) :
    term.all (fun l => l.eval (Function.update x i b)) = term.all (fun l => l.eval x) := by
  induction term with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons]
    rw [Literal.eval_update_ne (hmiss hd List.mem_cons_self) x b]
    rw [ih (fun l hl => hmiss l (List.mem_cons_of_mem _ hl))]

/-- If `φ : DNF N` computes a flip-sensitive function, every satisfiable term
mentions all N variables. -/
theorem DNF.term_mentions_all (φ : DNF N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x)
    (term : List (Literal N)) (hterm : term ∈ φ.terms)
    (x : BitString N) (hsat : term.all (fun l => l.eval x) = true) :
    ∀ i : Fin N, ∃ l ∈ term, l.var = i := by
  intro i
  by_contra hmiss
  push_neg at hmiss
  -- hmiss : ∀ l ∈ term, l.var ≠ i
  -- Since term misses variable i, flipping i doesn't change the term
  have hsat' : term.all (fun l => l.eval (Function.update x i (!x i))) = true := by
    rw [term_eval_update hmiss]; exact hsat
  -- Both x and (flip x i) satisfy the term, so DNF is true on both
  have hx_true : φ.eval x = true := by
    simp only [DNF.eval, List.any_eq_true]
    exact ⟨term, hterm, hsat⟩
  have hx'_true : φ.eval (Function.update x i (!x i)) = true := by
    simp only [DNF.eval, List.any_eq_true]
    exact ⟨term, hterm, hsat'⟩
  -- But f flips, so f x ≠ f (flip x i)
  have := hflip x i
  rw [← hcomp, ← hcomp] at this
  rw [hx_true, hx'_true] at this
  simp at this

/-- If a term mentions all N variables, it is satisfied by at most one assignment. -/
theorem full_term_unique {term : List (Literal N)}
    (hfull : ∀ i : Fin N, ∃ l ∈ term, l.var = i)
    {x y : BitString N}
    (hx : term.all (fun l => l.eval x) = true)
    (hy : term.all (fun l => l.eval y) = true) :
    x = y := by
  funext i
  obtain ⟨l, hl_mem, hl_var⟩ := hfull i
  have hx_l : l.eval x = true := by
    rw [List.all_eq_true] at hx; exact hx l hl_mem
  have hy_l : l.eval y = true := by
    rw [List.all_eq_true] at hy; exact hy l hl_mem
  simp only [Literal.eval, hl_var] at hx_l hy_l
  split at hx_l <;> split at hy_l <;> simp_all

/-- If `f` is flip-sensitive with `N ≥ 1`, its true-set has exactly `2^{N-1}` elements. -/
theorem card_true_of_flip_sensitive {N : Nat} (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    (Finset.univ.filter (fun x => f x = true)).card = 2 ^ (N - 1) := by
  set S_true := Finset.univ.filter (fun x => f x = true)
  set S_false := Finset.univ.filter (fun x => f x = false)
  -- The involution: flip variable 0
  have hN' : 0 < N := by omega
  set flip0 : BitString N → BitString N := fun x => Function.update x ⟨0, hN'⟩ (!x ⟨0, hN'⟩)
  -- flip0 is self-inverse
  have flip0_inv : ∀ x, flip0 (flip0 x) = x := by
    intro x; ext j; simp only [flip0]
    by_cases h : j = ⟨0, hN'⟩
    · subst h; simp [Function.update_self, Bool.not_not]
    · simp [Function.update_of_ne h]
  -- flip0 maps true-set to false-set
  have flip0_tf : ∀ x, f x = true → f (flip0 x) = false := by
    intro x hx; have := hflip x ⟨0, hN'⟩; rw [hx] at this; simpa using this
  -- Bijection from S_true to S_false
  have hcard_eq : S_true.card = S_false.card := by
    apply Finset.card_bij (fun x _ => flip0 x)
    · intro x hx; simp [S_true, S_false] at hx ⊢; exact flip0_tf x hx
    · intro a₁ h₁ a₂ h₂ heq
      have := congr_arg flip0 heq
      rwa [flip0_inv, flip0_inv] at this
    · intro b hb
      refine ⟨flip0 b, ?_, flip0_inv b⟩
      simp only [S_true, S_false, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      -- f b = false, need f (flip0 b) = true
      have h1 := hflip b ⟨0, hN'⟩
      rw [hb] at h1; simpa using h1
  -- |S_true| + |S_false| = 2^N
  have hcard_total : S_true.card + S_false.card = 2 ^ N := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : BitString N => f x = true)
    simp only [Finset.card_univ] at h
    rw [show Fintype.card (BitString N) = 2 ^ N from by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]] at h
    convert h using 2
    simp only [S_false]
    congr 1; ext x; cases f x <;> simp
  -- 2 * S_true.card = 2^N, so S_true.card = 2^{N-1}
  have : 2 * S_true.card = 2 ^ N := by omega
  have : 2 ^ N = 2 * 2 ^ (N - 1) := by
    cases N with
    | zero => omega
    | succ n => simp [Nat.pow_succ, Nat.mul_comm]
  omega

/-- If `φ : DNF N` computes a flip-sensitive function with `N ≥ 1`,
then `2^{N-1} ≤ φ.complexity`. -/
theorem DNF.flip_complexity_lb (φ : DNF N) (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    2 ^ (N - 1) ≤ φ.complexity := by
  -- Every true assignment is covered by some term, and each full term covers ≤ 1 assignment
  suffices h : (Finset.univ.filter (fun x : BitString N => f x = true)).card ≤ φ.complexity by
    rwa [card_true_of_flip_sensitive hN f hflip] at h
  -- For each true x, find a term that x satisfies
  have hfind : ∀ x : BitString N, f x = true →
      ∃ term ∈ φ.terms, term.all (fun l => l.eval x) = true := by
    intro x hx
    have : φ.eval x = true := by rw [hcomp]; exact hx
    simpa [DNF.eval, List.any_eq_true] using this
  -- Each satisfiable term mentions all variables (so is satisfied by ≤ 1 assignment)
  have huniq : ∀ term ∈ φ.terms, ∀ x₁ x₂ : BitString N,
      term.all (fun l => l.eval x₁) = true →
      term.all (fun l => l.eval x₂) = true →
      x₁ = x₂ := by
    intro term hterm x₁ x₂ h₁ h₂
    have hfull := DNF.term_mentions_all φ f hcomp hflip term hterm x₁ h₁
    exact full_term_unique hfull h₁ h₂
  -- Count: |true-set| ≤ |terms| by injection via findIdx
  -- Reformulate as card ≤ card
  rw [show φ.complexity = (Finset.range φ.complexity).card from
    (Finset.card_range φ.complexity).symm]
  apply Finset.card_le_card_of_injOn
    (fun x => φ.terms.findIdx (fun t => t.all (fun l => l.eval x)))
  · -- MapsTo: findIdx lands in range
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_setOf, true_and] at hx
    simp only [Finset.coe_range, Set.mem_Iio, DNF.complexity]
    rw [List.findIdx_lt_length]
    exact hfind x hx
  · -- InjOn: two true assignments with same findIdx must be equal
    intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_setOf, true_and] at hx₁ hx₂
    set k := φ.terms.findIdx (fun t => t.all (fun l => l.eval x₂))
    have hlt : k < φ.terms.length := by
      rw [List.findIdx_lt_length]; exact hfind x₂ hx₂
    have sat₂ : (φ.terms[k]'hlt).all (fun l => l.eval x₂) = true :=
      List.findIdx_getElem (w := hlt)
    have hlt₁ : φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁)) < φ.terms.length := by
      rw [List.findIdx_lt_length]; exact hfind x₁ hx₁
    have sat₁ : (φ.terms[φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁))]'hlt₁).all
        (fun l => l.eval x₁) = true :=
      List.findIdx_getElem (w := hlt₁)
    have heq' : φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁)) = k := heq
    rw [show (φ.terms[φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁))]'hlt₁) =
        (φ.terms[k]'hlt) from by congr 1] at sat₁
    exact huniq _ (List.getElem_mem ..) x₁ x₂ sat₁ sat₂

/-! ## Circuit to ACNFTree conversion -/

namespace Circuit
variable {N G : Nat} [NeZero N]

/-- Convert a wire in an unbounded-fan-in AND/OR circuit to a raw ACNF tree.

`pol = true` gives the wire's value; `pol = false` gives its negation.
Negations are pushed to leaves via De Morgan duality. -/
def wireToACNFTree (c : Circuit Basis.unboundedAON N 1 G)
    (w : Fin (N + G)) (pol : Bool) : ACNFTree N :=
  if h : w.val < N then
    ACNFTree.lit ⟨⟨w.val, h⟩, pol⟩
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    let children := List.ofFn (fun k : Fin gate.fanIn =>
      c.wireToACNFTree (gate.inputs k) (Bool.xor pol (gate.negated k)))
    match gate.op, pol with
    | .and, true  => ACNFTree.and children
    | .or, false  => ACNFTree.and children
    | .or, true   => ACNFTree.or children
    | .and, false  => ACNFTree.or children
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Convert a single-output unbounded-fan-in AND/OR circuit to a raw ACNF tree.

Expands the circuit DAG into a tree, pushing negations to leaves. -/
def toACNFTree (c : Circuit Basis.unboundedAON N 1 G) : ACNFTree N :=
  let outGate := c.outputs 0
  let children := List.ofFn (fun k : Fin outGate.fanIn =>
    c.wireToACNFTree (outGate.inputs k) (Bool.xor true (outGate.negated k)))
  match outGate.op with
  | .and => ACNFTree.and children
  | .or  => ACNFTree.or children

/-- Maximum fan-in across all gates (internal + output) in a single-output circuit. -/
def maxFanIn (c : Circuit B N 1 G) : Nat :=
  let internal := Fin.foldl G (fun acc i => max acc (c.gates i).fanIn) 0
  max internal (c.outputs 0).fanIn

end Circuit

/-! # Internal: Alternating Normal Form Correctness

Proofs that normalization preserves evaluation semantics, produces alternating
trees, and does not increase depth. Also proves CNF/DNF to ACNFTree conversion
preserves evaluation.

## Main results

* `ACNFTree.normalize_eval` — normalization preserves evaluation
* `ACNFTree.normalize_depth_le` — normalization does not increase depth
* `ACNFTree.normalize_isAlternating` — normalization produces alternating trees
* `CNF.toACNFTree_eval` — CNF to ACNFTree preserves evaluation
* `DNF.toACNFTree_eval` — DNF to ACNFTree preserves evaluation
* `Circuit.wireToACNFTree_eval` — circuit wire to ACNFTree preserves evaluation
* `Circuit.toACNFTree_eval` — circuit to ACNFTree preserves evaluation
* `Circuit.toACNFTree_depth_le` — ACNFTree depth bounded by circuit depth
* `Circuit.toACNFTree_normalize_isAlternating` — normalized ACNFTree is alternating
* `Circuit.toACNFTree_leafCount_le` — ACNFTree leaf count bounded by maxFanIn^depth
-/

namespace ACNFTree

variable {N : Nat}

/-! ## Relating evalAll/evalAny to List.all/List.any -/

theorem evalAll_eq_all (cs : List (ACNFTree N)) (x : BitString N) :
    eval.evalAll cs x = cs.all (fun c => c.eval x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [eval.evalAll, List.all_cons, ih]

theorem evalAny_eq_any (cs : List (ACNFTree N)) (x : BitString N) :
    eval.evalAny cs x = cs.any (fun c => c.eval x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [eval.evalAny, List.any_cons, ih]

/-! ## Eval append lemmas -/

theorem evalAll_append (l₁ l₂ : List (ACNFTree N)) (x : BitString N) :
    eval.evalAll (l₁ ++ l₂) x = (eval.evalAll l₁ x && eval.evalAll l₂ x) := by
  induction l₁ with
  | nil => simp [eval.evalAll]
  | cons c cs ih => simp only [List.cons_append, eval.evalAll, ih, Bool.and_assoc]

theorem evalAny_append (l₁ l₂ : List (ACNFTree N)) (x : BitString N) :
    eval.evalAny (l₁ ++ l₂) x = (eval.evalAny l₁ x || eval.evalAny l₂ x) := by
  induction l₁ with
  | nil => simp [eval.evalAny]
  | cons c cs ih => simp only [List.cons_append, eval.evalAny, ih, Bool.or_assoc]

/-! ## Depth list append -/

theorem depthList_append (l₁ l₂ : List (ACNFTree N)) :
    depth.depthList (l₁ ++ l₂) = max (depth.depthList l₁) (depth.depthList l₂) := by
  induction l₁ with
  | nil => simp [depth.depthList]
  | cons c cs ih => simp only [List.cons_append, depth.depthList, ih, Nat.max_assoc]

/-! ## IsAlternating list append -/

theorem isAlternatingAndList_append (l₁ l₂ : List (ACNFTree N)) :
    isAlternating.isAlternatingAndList (l₁ ++ l₂) =
    (isAlternating.isAlternatingAndList l₁ && isAlternating.isAlternatingAndList l₂) := by
  induction l₁ with
  | nil => simp [isAlternating.isAlternatingAndList]
  | cons c cs ih =>
    simp only [List.cons_append, isAlternating.isAlternatingAndList, ih, Bool.and_assoc]

theorem isAlternatingOrList_append (l₁ l₂ : List (ACNFTree N)) :
    isAlternating.isAlternatingOrList (l₁ ++ l₂) =
    (isAlternating.isAlternatingOrList l₁ && isAlternating.isAlternatingOrList l₂) := by
  induction l₁ with
  | nil => simp [isAlternating.isAlternatingOrList]
  | cons c cs ih =>
    simp only [List.cons_append, isAlternating.isAlternatingOrList, ih, Bool.and_assoc]

/-! ## SizeOf helpers for termination proofs -/

-- The auto-generated sizeOf for nested inductives requires manual unfolding.
private theorem sizeOf_lt_and {c : ACNFTree N} {children : List (ACNFTree N)}
    (hc : c ∈ children) : sizeOf c < sizeOf (ACNFTree.and children) := by
  induction hc with
  | head as =>
    show ACNFTree._sizeOf_1 _ < ACNFTree._sizeOf_1 _
    simp only [ACNFTree._sizeOf_1]
    omega
  | tail b _ ih =>
    apply Nat.lt_trans ih
    show ACNFTree._sizeOf_1 _ < ACNFTree._sizeOf_1 _
    simp only [ACNFTree._sizeOf_1]
    omega


/-! ## Normalize preserves eval -/

private theorem normalizeAndFlatten_evalAll (children : List (ACNFTree N)) (x : BitString N)
    (ih : ∀ c, c ∈ children → c.normalize.eval x = c.eval x) :
    eval.evalAll (normalize.normalizeAndFlatten children) x = eval.evalAll children x := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeAndFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [eval.evalAll, hrest, ← hc, hn]
    | and gcs =>
      rw [evalAll_append, hrest, eval.evalAll, ← hc, hn, eval]
    | or cs' =>
      simp only [eval.evalAll, hrest, ← hc, hn]

private theorem normalizeOrFlatten_evalAny (children : List (ACNFTree N)) (x : BitString N)
    (ih : ∀ c, c ∈ children → c.normalize.eval x = c.eval x) :
    eval.evalAny (normalize.normalizeOrFlatten children) x = eval.evalAny children x := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeOrFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [eval.evalAny, hrest, ← hc, hn]
    | and gcs =>
      simp only [eval.evalAny, hrest, ← hc, hn]
    | or cs' =>
      rw [evalAny_append, hrest, eval.evalAny, ← hc, hn, eval]

/-- Normalization preserves evaluation semantics. -/
theorem normalize_eval : (f : ACNFTree N) → (x : BitString N) →
    f.normalize.eval x = f.eval x
  | .lit _, _ => rfl
  | .and children, x => by
    simp only [normalize, eval]
    exact normalizeAndFlatten_evalAll children x (fun c hc => normalize_eval c x)
  | .or children, x => by
    simp only [normalize, eval]
    exact normalizeOrFlatten_evalAny children x (fun c hc => normalize_eval c x)
termination_by f => sizeOf f
decreasing_by
  all_goals exact sizeOf_lt_and hc

/-! ## Normalize does not increase depth -/

private theorem normalizeAndFlatten_depthList (children : List (ACNFTree N))
    (ih : ∀ c, c ∈ children → c.normalize.depth ≤ c.depth) :
    depth.depthList (normalize.normalizeAndFlatten children) ≤ depth.depthList children := by
  induction children with
  | nil => simp [normalize.normalizeAndFlatten]
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeAndFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [depth.depthList]
      exact max_le_max (by rw [← hn]; exact hc) hrest
    | and gcs =>
      rw [depthList_append]
      apply max_le_iff.mpr
      constructor
      · -- depthList gcs ≤ max c.depth (depthList cs)
        have hdep : depth (.and gcs) ≤ c.depth := hn ▸ hc
        simp only [depth] at hdep
        exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
      · exact Nat.le_trans hrest (Nat.le_max_right _ _)
    | or cs' =>
      simp only [depth.depthList]
      exact max_le_max (by rw [← hn]; exact hc) hrest

private theorem normalizeOrFlatten_depthList (children : List (ACNFTree N))
    (ih : ∀ c, c ∈ children → c.normalize.depth ≤ c.depth) :
    depth.depthList (normalize.normalizeOrFlatten children) ≤ depth.depthList children := by
  induction children with
  | nil => simp [normalize.normalizeOrFlatten]
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeOrFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [depth.depthList]
      exact max_le_max (by rw [← hn]; exact hc) hrest
    | and gcs =>
      simp only [depth.depthList]
      exact max_le_max (by rw [← hn]; exact hc) hrest
    | or cs' =>
      rw [depthList_append]
      apply max_le_iff.mpr
      constructor
      · have hdep : depth (.or cs') ≤ c.depth := hn ▸ hc
        simp only [depth] at hdep
        exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
      · exact Nat.le_trans hrest (Nat.le_max_right _ _)

/-- Normalization does not increase depth. -/
theorem normalize_depth_le : (f : ACNFTree N) → f.normalize.depth ≤ f.depth
  | .lit _ => Nat.le.refl
  | .and children => by
    simp only [normalize, depth]
    exact Nat.add_le_add_left (normalizeAndFlatten_depthList children
      (fun c hc => normalize_depth_le c)) 1
  | .or children => by
    simp only [normalize, depth]
    exact Nat.add_le_add_left (normalizeOrFlatten_depthList children
      (fun c hc => normalize_depth_le c)) 1
termination_by f => sizeOf f
decreasing_by
  all_goals exact sizeOf_lt_and hc

/-! ## Normalize produces alternating trees -/

private theorem normalizeAndFlatten_isAlternatingAndList (children : List (ACNFTree N))
    (ih : ∀ c, c ∈ children → c.normalize.isAlternating = true) :
    isAlternating.isAlternatingAndList (normalize.normalizeAndFlatten children) = true := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeAndFlatten]
    generalize hn : c.normalize = nc
    rw [hn] at hc
    cases nc with
    | lit l =>
      simp [isAlternating.isAlternatingAndList, rootOp, isAlternating, hrest]
    | and gcs =>
      rw [isAlternatingAndList_append, hrest, Bool.and_true]
      simp only [isAlternating] at hc; exact hc
    | or cs' =>
      simp only [isAlternating.isAlternatingAndList, rootOp, hrest, Bool.and_true]
      rw [hc, Bool.and_true]; decide

private theorem normalizeOrFlatten_isAlternatingOrList (children : List (ACNFTree N))
    (ih : ∀ c, c ∈ children → c.normalize.isAlternating = true) :
    isAlternating.isAlternatingOrList (normalize.normalizeOrFlatten children) = true := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeOrFlatten]
    generalize hn : c.normalize = nc
    rw [hn] at hc
    cases nc with
    | lit l =>
      simp [isAlternating.isAlternatingOrList, rootOp, isAlternating, hrest]
    | and gcs =>
      simp only [isAlternating.isAlternatingOrList, rootOp, hrest, Bool.and_true]
      rw [hc, Bool.and_true]; decide
    | or cs' =>
      rw [isAlternatingOrList_append, hrest, Bool.and_true]
      simp only [isAlternating] at hc; exact hc

/-- Normalization produces alternating trees. -/
theorem normalize_isAlternating : (f : ACNFTree N) → f.normalize.isAlternating = true
  | .lit _ => rfl
  | .and children => by
    simp only [normalize, isAlternating]
    exact normalizeAndFlatten_isAlternatingAndList children
      (fun c hc => normalize_isAlternating c)
  | .or children => by
    simp only [normalize, isAlternating]
    exact normalizeOrFlatten_isAlternatingOrList children
      (fun c hc => normalize_isAlternating c)
termination_by f => sizeOf f
decreasing_by
  all_goals exact sizeOf_lt_and hc

end ACNFTree

/-! ## CNF/DNF to ACNFTree conversion correctness -/

/-- Converting a CNF to ACNFTree preserves evaluation. -/
theorem CNF.toACNFTree_eval (φ : CNF N) (x : BitString N) :
    φ.toACNFTree.eval x = φ.eval x := by
  simp only [CNF.toACNFTree, ACNFTree.eval, ACNFTree.evalAll_eq_all, CNF.eval,
    List.all_map, Function.comp_def, ACNFTree.evalAny_eq_any, List.any_map, ACNFTree.eval]

/-- Converting a DNF to ACNFTree preserves evaluation. -/
theorem DNF.toACNFTree_eval (φ : DNF N) (x : BitString N) :
    φ.toACNFTree.eval x = φ.eval x := by
  simp only [DNF.toACNFTree, ACNFTree.eval, ACNFTree.evalAny_eq_any, DNF.eval,
    List.any_map, Function.comp_def, ACNFTree.evalAll_eq_all, List.all_map, ACNFTree.eval]

/-! ## Bridging: List.ofFn ↔ Fin.foldl -/

namespace ACNFTree

private theorem foldl_and_init (n : Nat) (g : Fin n → Bool) (a : Bool) :
    Fin.foldl n (fun acc k => acc && g k) a =
    (a && Fin.foldl n (fun acc k => acc && g k) true) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.true_and]
    rw [ih (fun k => g k.succ) (a && g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Bool.and_assoc]

private theorem foldl_or_init (n : Nat) (g : Fin n → Bool) (a : Bool) :
    Fin.foldl n (fun acc k => acc || g k) a =
    (a || Fin.foldl n (fun acc k => acc || g k) false) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.false_or]
    rw [ih (fun k => g k.succ) (a || g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Bool.or_assoc]

theorem evalAll_ofFn (n : Nat) (f : Fin n → ACNFTree N) (x : BitString N) :
    eval.evalAll (List.ofFn f) x =
    (Fin.foldl n (fun acc k => acc && (f k).eval x) true) := by
  induction n with
  | zero => simp [List.ofFn_zero, eval.evalAll, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ, eval.evalAll, ih]
    conv_rhs => rw [Fin.foldl_succ]
    simp only [Bool.true_and]
    exact (foldl_and_init n (fun k => (f k.succ).eval x) ((f 0).eval x)).symm

theorem evalAny_ofFn (n : Nat) (f : Fin n → ACNFTree N) (x : BitString N) :
    eval.evalAny (List.ofFn f) x =
    (Fin.foldl n (fun acc k => acc || (f k).eval x) false) := by
  induction n with
  | zero => simp [List.ofFn_zero, eval.evalAny, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ, eval.evalAny, ih]
    conv_rhs => rw [Fin.foldl_succ]
    simp only [Bool.false_or]
    exact (foldl_or_init n (fun k => (f k.succ).eval x) ((f 0).eval x)).symm

private theorem foldl_max_init (n : Nat) (g : Fin n → Nat) (a : Nat) :
    Fin.foldl n (fun acc k => max acc (g k)) a =
    max a (Fin.foldl n (fun acc k => max acc (g k)) 0) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Nat.zero_max]
    rw [ih (fun k => g k.succ) (max a (g 0))]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Nat.max_assoc]

private theorem foldl_add_init (n : Nat) (g : Fin n → Nat) (a : Nat) :
    Fin.foldl n (fun acc k => acc + g k) a =
    a + Fin.foldl n (fun acc k => acc + g k) 0 := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Nat.zero_add]
    rw [ih (fun k => g k.succ) (a + g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    omega

theorem foldl_deMorgan_and (n : Nat) (f : Fin n → Bool) :
    Fin.foldl n (fun acc k => acc || !f k) false =
    !(Fin.foldl n (fun acc k => acc && f k) true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.true_and, Bool.false_or]
    rw [foldl_or_init n (fun k => !(f k.succ)) (!(f 0))]
    rw [ih (fun k => f k.succ)]
    rw [foldl_and_init n (fun k => f k.succ) (f 0)]
    simp [Bool.not_and]

theorem foldl_deMorgan_or (n : Nat) (f : Fin n → Bool) :
    Fin.foldl n (fun acc k => acc && !f k) true =
    !(Fin.foldl n (fun acc k => acc || f k) false) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.false_or, Bool.true_and]
    rw [foldl_and_init n (fun k => !(f k.succ)) (!(f 0))]
    rw [ih (fun k => f k.succ)]
    rw [foldl_or_init n (fun k => f k.succ) (f 0)]
    simp [Bool.not_or]

private theorem depthList_ofFn_le (n : Nat) (f : Fin n → ACNFTree N) (g : Fin n → Nat)
    (h : ∀ k, (f k).depth ≤ g k) :
    depth.depthList (List.ofFn f) ≤ Fin.foldl n (fun acc k => max acc (g k)) 0 := by
  induction n with
  | zero => simp [List.ofFn_zero, depth.depthList, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [depth.depthList]
    conv_rhs => rw [Fin.foldl_succ, Nat.zero_max]
    rw [foldl_max_init]
    exact max_le_max (h 0) (ih (fun k => f k.succ) (fun k => g k.succ) (fun k => h k.succ))

private theorem leafCountList_ofFn (n : Nat) (f : Fin n → ACNFTree N) :
    leafCount.leafCountList (List.ofFn f) =
    Fin.foldl n (fun acc k => acc + (f k).leafCount) 0 := by
  induction n with
  | zero => simp [List.ofFn_zero, leafCount.leafCountList, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [leafCount.leafCountList]
    conv_rhs => rw [Fin.foldl_succ, Nat.zero_add]
    rw [foldl_add_init, ih]

end ACNFTree

/-! ## Circuit to ACNFTree: evaluation correctness -/

namespace Circuit
variable {N G : Nat} [NeZero N]

private theorem xor_not_xor (a b : Bool) : (!a ^^ b) = !(a ^^ b) := by cases a <;> cases b <;> rfl

/-- Converting a wire to ACNFTree preserves evaluation (with polarity). -/
theorem wireToACNFTree_eval (c : Circuit Basis.unboundedAON N 1 G)
    (x : BitString N) (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNFTree w pol).eval x = (!pol ^^ c.wireValue x w) := by
  conv_lhs => unfold wireToACNFTree
  split
  · -- Primary input (w.val < N)
    rename_i h
    simp only [wireValue_lt c x w h, ACNFTree.eval, Literal.eval]
    cases pol <;> simp
  · -- Gate wire (w.val ≥ N)
    rename_i h
    have hG : w.val - N < G := by omega
    conv_rhs => rw [wireValue_ge c x w h]; simp only [Gate.eval, Basis.unboundedAON]
    -- IH for each child wire
    have ce : ∀ k : Fin (c.gates ⟨w.val - N, hG⟩).fanIn,
        (c.wireToACNFTree ((c.gates ⟨w.val - N, hG⟩).inputs k)
          (pol ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).eval x =
        (!(pol ^^ (c.gates ⟨w.val - N, hG⟩).negated k) ^^
          c.wireValue x ((c.gates ⟨w.val - N, hG⟩).inputs k)) :=
      fun k => wireToACNFTree_eval c x _ _
    -- Rewrite children using IH and simplify xor
    simp only [xor_not_xor] at ce
    -- Case split on (op, pol) to reduce the match
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      simp only [hop, ACNFTree.eval, AONOp.eval, Bool.true_xor, Bool.false_xor,
        Bool.not_true, Bool.not_false] at ce ⊢
    -- AND/false: De Morgan — evalAny vs !(foldl &&)
    · rw [ACNFTree.evalAny_ofFn]; simp_rw [ce]; exact ACNFTree.foldl_deMorgan_and _ _
    -- AND/true: same-op — evalAll vs foldl &&
    · rw [ACNFTree.evalAll_ofFn]; simp_rw [ce, xor_not_xor, Bool.not_not]; rfl
    -- OR/false: De Morgan — evalAll vs !(foldl ||)
    · rw [ACNFTree.evalAll_ofFn]; simp_rw [ce]; exact ACNFTree.foldl_deMorgan_or _ _
    -- OR/true: same-op — evalAny vs foldl ||
    · rw [ACNFTree.evalAny_ofFn]; simp_rw [ce, xor_not_xor, Bool.not_not]; rfl
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Converting a circuit to ACNFTree preserves evaluation. -/
theorem toACNFTree_eval (c : Circuit Basis.unboundedAON N 1 G) (x : BitString N) :
    c.toACNFTree.eval x = (c.eval x) 0 := by
  simp only [toACNFTree, eval, Gate.eval, Basis.unboundedAON]
  -- The output gate is c.outputs 0
  -- toACNFTree builds children with pol = true ^^ negated k = !negated k
  rcases hop : (c.outputs 0).op with _ | _
  · -- AND output gate
    simp only [AONOp.eval, ACNFTree.eval]
    rw [ACNFTree.evalAll_ofFn]; simp_rw [wireToACNFTree_eval, Bool.true_xor, Bool.not_not]; rfl
  · -- OR output gate
    simp only [AONOp.eval, ACNFTree.eval]
    rw [ACNFTree.evalAny_ofFn]; simp_rw [wireToACNFTree_eval, Bool.true_xor, Bool.not_not]; rfl

/-! ## Circuit to ACNFTree: depth bound -/

/-- The ACNFTree tree for a wire has depth at most the wire's depth. -/
theorem wireToACNFTree_depth_le (c : Circuit Basis.unboundedAON N 1 G)
    (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNFTree w pol).depth ≤ c.wireDepth w := by
  conv_lhs => unfold wireToACNFTree
  split
  · -- Primary input
    rename_i h; simp [wireDepth_lt c w h, ACNFTree.depth]
  · -- Gate wire
    rename_i h
    have hG : w.val - N < G := by omega
    conv_rhs => rw [wireDepth_ge c w h]
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      simp only [hop, ACNFTree.depth]
    all_goals (
      apply Nat.add_le_add_left
      exact ACNFTree.depthList_ofFn_le _ _ _ fun k =>
        wireToACNFTree_depth_le c ((c.gates ⟨w.val - N, hG⟩).inputs k) _)
termination_by w.val
decreasing_by
  all_goals (
    have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
    have : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
    omega)

/-- The ACNFTree tree for a circuit has depth at most the circuit's depth. -/
theorem toACNFTree_depth_le (c : Circuit Basis.unboundedAON N 1 G) :
    c.toACNFTree.depth ≤ c.depth := by
  simp only [toACNFTree, depth]
  rcases (c.outputs 0).op with _ | _ <;>
    simp only [ACNFTree.depth] <;>
    exact Nat.add_le_add_left
      (ACNFTree.depthList_ofFn_le _ _ _ fun k =>
        wireToACNFTree_depth_le c ((c.outputs 0).inputs k) _) 1

/-! ## Normalization composition -/

/-- The normalized ACNFTree tree preserves evaluation. -/
theorem toACNFTree_normalize_eval (c : Circuit Basis.unboundedAON N 1 G)
    (x : BitString N) :
    c.toACNFTree.normalize.eval x = (c.eval x) 0 := by
  rw [ACNFTree.normalize_eval, toACNFTree_eval]

/-- The normalized ACNFTree tree has depth at most the circuit's depth. -/
theorem toACNFTree_normalize_depth_le (c : Circuit Basis.unboundedAON N 1 G) :
    c.toACNFTree.normalize.depth ≤ c.depth :=
  Nat.le_trans (ACNFTree.normalize_depth_le c.toACNFTree) (toACNFTree_depth_le c)

/-- The normalized ACNFTree tree is alternating. -/
theorem toACNFTree_normalize_isAlternating (c : Circuit Basis.unboundedAON N 1 G) :
    c.toACNFTree.normalize.isAlternating = true :=
  ACNFTree.normalize_isAlternating c.toACNFTree

/-! ## Leaf count bounds -/

private theorem foldl_max_le_elem (n : Nat) (f : Fin n → Nat) (i : Fin n) :
    f i ≤ Fin.foldl n (fun acc k => max acc (f k)) 0 := by
  induction n with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    by_cases hi : (i : Nat) < n
    · exact Nat.le_trans (ih (fun j => f j.castSucc) ⟨i, hi⟩) (Nat.le_max_left _ _)
    · have : i = Fin.last n := by ext; simp [Fin.val_last]; omega
      rw [this]; exact Nat.le_max_right _ _

/-- The fan-in of internal gate `i` is at most `maxFanIn`. -/
private theorem gate_fanIn_le_maxFanIn {B : Basis} (c : Circuit B N 1 G) (i : Fin G) :
    (c.gates i).fanIn ≤ c.maxFanIn := by
  simp only [maxFanIn]
  exact Nat.le_trans (foldl_max_le_elem G (fun i => (c.gates i).fanIn) i) (Nat.le_max_left _ _)

/-- The fan-in of the output gate is at most `maxFanIn`. -/
private theorem output_fanIn_le_maxFanIn {B : Basis} (c : Circuit B N 1 G) :
    (c.outputs 0).fanIn ≤ c.maxFanIn := by
  simp only [maxFanIn]
  exact Nat.le_max_right _ _

private theorem foldl_sum_le (n : Nat) (f : Fin n → Nat) (bound : Nat)
    (h : ∀ k, f k ≤ bound) :
    Fin.foldl n (fun acc k => acc + f k) 0 ≤ n * bound := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Nat.zero_add, ACNFTree.foldl_add_init]
    calc f 0 + Fin.foldl n (fun acc k => acc + f k.succ) 0
        ≤ bound + n * bound :=
          Nat.add_le_add (h 0) (ih (fun k => f k.succ) (fun k => h k.succ))
      _ = (n + 1) * bound := by rw [Nat.succ_mul]; omega


/-- The ACNFTree tree for a wire has at most `maxFanIn ^ wireDepth` leaves. -/
theorem wireToACNFTree_leafCount_le (c : Circuit Basis.unboundedAON N 1 G)
    (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNFTree w pol).leafCount ≤ c.maxFanIn ^ c.wireDepth w := by
  conv_lhs => unfold wireToACNFTree
  split
  · -- Primary input: leafCount = 1 = maxFanIn ^ 0
    rename_i h; simp [wireDepth_lt c w h, ACNFTree.leafCount]
  · -- Gate wire
    rename_i h
    have hG : w.val - N < G := by omega
    conv_rhs => rw [wireDepth_ge c w h]
    -- IH for each child
    have lc_ih : ∀ k : Fin (c.gates ⟨w.val - N, hG⟩).fanIn,
        (c.wireToACNFTree ((c.gates ⟨w.val - N, hG⟩).inputs k)
          (pol ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).leafCount ≤
        c.maxFanIn ^ c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k) :=
      fun k => wireToACNFTree_leafCount_le c _ _
    -- Reduce the match on (op, pol) — all branches give same leafCount structure
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      (simp only [hop]; simp only [ACNFTree.leafCount]; rw [ACNFTree.leafCountList_ofFn])
    -- All goals: foldl sum ≤ maxFanIn ^ (1 + foldl max)
    all_goals (
      set D := Fin.foldl (c.gates ⟨w.val - N, hG⟩).fanIn
            (fun acc k => max acc (c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k))) 0
      have hD : ∀ k, c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k) ≤ D :=
        fun k => foldl_max_le_elem _
          (fun j => c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs j)) k
      by_cases hM : c.maxFanIn = 0
      · -- maxFanIn = 0 implies all fanIns = 0, so Fin fanIn is empty
        have : (c.gates ⟨w.val - N, hG⟩).fanIn = 0 := by
          have := gate_fanIn_le_maxFanIn c ⟨w.val - N, hG⟩; omega
        simp [this, Fin.foldl_zero]
      · have hM_pos : 0 < c.maxFanIn := Nat.pos_of_ne_zero hM
        have hbound : ∀ k : Fin (c.gates ⟨w.val - N, hG⟩).fanIn,
            (c.wireToACNFTree ((c.gates ⟨w.val - N, hG⟩).inputs k)
              (_ ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).leafCount ≤
            c.maxFanIn ^ D :=
          fun k => Nat.le_trans (lc_ih k) (Nat.pow_le_pow_right hM_pos (hD k))
        calc Fin.foldl _ (fun acc k => acc +
                (c.wireToACNFTree ((c.gates ⟨w.val - N, hG⟩).inputs k)
                  (_ ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).leafCount) 0
            ≤ _ * c.maxFanIn ^ D := foldl_sum_le _ _ _ hbound
          _ ≤ c.maxFanIn * c.maxFanIn ^ D :=
              Nat.mul_le_mul_right _ (gate_fanIn_le_maxFanIn c ⟨w.val - N, hG⟩)
          _ = c.maxFanIn ^ (D + 1) := (pow_succ' c.maxFanIn D).symm
          _ = c.maxFanIn ^ (1 + D) := by congr 1; omega)
termination_by w.val
decreasing_by
  all_goals (
    have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
    have : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
    omega)

/-- The ACNFTree tree for a circuit has at most `maxFanIn ^ depth` leaves. -/
theorem toACNFTree_leafCount_le (c : Circuit Basis.unboundedAON N 1 G) :
    c.toACNFTree.leafCount ≤ c.maxFanIn ^ c.depth := by
  simp only [toACNFTree, depth]
  rcases hop : (c.outputs 0).op with _ | _ <;>
    (simp only []; simp only [ACNFTree.leafCount]; rw [ACNFTree.leafCountList_ofFn])
  all_goals (
    set D := Fin.foldl (c.outputs 0).fanIn
          (fun acc k => max acc (c.wireDepth ((c.outputs 0).inputs k))) 0
    have hD : ∀ k, c.wireDepth ((c.outputs 0).inputs k) ≤ D :=
      fun k => foldl_max_le_elem _
        (fun j => c.wireDepth ((c.outputs 0).inputs j)) k
    by_cases hM : c.maxFanIn = 0
    · have : (c.outputs 0).fanIn = 0 := by
        have := output_fanIn_le_maxFanIn c; omega
      simp [this, Fin.foldl_zero]
    · have hM_pos : 0 < c.maxFanIn := Nat.pos_of_ne_zero hM
      have hbound : ∀ k : Fin (c.outputs 0).fanIn,
          (c.wireToACNFTree ((c.outputs 0).inputs k)
            (true ^^ (c.outputs 0).negated k)).leafCount ≤
          c.maxFanIn ^ D :=
        fun k => Nat.le_trans (wireToACNFTree_leafCount_le c _ _)
          (Nat.pow_le_pow_right hM_pos (hD k))
      calc Fin.foldl _ (fun acc k => acc +
              (c.wireToACNFTree ((c.outputs 0).inputs k)
                (true ^^ (c.outputs 0).negated k)).leafCount) 0
          ≤ _ * c.maxFanIn ^ D := foldl_sum_le _ _ _ hbound
        _ ≤ c.maxFanIn * c.maxFanIn ^ D :=
            Nat.mul_le_mul_right _ (output_fanIn_le_maxFanIn c)
        _ = c.maxFanIn ^ (D + 1) := (pow_succ' c.maxFanIn D).symm
        _ = c.maxFanIn ^ (1 + D) := by congr 1; omega)

end Circuit

/-! ## Normalization preserves leaf count -/

namespace ACNFTree

variable {N : Nat}

theorem leafCountList_append (l₁ l₂ : List (ACNFTree N)) :
    leafCount.leafCountList (l₁ ++ l₂) =
    leafCount.leafCountList l₁ + leafCount.leafCountList l₂ := by
  induction l₁ with
  | nil => simp [leafCount.leafCountList]
  | cons c cs ih => simp only [List.cons_append, leafCount.leafCountList, ih]; omega

private theorem normalizeAndFlatten_leafCountList (children : List (ACNFTree N))
    (ih : ∀ c, c ∈ children → c.normalize.leafCount = c.leafCount) :
    leafCount.leafCountList (normalize.normalizeAndFlatten children) =
    leafCount.leafCountList children := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeAndFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [leafCount.leafCountList, hrest, ← hc, hn]
    | and gcs =>
      rw [leafCountList_append, hrest, leafCount.leafCountList, ← hc, hn, leafCount]
    | or cs' =>
      simp only [leafCount.leafCountList, hrest, ← hc, hn]

private theorem normalizeOrFlatten_leafCountList (children : List (ACNFTree N))
    (ih : ∀ c, c ∈ children → c.normalize.leafCount = c.leafCount) :
    leafCount.leafCountList (normalize.normalizeOrFlatten children) =
    leafCount.leafCountList children := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeOrFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [leafCount.leafCountList, hrest, ← hc, hn]
    | and gcs =>
      simp only [leafCount.leafCountList, hrest, ← hc, hn]
    | or cs' =>
      rw [leafCountList_append, hrest, leafCount.leafCountList, ← hc, hn, leafCount]

/-- Normalization preserves the number of leaves. -/
theorem normalize_leafCount : (f : ACNFTree N) → f.normalize.leafCount = f.leafCount
  | .lit _ => rfl
  | .and children => by
    simp only [normalize, leafCount]
    exact normalizeAndFlatten_leafCountList children (fun c hc => normalize_leafCount c)
  | .or children => by
    simp only [normalize, leafCount]
    exact normalizeOrFlatten_leafCountList children (fun c hc => normalize_leafCount c)
termination_by f => sizeOf f
decreasing_by
  all_goals exact sizeOf_lt_and hc

end ACNFTree

/-! ## ACNFTree to indexed ACNF conversion

Mutual conversion functions that transform a raw `ACNFTree` into the
indexed `ACNF` type. For alternating trees, this preserves evaluation,
depth, and leaf count. Non-alternating inputs may hit dummy branches. -/

mutual
/-- Convert a raw tree to an AND-rooted (or literal) ACNF.
For alternating trees where the root is not OR, this preserves semantics. -/
def ACNFTree.toACNFTrue : ACNFTree N → ACNF N true
  | .lit l => .lit l
  | .and children => .and (ACNFTree.toACNFFalseList children)
  | .or _ => .and []

/-- Convert a raw tree to an OR-rooted (or literal) ACNF.
For alternating trees where the root is not AND, this preserves semantics. -/
def ACNFTree.toACNFFalse : ACNFTree N → ACNF N false
  | .lit l => .lit l
  | .or children => .or (ACNFTree.toACNFTrueList children)
  | .and _ => .or []

/-- Convert a list of raw trees to AND-rooted (or literal) ACNFs. -/
def ACNFTree.toACNFTrueList : List (ACNFTree N) → List (ACNF N true)
  | [] => []
  | c :: cs => c.toACNFTrue :: ACNFTree.toACNFTrueList cs

/-- Convert a list of raw trees to OR-rooted (or literal) ACNFs. -/
def ACNFTree.toACNFFalseList : List (ACNFTree N) → List (ACNF N false)
  | [] => []
  | c :: cs => c.toACNFFalse :: ACNFTree.toACNFFalseList cs
end

/-- Convert a raw tree to an indexed ACNF, returning the root polarity. -/
def ACNFTree.toACNF (t : ACNFTree N) : (b : Bool) × ACNF N b :=
  match t with
  | .lit l => ⟨true, .lit l⟩
  | .and _ => ⟨true, t.toACNFTrue⟩
  | .or _ => ⟨false, t.toACNFFalse⟩

/-! ## Conversion correctness: eval -/

mutual
theorem ACNFTree.toACNFTrue_eval (t : ACNFTree N) (halt : t.isAlternating = true)
    (hroot : (t.rootOp != some AONOp.or) = true) (x : BitString N) :
    (t.toACNFTrue).eval x = t.eval x := by
  match t, halt, hroot with
  | .lit _, _, _ => rfl
  | .and children, halt, _ =>
    simp only [ACNFTree.toACNFTrue, ACNF.eval, ACNFTree.eval]
    exact ACNFTree.toACNFFalseList_evalAll children
      (by simp only [ACNFTree.isAlternating] at halt; exact halt) x
  | .or _, _, hroot => simp [ACNFTree.rootOp] at hroot

theorem ACNFTree.toACNFFalse_eval (t : ACNFTree N) (halt : t.isAlternating = true)
    (hroot : (t.rootOp != some AONOp.and) = true) (x : BitString N) :
    (t.toACNFFalse).eval x = t.eval x := by
  match t, halt, hroot with
  | .lit _, _, _ => rfl
  | .or children, halt, _ =>
    simp only [ACNFTree.toACNFFalse, ACNF.eval, ACNFTree.eval]
    exact ACNFTree.toACNFTrueList_evalAny children
      (by simp only [ACNFTree.isAlternating] at halt; exact halt) x
  | .and _, _, hroot => simp [ACNFTree.rootOp] at hroot

theorem ACNFTree.toACNFFalseList_evalAll (cs : List (ACNFTree N))
    (h : ACNFTree.isAlternating.isAlternatingAndList cs = true) (x : BitString N) :
    ACNF.eval.evalAll (ACNFTree.toACNFFalseList cs) x = ACNFTree.eval.evalAll cs x := by
  match cs, h with
  | [], _ => rfl
  | c :: rest, h =>
    simp only [ACNFTree.toACNFFalseList, ACNF.eval.evalAll, ACNFTree.eval.evalAll]
    simp only [ACNFTree.isAlternating.isAlternatingAndList, Bool.and_eq_true] at h
    congr 1
    · exact ACNFTree.toACNFFalse_eval c h.1.2 h.1.1 x
    · exact ACNFTree.toACNFFalseList_evalAll rest h.2 x

theorem ACNFTree.toACNFTrueList_evalAny (cs : List (ACNFTree N))
    (h : ACNFTree.isAlternating.isAlternatingOrList cs = true) (x : BitString N) :
    ACNF.eval.evalAny (ACNFTree.toACNFTrueList cs) x = ACNFTree.eval.evalAny cs x := by
  match cs, h with
  | [], _ => rfl
  | c :: rest, h =>
    simp only [ACNFTree.toACNFTrueList, ACNF.eval.evalAny, ACNFTree.eval.evalAny]
    simp only [ACNFTree.isAlternating.isAlternatingOrList, Bool.and_eq_true] at h
    congr 1
    · exact ACNFTree.toACNFTrue_eval c h.1.2 h.1.1 x
    · exact ACNFTree.toACNFTrueList_evalAny rest h.2 x
end

/-- For alternating trees, conversion to indexed ACNF preserves evaluation. -/
theorem ACNFTree.toACNF_eval (t : ACNFTree N) (h : t.isAlternating = true) (x : BitString N) :
    (t.toACNF).2.eval x = t.eval x := by
  match t, h with
  | .lit _, _ => rfl
  | .and _, h => exact ACNFTree.toACNFTrue_eval _ h (by simp [ACNFTree.rootOp]) x
  | .or _, h => exact ACNFTree.toACNFFalse_eval _ h (by simp [ACNFTree.rootOp]) x

/-! ## Conversion correctness: depth -/

mutual
theorem ACNFTree.toACNFTrue_depth (t : ACNFTree N) (halt : t.isAlternating = true)
    (hroot : (t.rootOp != some AONOp.or) = true) :
    (t.toACNFTrue).depth = t.depth := by
  match t, halt, hroot with
  | .lit _, _, _ => rfl
  | .and children, halt, _ =>
    simp only [ACNFTree.toACNFTrue, ACNF.depth, ACNFTree.depth]
    congr 1
    exact ACNFTree.toACNFFalseList_depthAll children
      (by simp only [ACNFTree.isAlternating] at halt; exact halt)
  | .or _, _, hroot => simp [ACNFTree.rootOp] at hroot

theorem ACNFTree.toACNFFalse_depth (t : ACNFTree N) (halt : t.isAlternating = true)
    (hroot : (t.rootOp != some AONOp.and) = true) :
    (t.toACNFFalse).depth = t.depth := by
  match t, halt, hroot with
  | .lit _, _, _ => rfl
  | .or children, halt, _ =>
    simp only [ACNFTree.toACNFFalse, ACNF.depth, ACNFTree.depth]
    congr 1
    exact ACNFTree.toACNFTrueList_depthAny children
      (by simp only [ACNFTree.isAlternating] at halt; exact halt)
  | .and _, _, hroot => simp [ACNFTree.rootOp] at hroot

theorem ACNFTree.toACNFFalseList_depthAll (cs : List (ACNFTree N))
    (h : ACNFTree.isAlternating.isAlternatingAndList cs = true) :
    ACNF.depth.depthAll (ACNFTree.toACNFFalseList cs) = ACNFTree.depth.depthList cs := by
  match cs, h with
  | [], _ => rfl
  | c :: rest, h =>
    simp only [ACNFTree.toACNFFalseList, ACNF.depth.depthAll, ACNFTree.depth.depthList]
    simp only [ACNFTree.isAlternating.isAlternatingAndList, Bool.and_eq_true] at h
    congr 1
    · exact ACNFTree.toACNFFalse_depth c h.1.2 h.1.1
    · exact ACNFTree.toACNFFalseList_depthAll rest h.2

theorem ACNFTree.toACNFTrueList_depthAny (cs : List (ACNFTree N))
    (h : ACNFTree.isAlternating.isAlternatingOrList cs = true) :
    ACNF.depth.depthAny (ACNFTree.toACNFTrueList cs) = ACNFTree.depth.depthList cs := by
  match cs, h with
  | [], _ => rfl
  | c :: rest, h =>
    simp only [ACNFTree.toACNFTrueList, ACNF.depth.depthAny, ACNFTree.depth.depthList]
    simp only [ACNFTree.isAlternating.isAlternatingOrList, Bool.and_eq_true] at h
    congr 1
    · exact ACNFTree.toACNFTrue_depth c h.1.2 h.1.1
    · exact ACNFTree.toACNFTrueList_depthAny rest h.2
end

/-- For alternating trees, conversion to indexed ACNF preserves depth. -/
theorem ACNFTree.toACNF_depth (t : ACNFTree N) (h : t.isAlternating = true) :
    (t.toACNF).2.depth = t.depth := by
  match t, h with
  | .lit _, _ => rfl
  | .and _, h => exact ACNFTree.toACNFTrue_depth _ h (by simp [ACNFTree.rootOp])
  | .or _, h => exact ACNFTree.toACNFFalse_depth _ h (by simp [ACNFTree.rootOp])

/-! ## Conversion correctness: leaf count -/

mutual
theorem ACNFTree.toACNFTrue_leafCount (t : ACNFTree N) (halt : t.isAlternating = true)
    (hroot : (t.rootOp != some AONOp.or) = true) :
    (t.toACNFTrue).leafCount = t.leafCount := by
  match t, halt, hroot with
  | .lit _, _, _ => rfl
  | .and children, halt, _ =>
    simp only [ACNFTree.toACNFTrue, ACNF.leafCount, ACNFTree.leafCount]
    exact ACNFTree.toACNFFalseList_leafCountAll children
      (by simp only [ACNFTree.isAlternating] at halt; exact halt)
  | .or _, _, hroot => simp [ACNFTree.rootOp] at hroot

theorem ACNFTree.toACNFFalse_leafCount (t : ACNFTree N) (halt : t.isAlternating = true)
    (hroot : (t.rootOp != some AONOp.and) = true) :
    (t.toACNFFalse).leafCount = t.leafCount := by
  match t, halt, hroot with
  | .lit _, _, _ => rfl
  | .or children, halt, _ =>
    simp only [ACNFTree.toACNFFalse, ACNF.leafCount, ACNFTree.leafCount]
    exact ACNFTree.toACNFTrueList_leafCountAny children
      (by simp only [ACNFTree.isAlternating] at halt; exact halt)
  | .and _, _, hroot => simp [ACNFTree.rootOp] at hroot

theorem ACNFTree.toACNFFalseList_leafCountAll (cs : List (ACNFTree N))
    (h : ACNFTree.isAlternating.isAlternatingAndList cs = true) :
    ACNF.leafCount.leafCountAll (ACNFTree.toACNFFalseList cs) =
    ACNFTree.leafCount.leafCountList cs := by
  match cs, h with
  | [], _ => rfl
  | c :: rest, h =>
    simp only [ACNFTree.toACNFFalseList, ACNF.leafCount.leafCountAll,
      ACNFTree.leafCount.leafCountList]
    simp only [ACNFTree.isAlternating.isAlternatingAndList, Bool.and_eq_true] at h
    congr 1
    · exact ACNFTree.toACNFFalse_leafCount c h.1.2 h.1.1
    · exact ACNFTree.toACNFFalseList_leafCountAll rest h.2

theorem ACNFTree.toACNFTrueList_leafCountAny (cs : List (ACNFTree N))
    (h : ACNFTree.isAlternating.isAlternatingOrList cs = true) :
    ACNF.leafCount.leafCountAny (ACNFTree.toACNFTrueList cs) =
    ACNFTree.leafCount.leafCountList cs := by
  match cs, h with
  | [], _ => rfl
  | c :: rest, h =>
    simp only [ACNFTree.toACNFTrueList, ACNF.leafCount.leafCountAny,
      ACNFTree.leafCount.leafCountList]
    simp only [ACNFTree.isAlternating.isAlternatingOrList, Bool.and_eq_true] at h
    congr 1
    · exact ACNFTree.toACNFTrue_leafCount c h.1.2 h.1.1
    · exact ACNFTree.toACNFTrueList_leafCountAny rest h.2
end

/-- For alternating trees, conversion to indexed ACNF preserves leaf count. -/
theorem ACNFTree.toACNF_leafCount (t : ACNFTree N) (h : t.isAlternating = true) :
    (t.toACNF).2.leafCount = t.leafCount := by
  match t, h with
  | .lit _, _ => rfl
  | .and _, h => exact ACNFTree.toACNFTrue_leafCount _ h (by simp [ACNFTree.rootOp])
  | .or _, h => exact ACNFTree.toACNFFalse_leafCount _ h (by simp [ACNFTree.rootOp])

/-! ## ACNF eval helpers for map -/

private theorem ACNF.evalAll_map {α : Type} (f : α → ACNF N false) (l : List α)
    (x : BitString N) :
    ACNF.eval.evalAll (l.map f) x = l.all (fun a => (f a).eval x) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map, ACNF.eval.evalAll, List.all_cons, ih]

private theorem ACNF.evalAny_map {α : Type} (f : α → ACNF N true) (l : List α)
    (x : BitString N) :
    ACNF.eval.evalAny (l.map f) x = l.any (fun a => (f a).eval x) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map, ACNF.eval.evalAny, List.any_cons, ih]

/-! ## ACNF wrappers for CNF/DNF/Circuit conversion -/

-- Note: CNF.toACNF and DNF.toACNF are defined directly in Circ.NF.Defs.

/-- Converting a CNF to ACNF preserves evaluation. -/
theorem CNF.toACNF_eval (φ : CNF N) (x : BitString N) :
    φ.toACNF.eval x = φ.eval x := by
  simp only [CNF.toACNF, ACNF.eval, CNF.eval, ACNF.evalAll_map]
  congr 1; ext clause
  simp only [ACNF.eval, ACNF.evalAny_map, ACNF.eval]

/-- Converting a DNF to ACNF preserves evaluation. -/
theorem DNF.toACNF_eval (φ : DNF N) (x : BitString N) :
    φ.toACNF.eval x = φ.eval x := by
  simp only [DNF.toACNF, ACNF.eval, DNF.eval, ACNF.evalAny_map]
  congr 1; ext term
  simp only [ACNF.eval, ACNF.evalAll_map, ACNF.eval]

namespace Circuit
variable {N G : Nat} [NeZero N]

/-- Convert a single-output unbounded-fan-in AND/OR circuit to a
guaranteed-alternating ACNF tree. The root polarity depends on the output gate. -/
def toACNF (c : Circuit Basis.unboundedAON N 1 G) : (b : Bool) × ACNF N b :=
  c.toACNFTree.normalize.toACNF

/-- Circuit to ACNF preserves evaluation. -/
theorem toACNF_eval (c : Circuit Basis.unboundedAON N 1 G) (x : BitString N) :
    (c.toACNF).2.eval x = (c.eval x) 0 := by
  simp only [toACNF]
  rw [ACNFTree.toACNF_eval _ (toACNFTree_normalize_isAlternating c)]
  exact toACNFTree_normalize_eval c x

/-- The ACNF depth is at most the circuit depth. -/
theorem toACNF_depth_le (c : Circuit Basis.unboundedAON N 1 G) :
    (c.toACNF).2.depth ≤ c.depth := by
  simp only [toACNF]
  rw [ACNFTree.toACNF_depth _ (toACNFTree_normalize_isAlternating c)]
  exact toACNFTree_normalize_depth_le c

/-- The ACNF leaf count is at most `maxFanIn ^ depth`. -/
theorem toACNF_leafCount_le (c : Circuit Basis.unboundedAON N 1 G) :
    (c.toACNF).2.leafCount ≤ c.maxFanIn ^ c.depth := by
  simp only [toACNF]
  rw [ACNFTree.toACNF_leafCount _ (toACNFTree_normalize_isAlternating c)]
  rw [ACNFTree.normalize_leafCount]
  exact toACNFTree_leafCount_le c

end Circuit
