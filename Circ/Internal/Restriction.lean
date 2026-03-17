import Circ.Restriction.Defs

/-! # Internal: Restriction Correctness Proofs

This module proves correctness of applying restrictions to CNF/DNF formulas:

* **Evaluation preservation**: applying a restriction and evaluating on a
  consistent assignment gives the same result as the original formula.
* **Width preservation**: restriction cannot increase formula width.
* **k-CNF/k-DNF preservation**: restriction preserves bounded-width properties.
-/

namespace Restriction

variable {N : Nat}

/-! ## Key lemma: applyLit consistent semantics -/

/-- If `x` is consistent with `ρ` and `ρ.applyLit l = some b`, then `l.eval x = b`. -/
private lemma applyLit_some_eval (ρ : Restriction N) (l : Literal N) (x : BitString N)
    (hc : ρ.Consistent x) (b : Bool) (h : ρ.applyLit l = some b) :
    l.eval x = b := by
  simp only [applyLit] at h
  split at h
  · simp at h
  · next bv hbv =>
    simp only [Option.some.injEq] at h
    have hxv := hc l.var bv hbv
    simp only [Literal.eval, hxv]
    exact h

/-- If `ρ.applyLit l = none`, then the variable is free. -/
private lemma applyLit_none_iff (ρ : Restriction N) (l : Literal N) :
    ρ.applyLit l = none ↔ ρ.assign l.var = none := by
  simp only [applyLit]
  split <;> simp_all

/-! ## Helper: List.any/all pointwise congr with membership -/

private lemma list_any_congr_mem {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any_cons]
    rw [h hd (List.mem_cons.mpr (Or.inl rfl))]
    rw [ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))]

private lemma list_all_congr_mem {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons]
    rw [h hd (List.mem_cons.mpr (Or.inl rfl))]
    rw [ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))]

/-! ## applyClause correctness -/

/-- If `applyClause ρ clause = none` (clause trivially true) and `x` is consistent
with `ρ`, then the clause evaluates to `true` on `x`. -/
theorem applyClause_eval_none (ρ : Restriction N) (clause : List (Literal N))
    (x : BitString N) (hc : ρ.Consistent x)
    (h : ρ.applyClause clause = none) :
    clause.any (fun l => l.eval x) = true := by
  simp only [applyClause] at h
  split at h
  · next htrue =>
    rw [List.any_eq_true]
    simp only [List.any_eq_true, decide_eq_true_eq] at htrue
    obtain ⟨l, hl_mem, hl_eq⟩ := htrue
    exact ⟨l, hl_mem, applyLit_some_eval ρ l x hc true hl_eq⟩
  · simp at h

/-- If `applyClause ρ clause = some clause'` and `x` is consistent with `ρ`,
then `clause'` evaluates the same as `clause` on `x`. -/
theorem applyClause_eval_some (ρ : Restriction N) (clause clause' : List (Literal N))
    (x : BitString N) (hc : ρ.Consistent x)
    (h : ρ.applyClause clause = some clause') :
    clause'.any (fun l => l.eval x) = clause.any (fun l => l.eval x) := by
  simp only [applyClause] at h
  split at h
  · simp at h
  · next hno_true =>
    simp only [Option.some.injEq] at h; subst h
    simp only [List.any_filter]
    simp only [Bool.not_eq_true] at hno_true
    rw [List.any_eq_false] at hno_true
    apply list_any_congr_mem
    intro l hl_mem
    by_cases hfree : applyLit ρ l = none
    · simp [hfree]
    · -- l is fixed; not true by hno_true, must be false
      have hnt := hno_true l hl_mem
      simp only [decide_eq_true_eq] at hnt
      simp only [hfree, decide_false, Bool.false_and]
      cases hab : applyLit ρ l with
      | none => exact absurd hab hfree
      | some b =>
        cases b with
        | true => exact absurd hab hnt
        | false =>
          symm; exact applyLit_some_eval ρ l x hc false hab

/-! ## applyTerm correctness -/

/-- If `applyTerm ρ term = none` (term trivially false) and `x` is consistent
with `ρ`, then the term evaluates to `false` on `x`. -/
theorem applyTerm_eval_none (ρ : Restriction N) (term : List (Literal N))
    (x : BitString N) (hc : ρ.Consistent x)
    (h : ρ.applyTerm term = none) :
    term.all (fun l => l.eval x) = false := by
  simp only [applyTerm] at h
  split at h
  · next hfalse =>
    simp only [List.any_eq_true, decide_eq_true_eq] at hfalse
    obtain ⟨l, hl_mem, hl_eq⟩ := hfalse
    have heval := applyLit_some_eval ρ l x hc false hl_eq
    rw [List.all_eq_false]
    exact ⟨l, hl_mem, by simp [heval]⟩
  · simp at h

/-- If `applyTerm ρ term = some term'` and `x` is consistent with `ρ`,
then `term'` evaluates the same as `term` on `x`. -/
theorem applyTerm_eval_some (ρ : Restriction N) (term term' : List (Literal N))
    (x : BitString N) (hc : ρ.Consistent x)
    (h : ρ.applyTerm term = some term') :
    term'.all (fun l => l.eval x) = term.all (fun l => l.eval x) := by
  simp only [applyTerm] at h
  split at h
  · simp at h
  · next hno_false =>
    simp only [Option.some.injEq] at h; subst h
    simp only [List.all_filter]
    simp only [Bool.not_eq_true] at hno_false
    rw [List.any_eq_false] at hno_false
    apply list_all_congr_mem
    intro l hl_mem
    by_cases hfree : applyLit ρ l = none
    · simp [hfree]
    · -- l is fixed; not false by hno_false, must be true
      have hnf := hno_false l hl_mem
      simp only [decide_eq_true_eq] at hnf
      simp only [hfree, decide_false]
      cases hab : applyLit ρ l with
      | none => exact absurd hab hfree
      | some b =>
        cases b with
        | false => exact absurd hab hnf
        | true =>
          have := applyLit_some_eval ρ l x hc true hab
          simp [this]

/-! ## applyCNF / applyDNF correctness -/

/-- Applying a restriction to a CNF formula preserves evaluation on consistent assignments. -/
theorem applyCNF_eval (ρ : Restriction N) (φ : CNF N) (x : BitString N)
    (hc : ρ.Consistent x) :
    (ρ.applyCNF φ).eval x = φ.eval x := by
  simp only [applyCNF, CNF.eval, List.all_filterMap]
  apply list_all_congr_mem
  intro clause hclause
  cases hc_eq : applyClause ρ clause with
  | none => exact (applyClause_eval_none ρ clause x hc hc_eq).symm
  | some clause' => exact applyClause_eval_some ρ clause clause' x hc hc_eq

/-- Applying a restriction to a DNF formula preserves evaluation on consistent assignments. -/
theorem applyDNF_eval (ρ : Restriction N) (φ : DNF N) (x : BitString N)
    (hc : ρ.Consistent x) :
    (ρ.applyDNF φ).eval x = φ.eval x := by
  simp only [applyDNF, DNF.eval, List.any_filterMap]
  apply list_any_congr_mem
  intro term hterm
  cases ht_eq : applyTerm ρ term with
  | none => exact (applyTerm_eval_none ρ term x hc ht_eq).symm
  | some term' => exact applyTerm_eval_some ρ term term' x hc ht_eq

/-! ## Width preservation -/

/-- `applyClause` either drops a clause or returns a filtered sublist. -/
private lemma applyClause_length_le (ρ : Restriction N) (clause clause' : List (Literal N))
    (h : ρ.applyClause clause = some clause') :
    clause'.length ≤ clause.length := by
  simp only [applyClause] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h
    exact List.length_filter_le _ _

/-- `applyTerm` either drops a term or returns a filtered sublist. -/
private lemma applyTerm_length_le (ρ : Restriction N) (term term' : List (Literal N))
    (h : ρ.applyTerm term = some term') :
    term'.length ≤ term.length := by
  simp only [applyTerm] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h
    exact List.length_filter_le _ _

/-- `foldl (fun acc x => max acc (f x)) init` over mapped list equals
`foldl max init` over `map f l`. -/
private lemma foldl_max_map {l : List β} {f : β → Nat} {init : Nat} :
    l.foldl (fun acc x => max acc (f x)) init = (l.map f).foldl max init := by
  induction l generalizing init with
  | nil => simp [List.foldl, List.map]
  | cons hd tl ih => simp only [List.foldl, List.map]; exact ih

/-- `foldl max init` is monotone in init. -/
private lemma foldl_max_mono_init (l : List Nat) {a b : Nat} (hab : a ≤ b) :
    l.foldl max a ≤ l.foldl max b := by
  induction l generalizing a b with
  | nil => simpa [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih
    exact max_le_max_right _ hab

/-- `foldl max init` is at least `init`. -/
private lemma le_foldl_max (l : List Nat) (init : Nat) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih => simp only [List.foldl]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- Every member is ≤ `foldl max 0`. -/
private lemma mem_le_foldl_max {l : List Nat} {x : Nat} (hx : x ∈ l) :
    x ≤ l.foldl max 0 := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldl]
    cases hx with
    | inl heq =>
      subst heq
      exact Nat.le_trans (le_max_right 0 _) (le_foldl_max _ _)
    | inr hmem =>
      exact Nat.le_trans (ih hmem) (foldl_max_mono_init _ (le_max_left 0 _))

/-- `foldl max 0` is bounded by `bound` when every element is ≤ `bound`. -/
private lemma foldl_max_le_bound (l : List Nat) (bound : Nat)
    (h : ∀ x ∈ l, x ≤ bound) : l.foldl max 0 ≤ bound := by
  suffices ∀ init ≤ bound, l.foldl max init ≤ bound from this 0 (Nat.zero_le _)
  induction l with
  | nil => intro init hinit; simpa [List.foldl]
  | cons hd tl ih =>
    intro init hinit
    simp only [List.foldl]
    exact ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx))) _
      (Nat.max_le.mpr ⟨hinit, h hd (List.mem_cons.mpr (Or.inl rfl))⟩)

/-- Restriction cannot increase CNF width. -/
theorem applyCNF_width_le (ρ : Restriction N) (φ : CNF N) :
    (ρ.applyCNF φ).width ≤ φ.width := by
  simp only [CNF.width, applyCNF, foldl_max_map]
  apply foldl_max_le_bound
  intro n hn
  rw [List.mem_map] at hn
  obtain ⟨clause', hclause', rfl⟩ := hn
  rw [List.mem_filterMap] at hclause'
  obtain ⟨clause, hclause, happ⟩ := hclause'
  exact Nat.le_trans (applyClause_length_le ρ clause clause' happ)
    (mem_le_foldl_max (List.mem_map_of_mem (f := fun c => c.length) hclause))

/-- Restriction cannot increase DNF width. -/
theorem applyDNF_width_le (ρ : Restriction N) (φ : DNF N) :
    (ρ.applyDNF φ).width ≤ φ.width := by
  simp only [DNF.width, applyDNF, foldl_max_map]
  apply foldl_max_le_bound
  intro n hn
  rw [List.mem_map] at hn
  obtain ⟨term', hterm', rfl⟩ := hn
  rw [List.mem_filterMap] at hterm'
  obtain ⟨term, hterm, happ⟩ := hterm'
  exact Nat.le_trans (applyTerm_length_le ρ term term' happ)
    (mem_le_foldl_max (List.mem_map_of_mem (f := fun t => t.length) hterm))

/-! ## k-CNF / k-DNF preservation -/

/-- Restriction preserves k-CNF. -/
theorem applyCNF_isKCNF (ρ : Restriction N) (φ : CNF N) (k : Nat)
    (hk : φ.isKCNF k) :
    (ρ.applyCNF φ).isKCNF k := by
  simp only [CNF.isKCNF, applyCNF]
  intro clause' hmem
  rw [List.mem_filterMap] at hmem
  obtain ⟨clause, hclause, happ⟩ := hmem
  exact Nat.le_trans (applyClause_length_le ρ clause clause' happ) (hk clause hclause)

/-- Restriction preserves k-DNF. -/
theorem applyDNF_isKDNF (ρ : Restriction N) (φ : DNF N) (k : Nat)
    (hk : φ.isKDNF k) :
    (ρ.applyDNF φ).isKDNF k := by
  simp only [DNF.isKDNF, applyDNF]
  intro term' hmem
  rw [List.mem_filterMap] at hmem
  obtain ⟨term, hterm, happ⟩ := hmem
  exact Nat.le_trans (applyTerm_length_le ρ term term' happ) (hk term hterm)

/-! ## Composition lemmas -/

@[simp] theorem compose_assign (ρ₂ ρ₁ : Restriction N) (i : Fin N) :
    (ρ₂.compose ρ₁).assign i = match ρ₁.assign i with
      | some b => some b
      | none => ρ₂.assign i := rfl

theorem compose_freeVars (ρ₂ ρ₁ : Restriction N) :
    (ρ₂.compose ρ₁).freeVars = ρ₁.freeVars ∩ ρ₂.freeVars := by
  ext i
  simp only [freeVars, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    compose_assign]
  constructor
  · intro h; rcases h₁ : ρ₁.assign i with _ | b <;> simp_all
  · intro ⟨h₁, h₂⟩; simp [h₁, h₂]

@[simp] theorem setVar_assign (ρ : Restriction N) (v : Fin N) (b : Bool) (i : Fin N) :
    (ρ.setVar v b).assign i = if i = v then some b else ρ.assign i := rfl

@[simp] theorem freeVar_assign (ρ : Restriction N) (v : Fin N) (i : Fin N) :
    (ρ.freeVar v).assign i = if i = v then none else ρ.assign i := rfl

/-- Setting and then freeing a variable restores the original restriction
(on that variable). -/
theorem freeVar_setVar (ρ : Restriction N) (v : Fin N) (b : Bool) :
    (ρ.setVar v b).freeVar v = ρ.freeVar v := by
  show (⟨_⟩ : Restriction N) = ⟨_⟩; congr 1; funext i
  simp only [freeVar_assign, setVar_assign]; split_ifs <;> rfl

/-- Freeing a variable that is already free is a no-op. -/
theorem freeVar_of_free (ρ : Restriction N) (v : Fin N) (hv : ρ.assign v = none) :
    ρ.freeVar v = ρ := by
  show (⟨_⟩ : Restriction N) = ⟨_⟩; congr 1; funext i
  split_ifs with h
  · subst h; exact hv.symm
  · rfl

/-- Setting a variable and then freeing it gives the original with that variable freed. -/
theorem setVar_freeVar_cancel (ρ : Restriction N) (v : Fin N) (b : Bool) :
    (ρ.setVar v b).freeVar v = ρ.freeVar v := by
  show (⟨_⟩ : Restriction N) = ⟨_⟩; congr 1; funext i
  simp only [setVar_assign, freeVar_assign]; split_ifs <;> rfl

end Restriction
