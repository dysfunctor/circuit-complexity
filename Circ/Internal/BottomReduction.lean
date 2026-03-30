import Circ.Internal.ACNFTree
import Circ.AC0

/-! # Bottom Fan-In Reduction (Step 1 of Parity ∉ AC⁰)

This module formalizes Step 1 of the Furst-Saxe-Sipser / Hastad proof that
parity is not in AC⁰.

Given an ACNFTree of depth ≥ 2, we show that there exists a restriction `ρ`
(leaving `s` variables free) and a new ACNFTree on those free variables with:
1. Correct evaluation (computes the restriction of the original function)
2. Depth at most the original depth
3. All bottom-level gates with fan-in at most `d`

The proof uses the switching lemma: each bottom gate is a 1-CNF (or 1-DNF),
and under a random restriction the gate's restricted function has short minterms
with high probability. A union bound over all bottom gates shows a good
restriction exists. Converting the short-minterm functions to short DNFs/CNFs
and merging them into the tree preserves depth.

## Main definitions

* `ACNFTree.isAllLit` -- whether all children of a node are literals
* `ACNFTree.extractLits` -- extract the literal from each literal child
* `ACNFTree.maxBottomFanIn` -- maximum fan-in of depth-1 subtrees
* `ACNFTree.numBottomGates` -- count of depth-1 subtrees
* `ACNFTree.bottomAndToCNF` -- convert a bottom AND gate to a 1-CNF
* `ACNFTree.bottomOrToDNF` -- convert a bottom OR gate to a 1-DNF
* `DNF.maxTermWidth` -- maximum term width in a DNF

## Main results

* `ACNFTree.extractLits_length_of_isAllLit` -- extractLits preserves length
* `ACNFTree.bottomAndToCNF_width_le` -- bottom AND gates yield width ≤ 1 CNFs
* `exists_short_dnf` -- short minterms imply short DNF exists
* `acnf_bottom_fanin_reduction` -- Step 1: bottom fan-in reduction
-/

open Classical

namespace ACNFTree

variable {N : Nat}

/-! ## Bottom gate predicates and metrics -/

/-- Whether all elements in a list of ACNFTree nodes are literals. -/
def isAllLit : List (ACNFTree N b) → Bool
  | [] => true
  | .lit _ :: cs => isAllLit cs
  | .and _ :: _ => false
  | .or _ :: _ => false

/-- Extract the `Literal` from each literal node in a list.
    Non-literal nodes are skipped (but should not occur when `isAllLit = true`). -/
def extractLits : List (ACNFTree N b) → List (Literal N)
  | [] => []
  | .lit l :: cs => l :: extractLits cs
  | .and _ :: cs => extractLits cs
  | .or _ :: cs => extractLits cs

/-- When all children are literals, `extractLits` has the same length as the
    original list (one literal per child). -/
theorem extractLits_length_of_isAllLit :
    ∀ {b : Bool} {children : List (ACNFTree N b)},
    isAllLit children = true → (extractLits children).length = children.length
  | _, [], _ => by simp [extractLits]
  | _, .lit _ :: cs, h => by
    simp only [extractLits, List.length_cons, Nat.succ.injEq]
    exact extractLits_length_of_isAllLit (by simpa [isAllLit] using h)
  | _, .and _ :: _, h => by simp [isAllLit] at h
  | _, .or _ :: _, h => by simp [isAllLit] at h

/-- The maximum fan-in of bottom-level (depth-1) gates in the tree.

A "bottom gate" is an AND/OR node all of whose children are literals.
For such a node, its fan-in is the number of children. For deeper nodes,
we recurse into children and take the maximum. Literals return 0. -/
def maxBottomFanIn : ACNFTree N b → Nat
  | .lit _ => 0
  | .and children =>
    if isAllLit children then children.length
    else maxBottomFanInList children
  | .or children =>
    if isAllLit children then children.length
    else maxBottomFanInList children
where
  maxBottomFanInList {b' : Bool} : List (ACNFTree N b') → Nat
    | [] => 0
    | c :: cs => max c.maxBottomFanIn (maxBottomFanInList cs)

/-- The number of bottom-level (depth-1) gates in the tree. -/
def numBottomGates : ACNFTree N b → Nat
  | .lit _ => 0
  | .and children =>
    if isAllLit children then 1
    else numBottomGatesList children
  | .or children =>
    if isAllLit children then 1
    else numBottomGatesList children
where
  numBottomGatesList {b' : Bool} : List (ACNFTree N b') → Nat
    | [] => 0
    | c :: cs => c.numBottomGates + numBottomGatesList cs

/-! ## Bottom gate to 1-CNF / 1-DNF conversion -/

/-- Convert a depth-1 AND gate (conjunction of literals) to a 1-CNF.
    The conjunction `l₁ ∧ ⋯ ∧ lₖ` becomes the CNF `(l₁) ∧ (l₂) ∧ ⋯ ∧ (lₖ)`,
    where each clause is a single literal. -/
def bottomAndToCNF (children : List (ACNFTree N false)) : CNF N :=
  ⟨(extractLits children).map (fun l => [l])⟩

/-- A 1-CNF from a bottom AND gate has width at most 1. -/
theorem bottomAndToCNF_width_le (children : List (ACNFTree N false)) :
    (bottomAndToCNF children).width ≤ 1 := by
  simp only [bottomAndToCNF, CNF.width]
  generalize extractLits children = lits
  suffices h : ∀ (init : Nat), init ≤ 1 →
      (lits.map (fun l => [l])).foldl (fun acc c => max acc c.length) init ≤ 1 by
    exact h 0 (by omega)
  induction lits with
  | nil => intro init h; simpa
  | cons l ls ih =>
    intro init h_init
    simp only [List.map_cons, List.foldl_cons, List.length_singleton]
    exact ih (max init 1) (by omega)

/-- The 1-CNF from a bottom AND gate evaluates identically to the AND gate
    when all children are literals. -/
theorem bottomAndToCNF_eval :
    ∀ (children : List (ACNFTree N false)),
    isAllLit children = true →
    (bottomAndToCNF children).eval = (ACNFTree.and children).eval
  | [], _ => by
    funext x
    simp [bottomAndToCNF, CNF.eval, extractLits, ACNFTree.eval, ACNFTree.eval.evalAll]
  | .lit l :: cs, h => by
    funext x
    simp only [bottomAndToCNF, CNF.eval, extractLits, List.map_cons, List.all_cons,
      List.any_cons, List.any_nil, Bool.or_false, ACNFTree.eval, ACNFTree.eval.evalAll]
    congr 1
    exact congr_fun (bottomAndToCNF_eval cs (by simpa [isAllLit] using h)) x
  | .or _ :: _, h => by simp [isAllLit] at h

/-- Convert a depth-1 OR gate (disjunction of literals) to a 1-DNF.
    The disjunction `l₁ ∨ ⋯ ∨ lₖ` becomes the DNF `(l₁) ∨ (l₂) ∨ ⋯ ∨ (lₖ)`. -/
def bottomOrToDNF (children : List (ACNFTree N true)) : DNF N :=
  ⟨(extractLits children).map (fun l => [l])⟩

/-- The 1-DNF from a bottom OR gate evaluates identically to the OR gate
    when all children are literals. -/
theorem bottomOrToDNF_eval :
    ∀ (children : List (ACNFTree N true)),
    isAllLit children = true →
    (bottomOrToDNF children).eval = (ACNFTree.or children).eval
  | [], _ => by
    funext x
    simp [bottomOrToDNF, DNF.eval, extractLits, ACNFTree.eval, ACNFTree.eval.evalAny]
  | .lit l :: cs, h => by
    funext x
    simp only [bottomOrToDNF, DNF.eval, extractLits, List.map_cons, List.any_cons,
      List.all_cons, List.all_nil, Bool.and_true, ACNFTree.eval, ACNFTree.eval.evalAny]
    congr 1
    exact congr_fun (bottomOrToDNF_eval cs (by simpa [isAllLit] using h)) x
  | .and _ :: _, h => by simp [isAllLit] at h

/-- The CNF obtained by negating the 1-DNF from a bottom OR gate has width ≤ 1.
    Each clause in the negated CNF is a single negated literal. -/
theorem bottomOrToDNF_neg_width_le (children : List (ACNFTree N true)) :
    (bottomOrToDNF children).neg.width ≤ 1 := by
  simp only [bottomOrToDNF, DNF.neg, CNF.width, List.map_map, Function.comp_def]
  generalize extractLits children = lits
  suffices h : ∀ (init : Nat), init ≤ 1 →
      (lits.map (fun l => [l].map Literal.neg)).foldl
        (fun acc c => max acc c.length) init ≤ 1 by
    exact h 0 (by omega)
  induction lits with
  | nil => intro init h; simpa
  | cons l ls ih =>
    intro init h_init
    simp only [List.map_cons, List.foldl_cons]
    exact ih (max init 1) (by omega)

end ACNFTree

/-! ## DNF term width -/

/-- The maximum term width (number of literals per term) in a DNF formula.
    Returns 0 for the empty DNF. -/
def DNF.maxTermWidth (φ : DNF N) : Nat :=
  φ.terms.foldl (fun acc t => max acc t.length) 0

/-! ## Short minterms imply short normal form -/

section ShortNormalForm

variable {M : Nat}

/-- Convert a restriction to a DNF term: for each fixed variable `i` with
    `ρ(i) = some b`, include the literal `⟨i, b⟩`. -/
noncomputable def Restriction.toTerm (ρ : Restriction M) : List (Literal M) :=
  ρ.support.toList.map (fun i => ⟨i, (ρ i).getD false⟩)

/-- The term length equals the restriction length. -/
theorem Restriction.toTerm_length (ρ : Restriction M) :
    ρ.toTerm.length = ρ.length := by
  simp [Restriction.toTerm, Restriction.length, Finset.length_toList]

/-- The DNF whose terms are the minterms of `f`, each converted to a term. -/
noncomputable def mintermsDNF (f : BitString M → Bool) : DNF M :=
  ⟨(Finset.univ.filter (Restriction.IsMinterm f)).toList.map Restriction.toTerm⟩

/-- Helper: foldl of max over a mapped list is bounded when each element is bounded. -/
private theorem foldl_max_map_le {α : Type*} (l : List α) (g : α → Nat) (bound : Nat)
    (h : ∀ x ∈ l, g x ≤ bound) :
    l.foldl (fun acc x => max acc (g x)) 0 ≤ bound := by
  suffices ∀ init, init ≤ bound → l.foldl (fun acc x => max acc (g x)) init ≤ bound by
    exact this 0 (Nat.zero_le _)
  induction l with
  | nil => intro init h; simpa
  | cons a rest ih =>
    intro init h_init
    simp only [List.foldl_cons]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (max init (g a)) (Nat.max_le.mpr ⟨h_init, h a List.mem_cons_self⟩)

/-- Each minterm `ρ` has `ρ.length ≤ maxMintermLength f` by definition of `Finset.sup`. -/
private theorem minterm_length_le (f : BitString M → Bool) (ρ : Restriction M)
    (hρ : ρ ∈ Finset.univ.filter (Restriction.IsMinterm f)) :
    ρ.length ≤ Restriction.maxMintermLength f :=
  Finset.le_sup (f := Restriction.length) hρ

/-- Each term in the minterm DNF has width at most `maxMintermLength f`.

    Each term comes from a minterm `ρ` with `ρ.length ≤ maxMintermLength f`
    (by definition of `Finset.sup`), and term length = `ρ.length`. -/
theorem mintermsDNF_maxTermWidth_le (f : BitString M → Bool) :
    (mintermsDNF f).maxTermWidth ≤ Restriction.maxMintermLength f := by
  simp only [mintermsDNF, DNF.maxTermWidth, List.foldl_map]
  apply foldl_max_map_le
  intro ρ hρ
  rw [Restriction.toTerm_length]
  exact minterm_length_le f ρ (Finset.mem_toList.mp hρ)

/-- **Minterm completeness**: a Boolean function is the disjunction of its minterms.

    For each `x`, `(mintermsDNF f).eval x = f x`. The two directions:
    - (←) If `f(x) = true`, among all restrictions consistent with `x` that make
      `f` constantly true, one with minimum length is a minterm covering `x`.
    - (→) If a minterm's term covers `x`, then `x` agrees with the minterm on all
      fixed variables, and since the minterm makes `f` constantly true, `f(x) = true`.

    The (←) direction uses the well-ordering principle on `Restriction.length`. -/
private theorem toTerm_all_eval {ρ : Restriction M} {x : BitString M}
    (h : ρ.toTerm.all (fun l => l.eval x) = true) :
    ∀ i : Fin M, ¬Restriction.isFree ρ i → ρ i = some (x i) := by
  intro i hi
  simp only [Restriction.toTerm, List.all_map, List.all_eq_true, Finset.mem_toList] at h
  have hi_supp : i ∈ ρ.support := Finset.mem_compl.mpr (by simp [Restriction.freeVars, hi])
  specialize h i hi_supp
  simp only [Function.comp_def, Literal.eval] at h
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (by rwa [Restriction.isFree] at hi)
  rw [hb] at h ⊢
  simp only [Option.getD_some] at h
  cases b <;> simp_all

private theorem fillIn_eq_of_agrees {ρ : Restriction M} {x : BitString M}
    (h : ∀ i : Fin M, ¬Restriction.isFree ρ i → ρ i = some (x i)) :
    ρ.fillIn (fun v => x v.val) = x := by
  funext i
  unfold Restriction.fillIn
  split
  · next b hb =>
    have := h i (by simp [Restriction.isFree, hb])
    rw [hb] at this; exact Option.some_injective _ this
  · rfl

private theorem eval_true_of_minterm_agrees {ρ : Restriction M} {f : BitString M → Bool}
    {x : BitString M} (hconst : ρ.MakesConstTrue f)
    (hagree : ∀ i : Fin M, ¬Restriction.isFree ρ i → ρ i = some (x i)) :
    f x = true := by
  have hfill := fillIn_eq_of_agrees hagree
  unfold Restriction.MakesConstTrue Restriction.restrict at hconst
  specialize hconst ((fun v => x v.val) ∘ ρ.freeVarEquiv)
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hconst
  rw [hfill] at hconst
  exact hconst

private theorem exists_minterm_consistent (f : BitString M → Bool) (x : BitString M)
    (hfx : f x = true) :
    ∃ ρ : Restriction M, Restriction.IsMinterm f ρ ∧
      ∀ i : Fin M, ¬Restriction.isFree ρ i → ρ i = some (x i) := by
  -- S: restrictions consistent with x that make f constantly true
  let S := Finset.univ.filter (fun ρ : Restriction M =>
    ρ.MakesConstTrue f ∧ ∀ i : Fin M, ¬Restriction.isFree ρ i → ρ i = some (x i))
  -- The full restriction ρ_full(i) = some (x i) is in S
  have hne : S.Nonempty := by
    refine ⟨fun i => some (x i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · -- MakesConstTrue: all variables are fixed, so fillIn always returns x
      intro z
      unfold Restriction.restrict
      have : Restriction.fillIn (fun i => some (x i))
          (z ∘ (Restriction.freeVarEquiv (fun i => some (x i))).symm) = x := by
        funext j; exact Restriction.fillIn_fixed (show (fun i => some (x i)) j = some (x j) from rfl) _
      rw [this, hfx]
    · intro i _; rfl
  -- Pick ρ₀ with minimum length in S
  obtain ⟨ρ₀, hρ₀_mem, hρ₀_min⟩ := S.exists_min_image Restriction.length hne
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hρ₀_mem
  refine ⟨ρ₀, ⟨hρ₀_mem.1, ?_⟩, hρ₀_mem.2⟩
  -- Show minimality: unfixing any fixed variable breaks MakesConstTrue
  intro i hi hcontra
  have h_in_S : ρ₀.unfix i ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontra, ?_⟩
    intro j hj
    simp only [Restriction.isFree, Restriction.unfix, Function.update_apply] at hj ⊢
    split_ifs at hj ⊢ with hji
    · exact absurd rfl hj
    · exact hρ₀_mem.2 j hj
  have h_lt : Restriction.length (ρ₀.unfix i) < Restriction.length ρ₀ := by
    simp only [Restriction.length]
    apply Finset.card_lt_card
    constructor
    · intro j hj
      simp only [Restriction.support, Finset.mem_compl, Restriction.freeVars,
        Finset.mem_filter, Finset.mem_univ, true_and, Restriction.isFree,
        Restriction.unfix, Function.update_apply] at hj ⊢
      intro hfree; apply hj; split_ifs
      · rfl
      · exact hfree
    · intro hsub
      have hmem : i ∈ ρ₀.support := by
        simp only [Restriction.support, Finset.mem_compl, Restriction.freeVars,
          Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
      have := hsub hmem
      simp only [Restriction.support, Finset.mem_compl, Restriction.freeVars,
        Finset.mem_filter, Finset.mem_univ, true_and, Restriction.isFree,
        Restriction.unfix, Function.update_self] at this
      exact absurd trivial this
  exact absurd (hρ₀_min _ h_in_S) (not_le.mpr h_lt)

private theorem agrees_toTerm_all_eval {ρ : Restriction M} {x : BitString M}
    (h : ∀ i : Fin M, ¬Restriction.isFree ρ i → ρ i = some (x i)) :
    ρ.toTerm.all (fun l => l.eval x) = true := by
  simp only [Restriction.toTerm, List.all_map, List.all_eq_true, Finset.mem_toList,
    Function.comp_def, Literal.eval]
  intro i hi
  have hi_nfree : ¬Restriction.isFree ρ i := by
    simp only [Restriction.support, Finset.mem_compl, Restriction.freeVars,
      Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  have := h i hi_nfree
  rw [this]; simp only [Option.getD_some]
  cases x i <;> simp

theorem mintermsDNF_eval (f : BitString M → Bool) :
    (mintermsDNF f).eval = f := by
  funext x
  simp only [mintermsDNF, DNF.eval, List.any_map, Function.comp_def]
  set a := (Finset.univ.filter (Restriction.IsMinterm f)).toList.any
      (fun ρ => ρ.toTerm.all (fun l => l.eval x))
  suffices key : (a = true) ↔ (f x = true) by
    cases ha : a <;> cases hf : f x <;> simp_all
  constructor
  · -- Forward: some minterm's term matches x → f x = true
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨ρ, hρ_mem, hρ_match⟩ := h
    rw [Finset.mem_toList, Finset.mem_filter] at hρ_mem
    exact eval_true_of_minterm_agrees hρ_mem.2.1 (toTerm_all_eval hρ_match)
  · -- Backward: f x = true → some minterm's term matches x
    intro hfx
    rw [List.any_eq_true]
    obtain ⟨ρ, hρ_minterm, hρ_agree⟩ := exists_minterm_consistent f x hfx
    exact ⟨ρ, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρ_minterm⟩),
      agrees_toTerm_all_eval hρ_agree⟩

/-- If every minterm of `f` has length at most `d`, then `f` can be expressed
    as a DNF with term width at most `d`.

    Uses `mintermsDNF`: the DNF whose terms are the minterms of `f`. -/
theorem exists_short_dnf (f : BitString M → Bool) (d : Nat)
    (h : Restriction.maxMintermLength f ≤ d) :
    ∃ (φ : DNF M), φ.maxTermWidth ≤ d ∧ φ.eval = f :=
  ⟨mintermsDNF f, le_trans (mintermsDNF_maxTermWidth_le f) h, mintermsDNF_eval f⟩

/-- Dual: if every minterm of `¬f` has length at most `d`, then `f` can be
    expressed as a CNF with clause width at most `d`.

    Applies `exists_short_dnf` to `¬f`, then negates the DNF via De Morgan. -/
theorem exists_short_cnf (f : BitString M → Bool) (d : Nat)
    (h : Restriction.maxMintermLength (fun x => !(f x)) ≤ d) :
    ∃ (φ : CNF M), φ.width ≤ d ∧ φ.eval = f := by
  obtain ⟨ψ, hwidth, heval⟩ := exists_short_dnf (fun x => !(f x)) d h
  refine ⟨ψ.neg, ?_, ?_⟩
  · -- CNF.width of DNF.neg = DNF.maxTermWidth (negating preserves lengths)
    simp only [DNF.neg, CNF.width, List.foldl_map]
    convert hwidth using 1
    simp only [DNF.maxTermWidth]
    congr 1; funext acc t; congr 1
    exact List.length_map (f := Literal.neg) (as := t)
  · funext x
    have hx := congr_fun heval x
    simp only at hx
    rw [DNF.eval_neg, hx, Bool.not_not]

end ShortNormalForm

/-! ## Good restriction predicate -/

namespace ACNFTree

variable {N : Nat}

/-- A restriction `ρ` is "good" for tree `t` with target fan-in `d` if every
    bottom gate's restricted evaluation function has `maxMintermLength ≤ d`.

    - For literals: vacuously true (no bottom gate).
    - For bottom gates (AND/OR with all-literal children): the restricted
      function has short minterms.
    - For non-bottom gates: recursively, all children satisfy the condition. -/
noncomputable def IsGoodRestriction (ρ : Restriction N) (d : Nat) :
    ACNFTree N b → Prop
  | .lit _ => True
  | .and children =>
    if isAllLit children then
      Restriction.maxMintermLength (Restriction.restrict ρ (ACNFTree.and children).eval) ≤ d
    else
      isGoodList ρ d children
  | .or children =>
    if isAllLit children then
      -- For OR bottom gates the switching lemma applies to the negation (a 1-CNF),
      -- so we require short minterms of the negated restricted function.
      Restriction.maxMintermLength
        (fun x => !(Restriction.restrict ρ (ACNFTree.or children).eval x)) ≤ d
    else
      isGoodList ρ d children
where
  isGoodList {b' : Bool} (ρ : Restriction N) (d : Nat) :
      List (ACNFTree N b') → Prop
    | [] => True
    | c :: cs => c.IsGoodRestriction ρ d ∧ isGoodList ρ d cs

/-! ## Sub-lemmas for Step 1 -/

/-- The bad set for tree `t`: restrictions in `R^s` that are NOT good.
    This is a Finset because `IsGoodRestriction` is decidable (classically). -/
noncomputable def badSetTree (t : ACNFTree N b) (s d : Nat) :
    Finset (Restriction N) :=
  (Restriction.sRestrictions N s).filter (fun ρ => ¬ t.IsGoodRestriction ρ d)

/-- For a bottom AND gate, the bad set is contained in `badRestrictions` of
    its 1-CNF representation. -/
private theorem badSetTree_and_bottom_sub (children : List (ACNFTree N false))
    (s d : Nat) (h_allLit : isAllLit children = true) :
    badSetTree (.and children) s d ⊆
    badRestrictions (bottomAndToCNF children) s d := by
  intro ρ hρ
  simp only [badSetTree, Finset.mem_filter] at hρ
  simp only [IsGoodRestriction, h_allLit, ↓reduceIte, not_le] at hρ
  simp only [badRestrictions, Finset.mem_filter]
  exact ⟨hρ.1, by rw [bottomAndToCNF_eval children h_allLit]; exact hρ.2⟩

/-- For a bottom OR gate, the bad set is contained in `badRestrictions` of
    the negated 1-DNF (which is a 1-CNF). -/
private theorem badSetTree_or_bottom_sub (children : List (ACNFTree N true))
    (s d : Nat) (h_allLit : isAllLit children = true) :
    badSetTree (.or children) s d ⊆
    badRestrictions (bottomOrToDNF children).neg s d := by
  intro ρ hρ
  simp only [badSetTree, Finset.mem_filter] at hρ
  simp only [IsGoodRestriction, h_allLit, ↓reduceIte, not_le] at hρ
  simp only [badRestrictions, Finset.mem_filter]
  refine ⟨hρ.1, ?_⟩
  -- Show the restricted negated-DNF function = negation of restricted OR-gate function
  suffices heq : Restriction.maxMintermLength (ρ.restrict (bottomOrToDNF children).neg.eval) =
      Restriction.maxMintermLength
        (fun x => !(ρ.restrict (ACNFTree.or children).eval x)) by
    rw [heq]; exact hρ.2
  congr 1; funext x
  simp only [Restriction.restrict, Function.comp_def, DNF.eval_neg,
    bottomOrToDNF_eval children h_allLit]

/-- Helper for `badSetTree_card_bound`: the list case (union bound over children).
    Parameterized by an induction hypothesis `ih_tree` for each child. -/
private theorem badSetTree_list_card_bound [NeZero N] {b' : Bool}
    (cs : List (ACNFTree N b')) (s d : Nat)
    (ih_tree : ∀ c : ACNFTree N b', c ∈ cs →
      (c.badSetTree s d).card * N ^ d ≤
      c.numBottomGates * (Restriction.sRestrictions N s).card * (8 * s) ^ d) :
    ((Restriction.sRestrictions N s).filter
      (fun ρ => ¬ IsGoodRestriction.isGoodList ρ d cs)).card * N ^ d ≤
    numBottomGates.numBottomGatesList cs *
      (Restriction.sRestrictions N s).card * (8 * s) ^ d := by
  induction cs with
  | nil =>
    simp [IsGoodRestriction.isGoodList]
  | cons c cs ih =>
    -- ¬(P ∧ Q) means ¬P ∨ ¬Q, so bad set ⊆ bad(c) ∪ bad(cs)
    have hsub : (Restriction.sRestrictions N s).filter
          (fun ρ => ¬ IsGoodRestriction.isGoodList ρ d (c :: cs)) ⊆
        c.badSetTree s d ∪
        (Restriction.sRestrictions N s).filter
          (fun ρ => ¬ IsGoodRestriction.isGoodList ρ d cs) := by
      intro ρ hρ
      simp only [IsGoodRestriction.isGoodList, not_and_or, Finset.mem_filter] at hρ
      simp only [Finset.mem_union, badSetTree, Finset.mem_filter]
      rcases hρ.2 with h | h
      · left; exact ⟨hρ.1, h⟩
      · right; exact ⟨hρ.1, h⟩
    have ih_cs := ih (fun c' hc' => ih_tree c' (List.mem_cons_of_mem _ hc'))
    have ih_c := ih_tree c List.mem_cons_self
    set bad_c := c.badSetTree s d
    set bad_cs := (Restriction.sRestrictions N s).filter
      (fun ρ => ¬ IsGoodRestriction.isGoodList ρ d cs)
    -- |bad_union| ≤ |bad_c| + |bad_cs| (Finset.card_union_le)
    have hcard_le : (bad_c ∪ bad_cs).card ≤ bad_c.card + bad_cs.card :=
      bad_c.card_union_le bad_cs
    calc ((Restriction.sRestrictions N s).filter
            (fun ρ => ¬ IsGoodRestriction.isGoodList ρ d (c :: cs))).card * N ^ d
        ≤ (bad_c ∪ bad_cs).card * N ^ d :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ ≤ (bad_c.card + bad_cs.card) * N ^ d :=
          Nat.mul_le_mul_right _ hcard_le
      _ = bad_c.card * N ^ d + bad_cs.card * N ^ d :=
          Nat.add_mul _ _ _
      _ ≤ c.numBottomGates * (Restriction.sRestrictions N s).card * (8 * s) ^ d +
          numBottomGates.numBottomGatesList cs *
            (Restriction.sRestrictions N s).card * (8 * s) ^ d :=
          Nat.add_le_add ih_c ih_cs
      _ = numBottomGates.numBottomGatesList (c :: cs) *
            (Restriction.sRestrictions N s).card * (8 * s) ^ d := by
          simp only [numBottomGates.numBottomGatesList, Nat.add_mul, Nat.add_mul]

/-- Helper: the switching lemma bound for a single bottom gate, using width ≤ 1. -/
private theorem switching_lemma_width_one [NeZero N] (φ : CNF N) (s d : Nat)
    (hd_le_s : d ≤ s) (h2sN : 2 * s ≤ N)
    (hwidth : φ.width ≤ 1) :
    (badRestrictions φ s d).card * N ^ d ≤
    (Restriction.sRestrictions N s).card * (8 * s) ^ d := by
  calc (badRestrictions φ s d).card * N ^ d
      ≤ (Restriction.sRestrictions N s).card * (8 * φ.width * s) ^ d :=
        switching_lemma _ s d hd_le_s h2sN
    _ ≤ (Restriction.sRestrictions N s).card * (8 * 1 * s) ^ d := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ hwidth)) _
    _ = (Restriction.sRestrictions N s).card * (8 * s) ^ d := by
        simp

/-- **Key cardinality bound** (switching lemma + structural induction).

For each bottom AND gate (a 1-CNF of width 1), the switching lemma gives
`|bad_gate| · N^d ≤ |R^s| · (8s)^d`. For each bottom OR gate, the switching
lemma is applied to the negation (also a 1-CNF of width 1). For non-bottom
nodes, the bad set is the union of children's bad sets, bounded by the sum
of their cardinalities.

Depends on: `switching_lemma`, `bottomAndToCNF_eval`, `bottomOrToDNF_eval`,
`DNF.eval_neg`. -/
theorem badSetTree_card_bound [NeZero N] :
    ∀ {b : Bool} (t : ACNFTree N b) (s d : Nat),
    d ≤ s → 2 * s ≤ N →
    (badSetTree t s d).card * N ^ d ≤
    t.numBottomGates * (Restriction.sRestrictions N s).card * (8 * s) ^ d
  | _, .lit _, s, d, _, _ => by
    simp [badSetTree, IsGoodRestriction, numBottomGates]
  | _, .and children, s, d, hd_le_s, h2sN => by
    simp only [numBottomGates]
    split
    case isTrue h_allLit =>
      -- Bottom AND: 1-CNF of width ≤ 1
      calc (badSetTree (.and children) s d).card * N ^ d
          ≤ (badRestrictions (bottomAndToCNF children) s d).card * N ^ d :=
            Nat.mul_le_mul_right _ (Finset.card_le_card
              (badSetTree_and_bottom_sub children s d h_allLit))
        _ ≤ (Restriction.sRestrictions N s).card * (8 * s) ^ d :=
            switching_lemma_width_one _ s d hd_le_s h2sN (bottomAndToCNF_width_le _)
        _ = 1 * (Restriction.sRestrictions N s).card * (8 * s) ^ d := by
            simp
    case isFalse h_not =>
      -- Non-bottom AND
      have hf : isAllLit children = false := Bool.eq_false_iff.mpr h_not
      have heq : badSetTree (.and children) s d =
          (Restriction.sRestrictions N s).filter
            (fun ρ => ¬ IsGoodRestriction.isGoodList ρ d children) := by
        simp [badSetTree, IsGoodRestriction, hf]
      rw [heq]
      exact badSetTree_list_card_bound children s d
        (fun c hc => badSetTree_card_bound c s d hd_le_s h2sN)
  | _, .or children, s, d, hd_le_s, h2sN => by
    simp only [numBottomGates]
    split
    case isTrue h_allLit =>
      -- Bottom OR: negate to get 1-CNF of width ≤ 1
      calc (badSetTree (.or children) s d).card * N ^ d
          ≤ (badRestrictions (bottomOrToDNF children).neg s d).card * N ^ d :=
            Nat.mul_le_mul_right _ (Finset.card_le_card
              (badSetTree_or_bottom_sub children s d h_allLit))
        _ ≤ (Restriction.sRestrictions N s).card * (8 * s) ^ d :=
            switching_lemma_width_one _ s d hd_le_s h2sN (bottomOrToDNF_neg_width_le _)
        _ = 1 * (Restriction.sRestrictions N s).card * (8 * s) ^ d := by
            simp
    case isFalse h_not =>
      -- Non-bottom OR
      have hf : isAllLit children = false := Bool.eq_false_iff.mpr h_not
      have heq : badSetTree (.or children) s d =
          (Restriction.sRestrictions N s).filter
            (fun ρ => ¬ IsGoodRestriction.isGoodList ρ d children) := by
        simp [badSetTree, IsGoodRestriction, hf]
      rw [heq]
      exact badSetTree_list_card_bound children s d
        (fun c hc => badSetTree_card_bound c s d hd_le_s h2sN)

theorem exists_good_restriction [NeZero N] {b : Bool}
    (t : ACNFTree N b) (s d : Nat)
    (hd_le_s : d ≤ s) (h2sN : 2 * s ≤ N)
    (hunion : t.numBottomGates * (8 * s) ^ d < N ^ d) :
    ∃ (ρ : Restriction N), ρ.numFree = s ∧ t.IsGoodRestriction ρ d := by
  -- The cardinality bound from the switching lemma
  have hbound := badSetTree_card_bound t s d hd_le_s h2sN
  have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNd_pos : 0 < N ^ d := Nat.pos_of_ne_zero (by
    intro h; simp [Nat.pow_eq_zero] at h; exact absurd h.1 (NeZero.ne N))
  set R := Restriction.sRestrictions N s with hR_def
  -- |R^s| > 0: there exist restrictions with exactly s free variables (since s ≤ N)
  have hR_pos : 0 < R.card := by
    rw [Finset.card_pos]
    -- Witness: fix variables ≥ s, leave variables < s free
    use fun i => if i.val < s then none else some false
    simp only [hR_def, Restriction.sRestrictions, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Restriction.numFree Restriction.freeVars Restriction.isFree
    convert_to Fintype.card {i : Fin N // i.val < s} = s
    · rw [Fintype.card_subtype]; congr 1; ext i; simp [ite_eq_left_iff]
    · exact Fintype.card_fin_lt_of_le (by omega)
  -- |badSet| < |R^s| by combining hbound with hunion
  have hbad_lt : (badSetTree t s d).card < R.card := by
    by_contra hge
    push_neg at hge
    -- |R| ≤ |bad| and |bad| * N^d ≤ numBottom * |R| * (8s)^d
    -- so |R| * N^d ≤ |bad| * N^d ≤ numBottom * |R| * (8s)^d
    have h1 : R.card * N ^ d ≤ t.numBottomGates * R.card * (8 * s) ^ d :=
      le_trans (Nat.mul_le_mul_right _ hge) hbound
    -- But hunion: numBottom * (8s)^d < N^d, so numBottom * |R| * (8s)^d < |R| * N^d
    have h2 : t.numBottomGates * R.card * (8 * s) ^ d < R.card * N ^ d := by
      calc t.numBottomGates * R.card * (8 * s) ^ d
          = R.card * (t.numBottomGates * (8 * s) ^ d) := by
            simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ < R.card * N ^ d := Nat.mul_lt_mul_of_pos_left hunion hR_pos
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  -- badSet ⊂ R^s, so ∃ ρ ∈ R^s with ρ ∉ badSet
  have hbad_sub : badSetTree t s d ⊆ R := Finset.filter_subset _ _
  have hss : badSetTree t s d ⊂ R := by
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hbad_sub, by intro heq; exact absurd hbad_lt (by rw [heq]; exact lt_irrefl _)⟩
  obtain ⟨ρ, hρR, hρnbad⟩ := Finset.exists_of_ssubset hss
  refine ⟨ρ, ?_, ?_⟩
  · -- ρ ∈ sRestrictions N s → numFree ρ = s
    have := hρR
    simp only [hR_def, Restriction.sRestrictions, Finset.mem_filter] at this
    exact this.2
  · -- ρ ∉ badSet → IsGoodRestriction ρ d t
    simp only [badSetTree, Finset.mem_filter, not_and, not_not] at hρnbad
    exact hρnbad hρR

/-! ### Eval congruence for rebuilt child lists -/

/-- If two child lists have the same length and agree pointwise on eval
    (up to applying a function `g` to the input), then `evalAll` agrees. -/
private theorem evalAll_congr {M : Nat}
    (cs : List (ACNFTree N false)) (cs' : List (ACNFTree M false))
    (g : BitString M → BitString N)
    (hlen : cs'.length = cs.length)
    (heval : ∀ i (hi : i < cs.length) (hi' : i < cs'.length),
      ∀ x, (cs'.get ⟨i, hi'⟩).eval x = (cs.get ⟨i, hi⟩).eval (g x)) :
    ∀ x, ACNFTree.eval.evalAll cs' x = ACNFTree.eval.evalAll cs (g x) := by
  induction cs generalizing cs' with
  | nil =>
    cases cs' with
    | nil => intro x; simp [ACNFTree.eval.evalAll]
    | cons => simp at hlen
  | cons c ct ih =>
    match cs', hlen with
    | c' :: ct', hlen =>
      intro x
      simp only [ACNFTree.eval.evalAll]
      have hlen' : ct'.length = ct.length := by simpa using hlen
      have h0 : c'.eval x = c.eval (g x) :=
        heval 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) x
      have ih' := ih ct' hlen' (fun i hi hi' x =>
        heval (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi') x) x
      rw [h0, ih']

/-- Dual of `evalAll_congr` for `evalAny`. -/
private theorem evalAny_congr {M : Nat}
    (cs : List (ACNFTree N true)) (cs' : List (ACNFTree M true))
    (g : BitString M → BitString N)
    (hlen : cs'.length = cs.length)
    (heval : ∀ i (hi : i < cs.length) (hi' : i < cs'.length),
      ∀ x, (cs'.get ⟨i, hi'⟩).eval x = (cs.get ⟨i, hi⟩).eval (g x)) :
    ∀ x, ACNFTree.eval.evalAny cs' x = ACNFTree.eval.evalAny cs (g x) := by
  induction cs generalizing cs' with
  | nil =>
    cases cs' with
    | nil => intro x; simp [ACNFTree.eval.evalAny]
    | cons => simp at hlen
  | cons c ct ih =>
    match cs', hlen with
    | c' :: ct', hlen =>
      intro x
      simp only [ACNFTree.eval.evalAny]
      have hlen' : ct'.length = ct.length := by simpa using hlen
      have h0 : c'.eval x = c.eval (g x) :=
        heval 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) x
      have ih' := ih ct' hlen' (fun i hi hi' x =>
        heval (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi') x) x
      rw [h0, ih']

/-- `maxBottomFanInList` is bounded by `d` when every element has
    `maxBottomFanIn ≤ d`. -/
private theorem maxBottomFanInList_le_of_forall {M : Nat} {b' : Bool}
    (cs : List (ACNFTree M b')) (d : Nat)
    (h : ∀ c ∈ cs, c.maxBottomFanIn ≤ d) :
    maxBottomFanIn.maxBottomFanInList cs ≤ d := by
  induction cs with
  | nil => unfold maxBottomFanIn.maxBottomFanInList; omega
  | cons c ct ih =>
    unfold maxBottomFanIn.maxBottomFanInList
    exact Nat.max_le.mpr ⟨h c List.mem_cons_self,
      ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))⟩

/-! ### Tree reconstruction from a good restriction

Given a restriction `ρ` that is good for tree `t`, construct a new ACNFTree
on `ρ.numFree` variables that computes the restricted function, preserves
depth, and has all bottom gates with fan-in at most `d`.

The construction proceeds by structural recursion on `t`:
- **Literals** `lit ⟨i, pol⟩`: depth 0, contradicts `hd_depth ≥ 2`.
- **Bottom AND gates** (`and children` with `isAllLit children`): The good
  restriction guarantees `maxMintermLength ≤ d` for the restricted function.
  By `exists_short_dnf`, obtain a `d`-DNF and convert via `DNF.toACNFTree`.
- **Bottom OR gates**: Dual, using `exists_short_cnf` and `CNF.toACNFTree`.
- **Non-bottom gates**: Recurse into children.

Depends on: `exists_short_dnf`, `exists_short_cnf`. -/

private theorem depthList_lit :
    ∀ {b : Bool} {children : List (ACNFTree N b)},
    isAllLit children = true → depth.depthList children = 0
  | _, [], _ => by unfold depth.depthList; rfl
  | _, .lit _ :: cs, h => by
    unfold depth.depthList ACNFTree.depth
    simp only [Nat.max_eq_zero_iff]
    exact ⟨trivial, depthList_lit (by simpa [isAllLit] using h)⟩
  | _, .and _ :: _, h => by simp [isAllLit] at h
  | _, .or _ :: _, h => by simp [isAllLit] at h

/-- Bottom AND gate depth = 1 (all children are literals of depth 0). -/
private theorem bottom_and_depth_eq_one (children : List (ACNFTree N false))
    (h : isAllLit children = true) :
    (ACNFTree.and children).depth = 1 := by
  unfold ACNFTree.depth; rw [depthList_lit h]

/-- Bottom OR gate depth = 1 (all children are literals of depth 0). -/
private theorem bottom_or_depth_eq_one (children : List (ACNFTree N true))
    (h : isAllLit children = true) :
    (ACNFTree.or children).depth = 1 := by
  unfold ACNFTree.depth; rw [depthList_lit h]

/-- If `isAllLit children = false`, at least one child is non-literal (depth ≥ 1),
    so `depthList children ≥ 1`. -/
private theorem depthList_pos_of_not_allLit :
    ∀ {b : Bool} {children : List (ACNFTree N b)},
    isAllLit children = false → 1 ≤ depth.depthList children
  | _, [], h => by simp [isAllLit] at h
  | _, .lit _ :: cs, h => by
    unfold depth.depthList ACNFTree.depth
    have := depthList_pos_of_not_allLit (by simpa [isAllLit] using h)
    omega
  | _, .and cs :: _, _ => by
    unfold depth.depthList ACNFTree.depth
    omega
  | _, .or cs :: _, _ => by
    unfold depth.depthList ACNFTree.depth
    omega

/-- Rebuild a literal: remap free variable or produce a constant.

For literal `⟨i, pol⟩`:
- If `ρ(i) = none` (free): produce `lit ⟨freeVarEquiv⁻¹(i), pol⟩` (depth 0).
- If `ρ(i) = some v`: the literal evaluates to the constant `if pol then v else !v`.
  Use `and []` (true) or `or []` (false) when the type index matches,
  or `or [and []]` / `and [or []]` for the cross case (depth 2, fan-in 0). -/
private noncomputable def rebuildLiteral {N : Nat} {b : Bool}
    (l : Literal N) (ρ : Restriction N) : ACNFTree ρ.numFree b :=
  match h : ρ l.var with
  | none => .lit ⟨ρ.freeVarEquiv.symm ⟨l.var, h⟩, l.polarity⟩
  | some v =>
    let val := if l.polarity then v else !v
    match b, val with
    | true, true => .and []
    | true, false => .and [.or []]
    | false, false => .or []
    | false, true => .or [.and []]

private theorem rebuildLiteral_eval {N : Nat} {b : Bool}
    (l : Literal N) (ρ : Restriction N) :
    ∀ x, (rebuildLiteral l ρ : ACNFTree ρ.numFree b).eval x =
      Restriction.restrict ρ (fun y => (ACNFTree.lit l : ACNFTree N b).eval y) x := by
  intro x; unfold rebuildLiteral; split
  next h_free =>
    -- Free variable: lit ⟨freeVarEquiv⁻¹(i), pol⟩ evaluates to the remapped literal
    simp only [ACNFTree.eval, Literal.eval, Restriction.restrict, Function.comp_def]
    rw [Restriction.fillIn_free ⟨l.var, h_free⟩]
  next v h_fixed =>
    -- Fixed variable: constant tree matches the constant literal value
    simp only [Restriction.restrict, Function.comp_def, ACNFTree.eval, Literal.eval]
    rw [Restriction.fillIn_fixed h_fixed]
    cases b <;> cases l.polarity <;> cases v <;>
      simp [ACNFTree.eval, ACNFTree.eval.evalAll, ACNFTree.eval.evalAny]

private theorem rebuildLiteral_depth {N : Nat} {b : Bool}
    (l : Literal N) (ρ : Restriction N) :
    (rebuildLiteral l ρ : ACNFTree ρ.numFree b).depth ≤ 2 := by
  unfold rebuildLiteral
  split
  · -- free variable: lit has depth 0
    simp [ACNFTree.depth]
  · -- fixed variable
    next v _ =>
    cases b <;> cases l.polarity <;> cases v <;>
      simp [ACNFTree.depth, depth.depthList]

private theorem rebuildLiteral_maxBottomFanIn {N : Nat} {b : Bool}
    (l : Literal N) (ρ : Restriction N) :
    (rebuildLiteral l ρ : ACNFTree ρ.numFree b).maxBottomFanIn ≤ 0 := by
  unfold rebuildLiteral
  split
  · simp [maxBottomFanIn]
  · next v _ =>
    cases b <;> cases l.polarity <;> cases v <;>
      simp [maxBottomFanIn, isAllLit, maxBottomFanIn.maxBottomFanInList]

/-- Remap a single literal through restriction `ρ`:
    free variables are remapped, fixed variables are dropped. -/
private noncomputable def remapLit (l : Literal N) (ρ : Restriction N) :
    Option (Literal ρ.numFree) :=
  if h : ρ.isFree l.var then
    some ⟨ρ.freeVarEquiv.symm ⟨l.var, h⟩, l.polarity⟩
  else
    none

/-- Filter a literal list to free-variable literals and remap their variable
    indices through `ρ.freeVarEquiv`. -/
private noncomputable def remapFreeLits (lits : List (Literal N)) (ρ : Restriction N) :
    List (Literal ρ.numFree) :=
  lits.filterMap (remapLit · ρ)

/-- When no fixed literal is falsified by ρ, the restricted AND of literals equals
    the conjunction of the remapped free literals. -/
private theorem restrictedAnd_eq_remappedLits
    (lits : List (Literal N)) (ρ : Restriction N)
    (h_no_false : ∀ l ∈ lits, ∀ v, ρ l.var = some v →
      (if l.polarity then v else !v) = true) :
    ∀ x : BitString ρ.numFree,
    lits.all (fun l => l.eval (ρ.fillIn (x ∘ ρ.freeVarEquiv.symm))) =
    (remapFreeLits lits ρ).all (fun l => l.eval x) := by
  intro x
  induction lits with
  | nil => simp [remapFreeLits, List.filterMap]
  | cons l ls ih =>
    simp only [List.all_cons, remapFreeLits, List.filterMap_cons, remapLit]
    have ih' := ih (fun l' hl' v hv => h_no_false l' (List.mem_cons_of_mem _ hl') v hv)
    simp only [remapFreeLits] at ih'
    by_cases h_free : ρ.isFree l.var
    · -- Free variable: literal appears in remapFreeLits
      simp only [h_free, dite_true, List.all_cons]
      congr 1
      · simp only [Literal.eval, Function.comp_def]
        rw [Restriction.fillIn_free ⟨l.var, h_free⟩]
    · -- Fixed variable: evaluates to true, so dropped without effect
      simp only [h_free, dite_false]
      have ⟨v, hv⟩ : ∃ v, ρ l.var = some v := by
        cases h : ρ l.var with
        | none => exact absurd (show ρ.isFree l.var from h) h_free
        | some v => exact ⟨v, rfl⟩
      have h_true : l.eval (ρ.fillIn (x ∘ ρ.freeVarEquiv.symm)) = true := by
        simp only [Literal.eval, Restriction.fillIn_fixed hv]
        exact h_no_false l List.mem_cons_self v hv
      rw [h_true, Bool.true_and]
      exact ih'

/-- `evalAll` of an all-literal list equals `List.all` of `extractLits`. -/
private theorem evalAll_eq_all_extractLits :
    ∀ {children : List (ACNFTree N false)},
    isAllLit children = true →
    ∀ x, ACNFTree.eval.evalAll children x =
      (extractLits children).all (fun l => l.eval x)
  | [], _, _ => by simp [ACNFTree.eval.evalAll, extractLits]
  | .lit l :: cs, h, x => by
    simp only [ACNFTree.eval.evalAll, ACNFTree.eval, extractLits, List.all_cons]
    congr 1
    exact evalAll_eq_all_extractLits (by simpa [isAllLit] using h) x
  | .or _ :: _, h, _ => by simp [isAllLit] at h

/-- `evalAll` of a mapped literal list equals `List.all` of the literals. -/
private theorem evalAll_map_lit (lits : List (Literal M)) :
    ∀ x, ACNFTree.eval.evalAll (lits.map fun l => ACNFTree.lit l) x =
      lits.all (fun l => l.eval x) := by
  intro x
  induction lits with
  | nil => simp [List.map, ACNFTree.eval.evalAll]
  | cons l ls ih =>
    simp only [List.map, ACNFTree.eval.evalAll, ACNFTree.eval, List.all_cons]
    exact congr_arg _ ih

private theorem depthList_map_lit {M : Nat} {b : Bool} (lits : List (Literal M)) :
    depth.depthList (lits.map fun l => (ACNFTree.lit l : ACNFTree M b)) = 0 := by
  induction lits with
  | nil => simp [List.map, depth.depthList]
  | cons l ls ih =>
    simp only [List.map]; unfold depth.depthList ACNFTree.depth; simp [ih]

private theorem isAllLit_map_lit {M : Nat} {b : Bool} (lits : List (Literal M)) :
    isAllLit (lits.map fun l => (ACNFTree.lit l : ACNFTree M b)) = true := by
  induction lits with
  | nil => simp [List.map, isAllLit]
  | cons l ls ih => simp only [List.map]; unfold isAllLit; exact ih

/-- `List.all` commutes with `List.dedup`: membership is preserved. -/
private theorem all_dedup_eq_all {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Bool) :
    l.dedup.all p = l.all p := by
  have h : l.dedup.all p = true ↔ l.all p = true := by
    simp [List.all_eq_true, List.mem_dedup]
  cases h1 : l.all p <;> cases h2 : l.dedup.all p <;> try rfl
  · exact absurd (h.mp h2) (by simp [h1])
  · exact absurd (h.mpr h1) (by simp [h2])

/-- In a satisfiable literal list, the deduped list has distinct variables.
    No two literals can have the same variable with different polarities
    since one would always be false. -/
private theorem dedup_nodup_vars_of_sat {M : Nat} {lits : List (Literal M)}
    (h : ∃ x₀, lits.all (fun l => l.eval x₀) = true) :
    (lits.dedup.map Literal.var).Nodup := by
  obtain ⟨x₀, hx₀⟩ := h
  rw [List.all_eq_true] at hx₀
  apply List.Nodup.map_on
  · intro a ha b hb hab
    have ha_true := hx₀ a (List.mem_dedup.mp ha)
    have hb_true := hx₀ b (List.mem_dedup.mp hb)
    simp only [Literal.eval] at ha_true hb_true
    rw [hab] at ha_true
    have h_pol_eq : a.polarity = b.polarity := by
      cases ha_p : a.polarity <;> cases hb_p : b.polarity <;> simp_all
    cases a; cases b; simp_all
  · exact List.nodup_dedup lits

/-- For literals with distinct variables, the list length is bounded by
    `maxMintermLength` of the conjunction.

    The proof constructs a minterm of `lits.all` that fixes each variable
    appearing in `lits` to the value satisfying its literal. This restriction
    has length = `lits.length` and is a minterm, giving the bound. -/
private theorem lits_length_le_maxMintermLength_conj {M : Nat} (lits : List (Literal M))
    (h_nodup_vars : (lits.map Literal.var).Nodup) :
    lits.length ≤ Restriction.maxMintermLength
      (fun x => lits.all (fun l => l.eval x)) := by
  -- Construct restriction σ that fixes each literal's variable to satisfy it
  let σ : Restriction M := fun v =>
    (lits.find? (fun l => decide (l.var = v))).map (fun l => l.polarity)
  -- Key helper: find? returns the unique literal with matching var
  have h_find : ∀ l ∈ lits, lits.find? (fun l' => decide (l'.var = l.var)) = some l := by
    intro l hl
    rw [List.find?_eq_some_iff_append]
    refine ⟨by simp, ?_⟩
    obtain ⟨as, bs, h_split⟩ := List.append_of_mem hl
    refine ⟨as, bs, h_split, fun a ha => ?_⟩
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    intro h_var_eq
    have ha_mem : a ∈ lits := h_split ▸ List.mem_append_left _ ha
    have h_eq_lit := List.inj_on_of_nodup_map h_nodup_vars ha_mem hl h_var_eq
    subst h_eq_lit
    have h_nd := h_split ▸ h_nodup_vars.of_map
    rw [List.nodup_append] at h_nd
    exact h_nd.2.2 a ha a List.mem_cons_self rfl
  -- Key property: for l ∈ lits, σ fixes l.var to l.polarity
  have h_fixes : ∀ l ∈ lits, σ l.var = some l.polarity := by
    intro l hl; show (lits.find? _).map _ = _; rw [h_find l hl]; rfl
  -- σ is free exactly when no literal has that variable
  have h_free_iff : ∀ v : Fin M, σ.isFree v ↔ ∀ l ∈ lits, l.var ≠ v := by
    intro v; unfold Restriction.isFree; show (lits.find? _).map _ = none ↔ _
    rw [Option.map_eq_none_iff]
    constructor
    · intro hfind l hl heq
      have := h_find l hl; rw [heq] at this; simp [hfind] at this
    · intro h_none_mem
      rw [List.find?_eq_none]
      intro l hl
      simp only [decide_eq_true_eq]
      exact h_none_mem l hl
  -- σ.support = image of Literal.var over lits
  have h_support : σ.support = (lits.map Literal.var).toFinset := by
    ext v; simp only [Restriction.support, Finset.mem_compl, Restriction.freeVars,
      Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
    rw [h_free_iff]
    push_neg; rfl
  -- σ.length = lits.length
  have h_len : σ.length = lits.length := by
    unfold Restriction.length; rw [h_support]
    rw [List.toFinset_card_of_nodup h_nodup_vars, List.length_map]
  -- σ makes the conjunction constantly true
  have h_const : σ.MakesConstTrue (fun x => lits.all (fun l => l.eval x)) := by
    intro x
    simp only [Restriction.restrict, List.all_eq_true]
    intro l hl
    simp only [Literal.eval, Restriction.fillIn_fixed (h_fixes l hl)]
    cases l.polarity <;> simp
  -- σ is minimal: unfixing any fixed variable i breaks constant-true
  have h_min : ∀ i : Fin M, ¬σ.isFree i →
      ¬(σ.unfix i).MakesConstTrue (fun x => lits.all (fun l => l.eval x)) := by
    intro i h_not_free h_abs
    rw [h_free_iff] at h_not_free; push_neg at h_not_free
    obtain ⟨l, hl, hlv⟩ := h_not_free
    simp only [Restriction.MakesConstTrue, Restriction.restrict,
      List.all_eq_true] at h_abs
    have h_unfix_free : (σ.unfix i).isFree i := by
      unfold Restriction.isFree Restriction.unfix; simp [Function.update]
    let x₀ : BitString (σ.unfix i).numFree :=
      Function.update (fun _ => true)
        ((σ.unfix i).freeVarEquiv.symm ⟨i, h_unfix_free⟩) (!l.polarity)
    have h_eval_l : l.eval ((σ.unfix i).fillIn (x₀ ∘ (σ.unfix i).freeVarEquiv.symm)) = false := by
      simp only [Literal.eval, hlv, Restriction.fillIn_free ⟨i, h_unfix_free⟩, Function.comp_def,
        x₀, Function.update_self]
      cases l.polarity <;> simp
    have := h_abs x₀ l hl
    rw [h_eval_l] at this
    exact absurd this Bool.false_ne_true
  -- Combine: σ is a minterm
  have h_minterm : Restriction.IsMinterm (fun x => lits.all (fun l => l.eval x)) σ :=
    ⟨h_const, h_min⟩
  rw [← h_len]
  exact Finset.le_sup (f := Restriction.length)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_minterm⟩)

/-- For a satisfiable conjunction of literals, the dedup length is bounded by
    `maxMintermLength` of the conjunction. -/
private theorem dedup_length_le_maxMintermLength_conj {M : Nat}
    {lits : List (Literal M)}
    (h_sat : ∃ x₀, lits.all (fun l => l.eval x₀) = true) :
    lits.dedup.length ≤ Restriction.maxMintermLength
      (fun x => lits.all (fun l => l.eval x)) := by
  have h_nodup := dedup_nodup_vars_of_sat h_sat
  have h_bound := lits_length_le_maxMintermLength_conj lits.dedup h_nodup
  have h_eq : (fun x => lits.dedup.all (fun l => l.eval x)) =
      (fun x => lits.all (fun l => l.eval x)) := by
    funext x; exact all_dedup_eq_all lits _
  rw [h_eq] at h_bound
  exact h_bound

/-- `and [or []]` (the constantly false tree) has bottom fan-in 0. -/
private theorem maxBottomFanIn_and_or_empty {N : Nat} :
    (ACNFTree.and [ACNFTree.or ([] : List (ACNFTree N true))]).maxBottomFanIn = 0 := by
  unfold maxBottomFanIn isAllLit maxBottomFanIn.maxBottomFanInList
    maxBottomFanIn isAllLit maxBottomFanIn.maxBottomFanInList; rfl

/-- `or [and []]` (the constantly true tree) has bottom fan-in 0. -/
private theorem maxBottomFanIn_or_and_empty {N : Nat} :
    (ACNFTree.or [ACNFTree.and ([] : List (ACNFTree N false))]).maxBottomFanIn = 0 := by
  unfold maxBottomFanIn isAllLit maxBottomFanIn.maxBottomFanInList
    maxBottomFanIn isAllLit maxBottomFanIn.maxBottomFanInList; rfl

/-- Rebuild a bottom AND gate.

Direct construction: filter the literals to free variables, remap indices.
If some fixed literal is falsified, the AND is constantly false.
If the conjunction of free literals is unsatisfiable (contradictory polarities),
the AND is also constantly false. Otherwise, use the deduped free literals. -/
private theorem rebuild_bottom_and [NeZero N]
    (children : List (ACNFTree N false)) (ρ : Restriction N) (d : Nat)
    (h_allLit : isAllLit children = true)
    (hgood : Restriction.maxMintermLength
      (Restriction.restrict ρ (ACNFTree.and children).eval) ≤ d) :
    ∃ (c' : ACNFTree ρ.numFree true),
      (∀ x, c'.eval x = Restriction.restrict ρ
        (fun y => (ACNFTree.and children).eval y) x) ∧
      c'.depth ≤ (ACNFTree.and children).depth + 1 ∧
      c'.maxBottomFanIn ≤ d ∧
      1 ≤ c'.depth := by
  by_cases h_all_sat : ∀ l ∈ extractLits children, ∀ v, ρ l.var = some v →
      (if l.polarity then v else !v) = true
  · -- No falsified literal
    let freeLits := remapFreeLits (extractLits children) ρ
    by_cases h_sat : ∃ x₀, freeLits.all (fun l => l.eval x₀) = true
    · -- Satisfiable: use deduped conjunction of remapped free literals
      refine ⟨.and (freeLits.dedup.map fun l => .lit l), ?_, ?_, ?_⟩
      · -- Eval
        intro x
        simp only [ACNFTree.eval, Restriction.restrict, Function.comp_def]
        rw [evalAll_map_lit, all_dedup_eq_all, evalAll_eq_all_extractLits h_allLit]
        exact (restrictedAnd_eq_remappedLits (extractLits children) ρ h_all_sat x).symm
      · -- Depth
        rw [bottom_and_depth_eq_one children h_allLit]
        unfold ACNFTree.depth; rw [depthList_map_lit]; omega
      · constructor
        · -- Fan-in: dedup.length ≤ maxMintermLength(g) ≤ d
          unfold maxBottomFanIn; rw [isAllLit_map_lit]; simp only [↓reduceIte, List.length_map]
          have h_bound := dedup_length_le_maxMintermLength_conj h_sat
          have h_func_eq : (fun x => freeLits.all (fun l => l.eval x)) =
              ρ.restrict (ACNFTree.and children).eval := by
            funext x
            simp only [Restriction.restrict, ACNFTree.eval]
            rw [evalAll_eq_all_extractLits h_allLit,
                restrictedAnd_eq_remappedLits (extractLits children) ρ h_all_sat x]
          rw [h_func_eq] at h_bound
          exact le_trans h_bound hgood
        · unfold ACNFTree.depth; omega
    · -- Unsatisfiable: conjunction of free literals is always false
      have h_false : ∀ x, freeLits.all (fun l => l.eval x) = false := by
        intro x; cases h : freeLits.all (fun l => l.eval x) with
        | false => rfl
        | true => exact absurd ⟨x, h⟩ h_sat
      refine ⟨.and [.or []], ?_, ?_, ?_⟩
      · intro x
        simp only [ACNFTree.eval, ACNFTree.eval.evalAll, ACNFTree.eval.evalAny,
          Bool.false_and, Restriction.restrict]
        symm
        rw [evalAll_eq_all_extractLits h_allLit,
            restrictedAnd_eq_remappedLits (extractLits children) ρ h_all_sat x]
        exact h_false x
      · rw [bottom_and_depth_eq_one children h_allLit]
        simp only [ACNFTree.depth, depth.depthList]; omega
      · exact ⟨maxBottomFanIn_and_or_empty ▸ Nat.zero_le _,
              by simp only [ACNFTree.depth, depth.depthList]; omega⟩
  · -- Some literal is falsified: AND is constantly false.
    -- Use `and [or []]`: evaluates to false, depth 2, fan-in 0.
    push_neg at h_all_sat
    obtain ⟨l, hl_mem, v, hv, h_false⟩ := h_all_sat
    refine ⟨.and [.or []], ?_, ?_, ?_⟩
    · -- Eval: and [or []] = false = restricted (and children)
      intro x
      simp only [ACNFTree.eval, ACNFTree.eval.evalAll, ACNFTree.eval.evalAny,
        Bool.false_and, Restriction.restrict, Function.comp_def]
      -- The restricted AND is false because the falsified literal is in children
      rw [evalAll_eq_all_extractLits h_allLit]
      symm; rw [List.all_eq_false]
      exact ⟨l, hl_mem, by
        simp only [Literal.eval, Restriction.fillIn_fixed hv]
        revert h_false; cases l.polarity <;> simp_all⟩
    · -- Depth: and [or []] has depth 2 ≤ 1 + 1
      rw [bottom_and_depth_eq_one children h_allLit]
      simp only [ACNFTree.depth, depth.depthList]; omega
    · exact ⟨maxBottomFanIn_and_or_empty ▸ Nat.zero_le _,
            by simp only [ACNFTree.depth, depth.depthList]; omega⟩

/-- `evalAny` of an all-literal list equals `List.any` of `extractLits`. -/
private theorem evalAny_eq_any_extractLits :
    ∀ {children : List (ACNFTree N true)},
    isAllLit children = true →
    ∀ x, ACNFTree.eval.evalAny children x =
      (extractLits children).any (fun l => l.eval x)
  | [], _, _ => by simp [ACNFTree.eval.evalAny, extractLits]
  | .lit l :: cs, h, x => by
    simp only [ACNFTree.eval.evalAny, ACNFTree.eval, extractLits, List.any_cons]
    congr 1
    exact evalAny_eq_any_extractLits (by simpa [isAllLit] using h) x
  | .and _ :: _, h, _ => by simp [isAllLit] at h

/-- `evalAny` of a mapped literal list equals `List.any` of the literals. -/
private theorem evalAny_map_lit (lits : List (Literal M)) :
    ∀ x, ACNFTree.eval.evalAny (lits.map fun l => ACNFTree.lit l) x =
      lits.any (fun l => l.eval x) := by
  intro x; induction lits with
  | nil => simp [List.map, ACNFTree.eval.evalAny]
  | cons l ls ih =>
    simp only [List.map, ACNFTree.eval.evalAny, ACNFTree.eval, List.any_cons]
    exact congr_arg _ ih

/-- Dual of `restrictedAnd_eq_remappedLits`: when no fixed literal is satisfied,
    the restricted OR of literals equals the disjunction of remapped free literals. -/
private theorem restrictedOr_eq_remappedLits
    (lits : List (Literal N)) (ρ : Restriction N)
    (h_no_true : ∀ l ∈ lits, ∀ v, ρ l.var = some v →
      (if l.polarity then v else !v) = false) :
    ∀ x : BitString ρ.numFree,
    lits.any (fun l => l.eval (ρ.fillIn (x ∘ ρ.freeVarEquiv.symm))) =
    (remapFreeLits lits ρ).any (fun l => l.eval x) := by
  intro x
  induction lits with
  | nil => simp [remapFreeLits, List.filterMap]
  | cons l ls ih =>
    simp only [List.any_cons, remapFreeLits, List.filterMap_cons, remapLit]
    have ih' := ih (fun l' hl' v hv => h_no_true l' (List.mem_cons_of_mem _ hl') v hv)
    simp only [remapFreeLits] at ih'
    by_cases h_free : ρ.isFree l.var
    · simp only [h_free, dite_true, List.any_cons]
      congr 1
      · simp only [Literal.eval, Function.comp_def]
        rw [Restriction.fillIn_free ⟨l.var, h_free⟩]
    · simp only [h_free, dite_false]
      have ⟨v, hv⟩ : ∃ v, ρ l.var = some v := by
        cases h : ρ l.var with
        | none => exact absurd (show ρ.isFree l.var from h) h_free
        | some v => exact ⟨v, rfl⟩
      have h_false : l.eval (ρ.fillIn (x ∘ ρ.freeVarEquiv.symm)) = false := by
        simp only [Literal.eval, Restriction.fillIn_fixed hv]
        exact h_no_true l List.mem_cons_self v hv
      rw [h_false, Bool.false_or]
      exact ih'

/-- `List.any` commutes with `List.dedup`: membership is preserved. -/
private theorem any_dedup_eq_any {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Bool) :
    l.dedup.any p = l.any p := by
  cases hp : l.any p with
  | false =>
    rw [List.any_eq_false] at hp ⊢
    intro x hx; exact hp x (List.mem_dedup.mp hx)
  | true =>
    obtain ⟨x, hx, hpx⟩ := List.any_eq_true.mp hp
    exact List.any_eq_true.mpr ⟨x, List.mem_dedup.mpr hx, hpx⟩

/-- In a falsifiable literal list, the deduped list has distinct variables.
    No two literals can be complementary since one would always be true. -/
private theorem dedup_nodup_vars_of_not_taut {M : Nat} {lits : List (Literal M)}
    (h : ∃ x₀, lits.any (fun l => l.eval x₀) = false) :
    (lits.dedup.map Literal.var).Nodup := by
  obtain ⟨x₀, hx₀⟩ := h
  rw [List.any_eq_false] at hx₀
  apply List.Nodup.map_on
  · intro a ha b hb hab
    have ha_false := hx₀ a (List.mem_dedup.mp ha)
    have hb_false := hx₀ b (List.mem_dedup.mp hb)
    simp only [Literal.eval] at ha_false hb_false
    rw [hab] at ha_false
    have h_pol_eq : a.polarity = b.polarity := by
      cases ha_p : a.polarity <;> cases hb_p : b.polarity <;> simp_all
    cases a; cases b; simp_all
  · exact List.nodup_dedup lits

/-- For literals with distinct variables, the list length is bounded by
    `maxMintermLength` of the negated disjunction.

    The proof constructs a minterm of `¬(lits.any)` that fixes each variable
    appearing in `lits` to the value falsifying its literal. This restriction
    has length = `lits.length` and is a minterm, giving the bound via `Finset.sup`. -/
private theorem lits_length_le_maxMintermLength_neg {M : Nat} (lits : List (Literal M))
    (h_nodup_vars : (lits.map Literal.var).Nodup) :
    lits.length ≤ Restriction.maxMintermLength
      (fun x => !(lits.any (fun l => l.eval x))) := by
  -- Construct restriction σ that fixes each literal's variable to falsify it
  let σ : Restriction M := fun v =>
    (lits.find? (fun l => decide (l.var = v))).map (fun l => !l.polarity)
  -- Key helper: find? returns the unique literal with matching var
  have h_find : ∀ l ∈ lits, lits.find? (fun l' => decide (l'.var = l.var)) = some l := by
    intro l hl
    rw [List.find?_eq_some_iff_append]
    refine ⟨by simp, ?_⟩
    obtain ⟨as, bs, h_split⟩ := List.append_of_mem hl
    refine ⟨as, bs, h_split, fun a ha => ?_⟩
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    intro h_var_eq
    have ha_mem : a ∈ lits := h_split ▸ List.mem_append_left _ ha
    have h_eq_lit := List.inj_on_of_nodup_map h_nodup_vars ha_mem hl h_var_eq
    subst h_eq_lit
    have h_nd := h_split ▸ h_nodup_vars.of_map
    rw [List.nodup_append] at h_nd
    exact h_nd.2.2 a ha a List.mem_cons_self rfl
  -- Key property: for l ∈ lits, σ fixes l.var to !l.polarity
  have h_fixes : ∀ l ∈ lits, σ l.var = some (!l.polarity) := by
    intro l hl; show (lits.find? _).map _ = _; rw [h_find l hl]; rfl
  -- σ is free exactly when no literal has that variable
  have h_free_iff : ∀ v : Fin M, σ.isFree v ↔ ∀ l ∈ lits, l.var ≠ v := by
    intro v; unfold Restriction.isFree; show (lits.find? _).map _ = none ↔ _
    rw [Option.map_eq_none_iff]
    constructor
    · intro hfind l hl heq
      have := h_find l hl; rw [heq] at this; simp [hfind] at this
    · intro h_none_mem
      rw [List.find?_eq_none]
      intro l hl
      simp only [decide_eq_true_eq]
      exact h_none_mem l hl
  -- σ.support = image of Literal.var over lits
  have h_support : σ.support = (lits.map Literal.var).toFinset := by
    ext v; simp only [Restriction.support, Finset.mem_compl, Restriction.freeVars,
      Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
    rw [h_free_iff]
    push_neg; rfl
  -- σ.length = lits.length
  have h_len : σ.length = lits.length := by
    unfold Restriction.length; rw [h_support]
    rw [List.toFinset_card_of_nodup h_nodup_vars, List.length_map]
  -- σ makes ¬g constantly true
  have h_const : σ.MakesConstTrue (fun x => !(lits.any (fun l => l.eval x))) := by
    intro x
    simp only [Restriction.restrict, Bool.not_eq_true', List.any_eq_false]
    intro l hl
    simp only [Literal.eval, Restriction.fillIn_fixed (h_fixes l hl)]
    cases l.polarity <;> simp
  -- σ is minimal: unfixing any fixed variable i breaks constant-true
  have h_min : ∀ i : Fin M, ¬σ.isFree i →
      ¬(σ.unfix i).MakesConstTrue (fun x => !(lits.any (fun l => l.eval x))) := by
    intro i h_not_free h_abs
    rw [h_free_iff] at h_not_free; push_neg at h_not_free
    obtain ⟨l, hl, hlv⟩ := h_not_free
    -- After unfixing i = l.var, variable i is free; assign it to satisfy l
    simp only [Restriction.MakesConstTrue, Restriction.restrict, Bool.not_eq_true',
      List.any_eq_false] at h_abs
    -- Variable i is free in σ.unfix i
    have h_unfix_free : (σ.unfix i).isFree i := by
      unfold Restriction.isFree Restriction.unfix; simp [Function.update]
    -- Build x that assigns l.polarity to the free variable slot for i
    let x₀ : BitString (σ.unfix i).numFree :=
      Function.update (fun _ => true) ((σ.unfix i).freeVarEquiv.symm ⟨i, h_unfix_free⟩) l.polarity
    have h_eval_l : l.eval ((σ.unfix i).fillIn (x₀ ∘ (σ.unfix i).freeVarEquiv.symm)) = true := by
      simp only [Literal.eval, hlv, Restriction.fillIn_free ⟨i, h_unfix_free⟩, Function.comp_def,
        x₀, Function.update_self]
      cases l.polarity <;> simp
    exact absurd h_eval_l (h_abs x₀ l hl)
  -- Combine: σ is a minterm
  have h_minterm : Restriction.IsMinterm (fun x => !(lits.any (fun l => l.eval x))) σ :=
    ⟨h_const, h_min⟩
  rw [← h_len]
  exact Finset.le_sup (f := Restriction.length)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_minterm⟩)

/-- Rebuild a bottom OR gate using the goodness condition.
    Dual of `rebuild_bottom_and`: direct construction from free literals. -/
private theorem rebuild_bottom_or [NeZero N]
    (children : List (ACNFTree N true)) (ρ : Restriction N) (d : Nat)
    (h_allLit : isAllLit children = true)
    (hgood : Restriction.maxMintermLength
      (fun x => !(Restriction.restrict ρ (ACNFTree.or children).eval x)) ≤ d) :
    ∃ (c' : ACNFTree ρ.numFree false),
      (∀ x, c'.eval x = Restriction.restrict ρ
        (fun y => (ACNFTree.or children).eval y) x) ∧
      c'.depth ≤ (ACNFTree.or children).depth + 1 ∧
      c'.maxBottomFanIn ≤ d ∧
      1 ≤ c'.depth := by
  by_cases h_no_true : ∀ l ∈ extractLits children, ∀ v, ρ l.var = some v →
      (if l.polarity then v else !v) = false
  · -- No satisfied fixed literal: disjunction of remapped free literals
    let freeLits := remapFreeLits (extractLits children) ρ
    -- Sub-case: is the restricted OR a tautology?
    by_cases h_taut : ∀ x, ρ.restrict (ACNFTree.or children).eval x = true
    · -- Tautological: use `or [and []]` (constantly true, depth 2, fan-in 0)
      refine ⟨.or [.and []], ?_, ?_, ?_⟩
      · intro x; simp only [ACNFTree.eval, ACNFTree.eval.evalAny, ACNFTree.eval.evalAll,
          Bool.true_or, Restriction.restrict, Function.comp_def]
        exact (h_taut x).symm
      · rw [bottom_or_depth_eq_one children h_allLit]
        simp only [ACNFTree.depth, depth.depthList]; omega
      · exact ⟨maxBottomFanIn_or_and_empty ▸ Nat.zero_le _,
              by simp only [ACNFTree.depth, depth.depthList]; omega⟩
    · -- Non-tautological: ∃ x₀ with g(x₀) = false
      -- Use deduped free literals: same semantics, but distinct for bounding
      push_neg at h_taut
      obtain ⟨x₀, hx₀⟩ := h_taut
      refine ⟨.or (freeLits.dedup.map fun l => .lit l), ?_, ?_, ?_⟩
      · -- Eval: deduped disjunction computes the restricted OR
        intro x
        simp only [ACNFTree.eval, Restriction.restrict, Function.comp_def]
        rw [evalAny_map_lit, any_dedup_eq_any, evalAny_eq_any_extractLits h_allLit]
        exact (restrictedOr_eq_remappedLits (extractLits children) ρ h_no_true x).symm
      · rw [bottom_or_depth_eq_one children h_allLit]
        unfold ACNFTree.depth; rw [depthList_map_lit]; omega
      · constructor
        · -- Fan-in: dedup.length ≤ maxMintermLength(¬g) ≤ d
          unfold maxBottomFanIn; rw [isAllLit_map_lit]; simp only [↓reduceIte, List.length_map]
          -- freeLits has a falsifying assignment (from hx₀)
          have h_not_taut_free : ∃ x₀, freeLits.any (fun l => l.eval x₀) = false := by
            refine ⟨x₀, Bool.eq_false_iff.mpr fun h_any => hx₀ ?_⟩
            simp only [Restriction.restrict, ACNFTree.eval]
            rw [evalAny_eq_any_extractLits h_allLit,
                restrictedOr_eq_remappedLits (extractLits children) ρ h_no_true x₀]
            exact h_any
          -- dedup of freeLits has distinct vars (since OR is not tautological)
          have h_nodup := dedup_nodup_vars_of_not_taut h_not_taut_free
          -- dedup.length ≤ maxMintermLength(¬(dedup.any)) via constructed minterm
          have h_bound := lits_length_le_maxMintermLength_neg freeLits.dedup h_nodup
          -- Rewrite ¬(dedup.any) = ¬(restricted OR) to match hgood
          have h_any_eq : (fun x => !(freeLits.dedup.any (fun l => l.eval x))) =
              (fun x => !(ρ.restrict (ACNFTree.or children).eval x)) := by
            funext x; congr 1
            rw [any_dedup_eq_any]
            symm
            simp only [Restriction.restrict, ACNFTree.eval]
            rw [evalAny_eq_any_extractLits h_allLit,
                restrictedOr_eq_remappedLits (extractLits children) ρ h_no_true x]
          rw [h_any_eq] at h_bound
          exact le_trans h_bound hgood
        · unfold ACNFTree.depth; omega
  · -- Some fixed literal is satisfied: OR is constantly true.
    -- Use `or [and []]` which evaluates to true, depth 2, fan-in 0.
    push_neg at h_no_true
    obtain ⟨l, hl_mem, v, hv, h_true⟩ := h_no_true
    refine ⟨.or [.and []], ?_, ?_, ?_⟩
    · intro x
      simp only [ACNFTree.eval, ACNFTree.eval.evalAny, ACNFTree.eval.evalAll,
        Bool.true_or, Restriction.restrict, Function.comp_def]
      rw [evalAny_eq_any_extractLits h_allLit]
      symm; rw [List.any_eq_true]
      exact ⟨l, hl_mem, by
        simp only [Literal.eval, Restriction.fillIn_fixed hv]
        revert h_true; cases l.polarity <;> simp_all⟩
    · rw [bottom_or_depth_eq_one children h_allLit]
      simp only [ACNFTree.depth, depth.depthList]; omega
    · exact ⟨maxBottomFanIn_or_and_empty ▸ Nat.zero_le _,
            by simp only [ACNFTree.depth, depth.depthList]; omega⟩

/-- Whether a tree is not a literal (i.e., is an AND or OR node). -/
def IsNonLit : ACNFTree N b → Prop
  | .lit _ => False
  | .and _ => True
  | .or _ => True

private theorem IsNonLit_of_depth_pos {b : Bool} {c : ACNFTree N b}
    (h : 1 ≤ c.depth) : c.IsNonLit := by
  cases c with
  | lit _ => simp [ACNFTree.depth] at h
  | and _ => trivial
  | or _ => trivial

private theorem isAllLit_cons_of_tail_false {b : Bool}
    (c : ACNFTree N b) {cs : List (ACNFTree N b)}
    (h : isAllLit cs = false) : isAllLit (c :: cs) = false := by
  match b, c with
  | _, .lit _ => simpa [isAllLit]
  | true, .and _ => simp [isAllLit]
  | false, .or _ => simp [isAllLit]

private theorem isAllLit_false_of_nonlit {b : Bool} {cs : List (ACNFTree N b)}
    {c : ACNFTree N b} (hc : c ∈ cs) (hnl : c.IsNonLit) : isAllLit cs = false := by
  induction cs with
  | nil => exact absurd hc List.not_mem_nil
  | cons hd tl ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · -- c = hd, c is non-literal → isAllLit (c :: tl) = false
      match b, c, hnl with
      | true, .and _, _ => simp [isAllLit]
      | false, .or _, _ => simp [isAllLit]
    · -- c ∈ tl
      match b, hd with
      | _, .lit _ => simp [isAllLit]; exact ih hc
      | true, .and _ => simp [isAllLit]
      | false, .or _ => simp [isAllLit]

private theorem size_le_sizeList_of_mem {b : Bool} {cs : List (ACNFTree N b)}
    {c : ACNFTree N b} (hc : c ∈ cs) : c.size ≤ ACNFTree.size.sizeList cs := by
  induction cs with
  | nil => exact absurd hc List.not_mem_nil
  | cons hd tl ih =>
    unfold ACNFTree.size.sizeList
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    · have := ih hc; omega

/-- Rebuild a list of children using an oracle for each child.
    Factored out to break the mutual dependency between `rebuild_child` and
    `rebuild_list`. -/
private theorem rebuild_children_list [NeZero N] {b' : Bool}
    (cs : List (ACNFTree N b')) (ρ : Restriction N) (d : Nat)
    (hgood : IsGoodRestriction.isGoodList ρ d cs)
    (oracle : ∀ c ∈ cs, IsGoodRestriction ρ d c →
      ∃ (c' : ACNFTree ρ.numFree b'),
        (∀ x, c'.eval x = Restriction.restrict ρ (fun y => c.eval y) x) ∧
        c'.depth ≤ max 2 (c.depth + 1) ∧
        c'.maxBottomFanIn ≤ d ∧
        (c.IsNonLit → c'.IsNonLit)) :
    ∃ (cs' : List (ACNFTree ρ.numFree b')),
      cs'.length = cs.length ∧
      (∀ i (hi : i < cs.length) (hi' : i < cs'.length),
        ∀ x, (cs'.get ⟨i, hi'⟩).eval x =
          Restriction.restrict ρ (fun y => (cs.get ⟨i, hi⟩).eval y) x) ∧
      depth.depthList cs' ≤ max 2 (depth.depthList cs + 1) ∧
      (∀ c' ∈ cs', c'.maxBottomFanIn ≤ d) ∧
      (isAllLit cs = false → isAllLit cs' = false) := by
  induction cs with
  | nil =>
    exact ⟨[], rfl, fun _ hi => absurd hi (Nat.not_lt_zero _),
      by unfold depth.depthList; omega,
      fun _ h => absurd h List.not_mem_nil,
      fun h => by simp [isAllLit] at h⟩
  | cons c cs ih =>
    simp only [IsGoodRestriction.isGoodList] at hgood
    obtain ⟨hgood_c, hgood_cs⟩ := hgood
    obtain ⟨c', heval_c, hdepth_c, hfanin_c, hnonlit_c⟩ :=
      oracle c List.mem_cons_self hgood_c
    obtain ⟨cs', hlen, heval_cs, hdepth_cs, hfanin_cs, halllit_cs⟩ :=
      ih hgood_cs (fun c' hc' => oracle c' (List.mem_cons_of_mem _ hc'))
    refine ⟨c' :: cs', by simp [hlen], fun i hi hi' => ?_, ?_, ?_, ?_⟩
    · match i with
      | 0 => exact heval_c
      | i + 1 =>
        simp only [List.length_cons] at hi hi'
        exact heval_cs i (by omega) (by omega)
    · unfold depth.depthList
      exact Nat.max_le.mpr
        ⟨le_trans hdepth_c (by unfold depth.depthList; omega),
         le_trans hdepth_cs (by unfold depth.depthList; omega)⟩
    · intro c'' hc''
      simp only [List.mem_cons] at hc''
      rcases hc'' with rfl | hc''
      · exact hfanin_c
      · exact hfanin_cs c'' hc''
    · intro h_not_all
      match b', c with
      | _, .lit _ =>
        have hcs : isAllLit cs = false := by simpa [isAllLit] using h_not_all
        have hcs' : isAllLit cs' = false := halllit_cs hcs
        exact isAllLit_cons_of_tail_false c' hcs'
      | true, .and _ =>
        have : c'.IsNonLit := hnonlit_c trivial
        exact isAllLit_false_of_nonlit List.mem_cons_self this
      | false, .or _ =>
        have : c'.IsNonLit := hnonlit_c trivial
        exact isAllLit_false_of_nonlit List.mem_cons_self this

private theorem rebuild_child [NeZero N] {b : Bool}
    (c : ACNFTree N b) (ρ : Restriction N) (d : Nat)
    (hgood : IsGoodRestriction ρ d c) :
    ∃ (c' : ACNFTree ρ.numFree b),
      (∀ x, c'.eval x = Restriction.restrict ρ (fun y => c.eval y) x) ∧
      c'.depth ≤ max 2 (c.depth + 1) ∧
      c'.maxBottomFanIn ≤ d ∧
      (c.IsNonLit → c'.IsNonLit) := by
  -- Strong induction on c.size
  suffices ∀ (n : Nat) (b : Bool) (c : ACNFTree N b),
      c.size ≤ n → IsGoodRestriction ρ d c →
      ∃ (c' : ACNFTree ρ.numFree b),
        (∀ x, c'.eval x = Restriction.restrict ρ (fun y => c.eval y) x) ∧
        c'.depth ≤ max 2 (c.depth + 1) ∧
        c'.maxBottomFanIn ≤ d ∧
        (c.IsNonLit → c'.IsNonLit) from this c.size b c le_rfl hgood
  intro n
  induction n with
  | zero =>
    intro b c hsz hgood
    cases c with
    | lit l =>
      exact ⟨rebuildLiteral l ρ, rebuildLiteral_eval l ρ,
        le_trans (rebuildLiteral_depth l ρ) (by simp [ACNFTree.depth]),
        le_trans (rebuildLiteral_maxBottomFanIn l ρ) (Nat.zero_le _),
        fun h => absurd h (by simp [IsNonLit])⟩
    | and children => exfalso; unfold ACNFTree.size at hsz; omega
    | or children => exfalso; unfold ACNFTree.size at hsz; omega
  | succ n ih =>
    intro b c hsz hgood
    cases c with
    | lit l =>
      exact ⟨rebuildLiteral l ρ, rebuildLiteral_eval l ρ,
        le_trans (rebuildLiteral_depth l ρ) (by simp [ACNFTree.depth]),
        le_trans (rebuildLiteral_maxBottomFanIn l ρ) (Nat.zero_le _),
        fun h => absurd h (by simp [IsNonLit])⟩
    | and children =>
      by_cases h_allLit : isAllLit children = true
      · -- Bottom AND gate
        simp only [IsGoodRestriction, h_allLit, ite_true] at hgood
        obtain ⟨c', heval, hdepth, hfanin, hdepth_pos⟩ :=
          rebuild_bottom_and children ρ d h_allLit hgood
        exact ⟨c', heval,
          le_trans hdepth (by rw [bottom_and_depth_eq_one children h_allLit]; omega),
          hfanin, fun _ => IsNonLit_of_depth_pos hdepth_pos⟩
      · -- Non-bottom AND gate
        simp only [Bool.not_eq_true] at h_allLit
        simp only [IsGoodRestriction, h_allLit] at hgood
        have hsz_children : ∀ c' ∈ children, c'.size ≤ n := by
          intro c' hc'
          have : c'.size ≤ ACNFTree.size.sizeList children := size_le_sizeList_of_mem hc'
          unfold ACNFTree.size at hsz; omega
        have oracle : ∀ c' ∈ children, IsGoodRestriction ρ d c' →
            ∃ (c'' : ACNFTree ρ.numFree false),
              (∀ x, c''.eval x = Restriction.restrict ρ (fun y => c'.eval y) x) ∧
              c''.depth ≤ max 2 (c'.depth + 1) ∧
              c''.maxBottomFanIn ≤ d ∧
              (c'.IsNonLit → c''.IsNonLit) :=
          fun c' hc' hg => ih false c' (hsz_children c' hc') hg
        obtain ⟨cs', hlen, heval_i, hdepth_cs, hfanin_cs, halllit_cs⟩ :=
          rebuild_children_list children ρ d hgood oracle
        have hcs'_not_alllit : isAllLit cs' = false := halllit_cs h_allLit
        refine ⟨.and cs', ?_, ?_, ?_, fun _ => trivial⟩
        · intro x
          simp only [ACNFTree.eval, Restriction.restrict, Function.comp_def]
          exact evalAll_congr children cs'
            (fun x => ρ.fillIn (x ∘ ρ.freeVarEquiv.symm)) hlen
            (fun i hi hi' x' => by
              have := heval_i i hi (hlen ▸ hi) x'
              simp only [Restriction.restrict, Function.comp_def] at this
              exact this) x
        · -- 1 + depthList cs' ≤ max 2 (1 + depthList children + 1)
          unfold ACNFTree.depth
          have hdl_pos : 1 ≤ depth.depthList children := depthList_pos_of_not_allLit h_allLit
          omega
        · unfold maxBottomFanIn; rw [hcs'_not_alllit]; simp
          exact maxBottomFanInList_le_of_forall cs' d hfanin_cs
    | or children =>
      by_cases h_allLit : isAllLit children = true
      · -- Bottom OR gate
        simp only [IsGoodRestriction, h_allLit, ite_true] at hgood
        obtain ⟨c', heval, hdepth, hfanin, hdepth_pos⟩ :=
          rebuild_bottom_or children ρ d h_allLit hgood
        exact ⟨c', heval,
          le_trans hdepth (by rw [bottom_or_depth_eq_one children h_allLit]; omega),
          hfanin, fun _ => IsNonLit_of_depth_pos hdepth_pos⟩
      · -- Non-bottom OR gate
        simp only [Bool.not_eq_true] at h_allLit
        simp only [IsGoodRestriction, h_allLit] at hgood
        have hsz_children : ∀ c' ∈ children, c'.size ≤ n := by
          intro c' hc'
          have : c'.size ≤ ACNFTree.size.sizeList children := size_le_sizeList_of_mem hc'
          unfold ACNFTree.size at hsz; omega
        have oracle : ∀ c' ∈ children, IsGoodRestriction ρ d c' →
            ∃ (c'' : ACNFTree ρ.numFree true),
              (∀ x, c''.eval x = Restriction.restrict ρ (fun y => c'.eval y) x) ∧
              c''.depth ≤ max 2 (c'.depth + 1) ∧
              c''.maxBottomFanIn ≤ d ∧
              (c'.IsNonLit → c''.IsNonLit) :=
          fun c' hc' hg => ih true c' (hsz_children c' hc') hg
        obtain ⟨cs', hlen, heval_i, hdepth_cs, hfanin_cs, halllit_cs⟩ :=
          rebuild_children_list children ρ d hgood oracle
        have hcs'_not_alllit : isAllLit cs' = false := halllit_cs h_allLit
        refine ⟨.or cs', ?_, ?_, ?_, fun _ => trivial⟩
        · intro x
          simp only [ACNFTree.eval, Restriction.restrict, Function.comp_def]
          exact evalAny_congr children cs'
            (fun x => ρ.fillIn (x ∘ ρ.freeVarEquiv.symm)) hlen
            (fun i hi hi' x' => by
              have := heval_i i hi (hlen ▸ hi) x'
              simp only [Restriction.restrict, Function.comp_def] at this
              exact this) x
        · unfold ACNFTree.depth
          have hdl_pos : 1 ≤ depth.depthList children := depthList_pos_of_not_allLit h_allLit
          omega
        · unfold maxBottomFanIn; rw [hcs'_not_alllit]; simp
          exact maxBottomFanInList_le_of_forall cs' d hfanin_cs

/-- **Rebuild a list of children** using `rebuild_child` on each element.
    The depth bound uses `max 2 (depthList cs + 1)` because literals (depth 0)
    may be rebuilt as constants (depth 2), and bottom gates (depth 1) may
    increase to depth 2. -/
private theorem rebuild_list [NeZero N] {b' : Bool}
    (cs : List (ACNFTree N b')) (ρ : Restriction N) (d : Nat)
    (hgood : IsGoodRestriction.isGoodList ρ d cs) :
    ∃ (cs' : List (ACNFTree ρ.numFree b')),
      cs'.length = cs.length ∧
      (∀ i (hi : i < cs.length) (hi' : i < cs'.length),
        ∀ x, (cs'.get ⟨i, hi'⟩).eval x =
          Restriction.restrict ρ (fun y => (cs.get ⟨i, hi⟩).eval y) x) ∧
      depth.depthList cs' ≤ max 2 (depth.depthList cs + 1) ∧
      (∀ c' ∈ cs', c'.maxBottomFanIn ≤ d) ∧
      (isAllLit cs = false → isAllLit cs' = false) :=
  rebuild_children_list cs ρ d hgood (fun c _ hg => rebuild_child c ρ d hg)

/-- **Tree reconstruction from a good restriction.**

Since `t.depth ≥ 2` and bottom gates have depth 1, the root is a non-bottom
AND/OR node. For the non-bottom case, `IsGoodRestriction` recurses into
`isGoodList`, and we use `rebuild_list` to reconstruct the children.
The new root node has the same constructor (AND/OR) with the rebuilt children.

The depth bound gives `t'.depth ≤ t.depth + 1` because bottom-level gates
(depth 1) may increase to depth 2 under reconstruction. -/
theorem rebuild_from_good_restriction [NeZero N] {b : Bool}
    (t : ACNFTree N b) (ρ : Restriction N) (d : Nat)
    (hd_depth : 2 ≤ t.depth)
    (hgood : t.IsGoodRestriction ρ d) :
    ∃ (t' : ACNFTree ρ.numFree b),
      (∀ x, t'.eval x = Restriction.restrict ρ (fun y => t.eval y) x) ∧
      t'.depth ≤ t.depth + 1 ∧
      t'.maxBottomFanIn ≤ d := by
  match t with
  | .lit _ => exfalso; unfold ACNFTree.depth at hd_depth; omega
  | .and children =>
    have h_not_bottom : isAllLit children = false := by
      cases h : isAllLit children
      · rfl
      · rw [bottom_and_depth_eq_one children h] at hd_depth; omega
    simp only [IsGoodRestriction, h_not_bottom] at hgood
    obtain ⟨cs', hlen, heval_i, hdepth_cs, hfanin_cs, halllit_cs⟩ :=
      rebuild_list children ρ d hgood
    have hdl_pos : 1 ≤ depth.depthList children := depthList_pos_of_not_allLit h_not_bottom
    have hcs'_not_alllit : isAllLit cs' = false := halllit_cs h_not_bottom
    refine ⟨.and cs', ?_, ?_, ?_⟩
    · intro x
      simp only [ACNFTree.eval, Restriction.restrict, Function.comp_def]
      exact evalAll_congr children cs'
        (fun x => ρ.fillIn (x ∘ ρ.freeVarEquiv.symm)) hlen
        (fun i hi hi' x' => by
          have := heval_i i hi (hlen ▸ hi) x'
          simp only [Restriction.restrict, Function.comp_def] at this
          exact this) x
    · unfold ACNFTree.depth; omega
    · unfold maxBottomFanIn; rw [hcs'_not_alllit]; simp
      exact maxBottomFanInList_le_of_forall cs' d hfanin_cs
  | .or children =>
    have h_not_bottom : isAllLit children = false := by
      cases h : isAllLit children
      · rfl
      · rw [bottom_or_depth_eq_one children h] at hd_depth; omega
    simp only [IsGoodRestriction, h_not_bottom] at hgood
    obtain ⟨cs', hlen, heval_i, hdepth_cs, hfanin_cs, halllit_cs⟩ :=
      rebuild_list children ρ d hgood
    have hdl_pos : 1 ≤ depth.depthList children := depthList_pos_of_not_allLit h_not_bottom
    have hcs'_not_alllit : isAllLit cs' = false := halllit_cs h_not_bottom
    refine ⟨.or cs', ?_, ?_, ?_⟩
    · intro x
      simp only [ACNFTree.eval, Restriction.restrict, Function.comp_def]
      exact evalAny_congr children cs'
        (fun x => ρ.fillIn (x ∘ ρ.freeVarEquiv.symm)) hlen
        (fun i hi hi' x' => by
          have := heval_i i hi (hlen ▸ hi) x'
          simp only [Restriction.restrict, Function.comp_def] at this
          exact this) x
    · unfold ACNFTree.depth; omega
    · unfold maxBottomFanIn; rw [hcs'_not_alllit]; simp
      exact maxBottomFanInList_le_of_forall cs' d hfanin_cs

end ACNFTree

/-! ## Step 1: Bottom Fan-In Reduction -/

/-- **Step 1 of the parity ∉ AC⁰ proof: bottom fan-in reduction.**

Given an ACNFTree of depth ≥ 2 on `N` variables, there exists a restriction `ρ`
leaving `s` free variables and a new ACNFTree over those free variables with:
1. Correct evaluation (restriction of the original function)
2. Depth at most the original depth + 1
3. All bottom-level gates with fan-in at most `d`

Parameters `s` (free variables) and `d` (target fan-in) must satisfy:
- `d ≤ s` and `2s ≤ N` (switching lemma requirements)
- `numBottomGates · (8s)^d < N^d` (union bound: ensures the total number of
  "bad" restrictions across all bottom gates is less than the total number of
  restrictions, so a "good" restriction exists) -/
theorem acnf_bottom_fanin_reduction {N : Nat} [NeZero N] {b : Bool}
    (t : ACNFTree N b) (s d : Nat)
    (hd_depth : 2 ≤ t.depth)
    (hd_le_s : d ≤ s)
    (h2sN : 2 * s ≤ N)
    (hunion : t.numBottomGates * (8 * s) ^ d < N ^ d) :
    ∃ (ρ : Restriction N) (t' : ACNFTree ρ.numFree b),
      ρ.numFree = s ∧
      (∀ x, t'.eval x = Restriction.restrict ρ (fun y => t.eval y) x) ∧
      t'.depth ≤ t.depth + 1 ∧
      t'.maxBottomFanIn ≤ d := by
  obtain ⟨ρ, hρfree, hρgood⟩ := t.exists_good_restriction s d hd_le_s h2sN hunion
  obtain ⟨t', heval, hdepth, hfanin⟩ := t.rebuild_from_good_restriction ρ d hd_depth hρgood
  exact ⟨ρ, t', hρfree, heval, hdepth, hfanin⟩
