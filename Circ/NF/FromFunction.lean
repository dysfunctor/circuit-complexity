import Circ.NF.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card

/-! # Truth-table CNF compilation on a support set

When a Boolean function `f : BitString N → Bool` depends only on a
subset `S ⊆ Fin N` of its inputs, we can compile it to a CNF with
`≤ 2^|S|` clauses by iterating over `S`-assignments and using a fixed
extension to `BitString N`. This is what Jukna's Lemma 11.1 consumes,
applied to each small-depth subcircuit whose value depends only on its
reachable primary inputs.

## Main definitions

* `CNF.clauseExcludingS S α` — the clause for the falsifying
  `S`-assignment `α`.
* `CNF.fromFunctionOnSet f S h` — the support-restricted truth-table CNF.

## Main results

* `CNF.fromFunctionOnSet_eval` — `(fromFunctionOnSet f S h).eval x = f x`.
* `CNF.fromFunctionOnSet_complexity_le` —
  `(fromFunctionOnSet f S h).complexity ≤ 2^|S|`.
-/

namespace CNF

variable {N : ℕ}

/-- A literal with polarity `!b` at position `i` evaluates to `true`
exactly when `x i ≠ b`. -/
theorem literal_eval_neg_polarity (b : Bool) (x : BitString N) (i : Fin N) :
    ({ var := i, polarity := !b } : Literal N).eval x = decide (x i ≠ b) := by
  simp only [Literal.eval]
  cases b <;> cases x i <;> decide

/-- Canonical extension of an `S`-assignment `α` to a full `BitString N`:
fills in `false` outside `S`. Any two extensions are interchangeable
for functions that depend only on `S`; this one is convenient because
it gives a specific term. -/
def extendFromS (S : Finset (Fin N)) (α : {i // i ∈ S} → Bool) : BitString N :=
  fun i => if hi : i ∈ S then α ⟨i, hi⟩ else false

lemma extendFromS_of_mem (S : Finset (Fin N)) (α : {i // i ∈ S} → Bool)
    (i : Fin N) (hi : i ∈ S) : extendFromS S α i = α ⟨i, hi⟩ := by
  simp [extendFromS, hi]

/-- Clause that excludes a specific `S`-assignment `α`: one literal per
variable in `S`, with polarity `!(α i)`. Evaluates to `true` iff the
input disagrees with `α` somewhere on `S`. -/
noncomputable def clauseExcludingS (S : Finset (Fin N))
    (α : {i // i ∈ S} → Bool) : List (Literal N) :=
  S.attach.toList.map (fun i => { var := i.val, polarity := !(α i) })

theorem clauseExcludingS_any_eval (S : Finset (Fin N))
    (α : {i // i ∈ S} → Bool) (x : BitString N) :
    ((clauseExcludingS S α).any fun l => l.eval x) =
      decide (∃ i : {i // i ∈ S}, x i.val ≠ α i) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨l, hl_mem, hl_eval⟩
    simp only [clauseExcludingS, List.mem_map, Finset.mem_toList,
      Finset.mem_attach, true_and] at hl_mem
    obtain ⟨i, hi_eq⟩ := hl_mem
    refine ⟨i, ?_⟩
    rw [← hi_eq, literal_eval_neg_polarity, decide_eq_true_eq] at hl_eval
    exact hl_eval
  · rintro ⟨i, hi⟩
    refine ⟨{ var := i.val, polarity := !(α i) }, ?_, ?_⟩
    · simp only [clauseExcludingS, List.mem_map, Finset.mem_toList,
        Finset.mem_attach, true_and]
      exact ⟨i, rfl⟩
    · rw [literal_eval_neg_polarity, decide_eq_true_eq]
      exact hi

/-- Tight truth-table CNF when `f` depends only on the variables in `S`.
One clause per `S`-assignment that makes `f` false (extended to
`BitString N` via `extendFromS`). -/
noncomputable def fromFunctionOnSet (f : BitString N → Bool)
    (S : Finset (Fin N))
    (_h : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y) : CNF N :=
  ⟨((Finset.univ : Finset ({i // i ∈ S} → Bool)).filter
      (fun α => !f (extendFromS S α))).toList.map (clauseExcludingS S)⟩

theorem fromFunctionOnSet_eval (f : BitString N → Bool)
    (S : Finset (Fin N))
    (h : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y) (x : BitString N) :
    (fromFunctionOnSet f S h).eval x = f x := by
  show ((((Finset.univ : Finset ({i // i ∈ S} → Bool)).filter
      (fun α => !f (extendFromS S α))).toList.map
        (clauseExcludingS S)).all (fun c => c.any fun l => l.eval x)) = f x
  simp only [List.all_map, Function.comp_def, clauseExcludingS_any_eval]
  rw [Bool.eq_iff_iff, List.all_eq_true]
  simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  constructor
  · intro hAll
    by_contra hfx
    have hfx' : f x = false := by
      match hc : f x with
      | false => rfl
      | true => exact absurd hc hfx
    -- Apply hAll at α = x restricted to S.
    set α : {i // i ∈ S} → Bool := fun i => x i.val with hα_def
    have hf_ext : f (extendFromS S α) = false := by
      rw [← hfx']
      apply h (extendFromS S α) x
      intro i hi
      rw [extendFromS_of_mem S α i hi]
    have hnf_ext : (!f (extendFromS S α)) = true := by simp [hf_ext]
    obtain ⟨i, hi⟩ := hAll α hnf_ext
    -- hi : x i.val ≠ α i = x i.val — contradiction.
    simp [hα_def] at hi
  · intro hfx α hfα
    -- Want: ∃ i, x i.val ≠ α i.
    -- Assume for contradiction that x agrees with α on S.
    by_contra hcon
    push_neg at hcon
    -- hcon : ∀ i : {i // i ∈ S}, x i.val = α i
    -- Then x agrees with extendFromS α on S, so f x = f (extendFromS α).
    have hagree : ∀ i ∈ S, x i = extendFromS S α i := fun i hi => by
      rw [extendFromS_of_mem S α i hi]; exact hcon ⟨i, hi⟩
    have := h x (extendFromS S α) hagree
    -- this : f x = f (extendFromS S α)
    -- hfα : !f (extendFromS S α) = true, i.e., f (extendFromS S α) = false
    -- hfx : f x = true
    -- contradiction
    rw [this] at hfx
    have : f (extendFromS S α) = false := by
      match hc : f (extendFromS S α) with
      | false => rfl
      | true => simp [hc] at hfα
    rw [this] at hfx
    exact Bool.false_ne_true hfx

theorem fromFunctionOnSet_complexity_le (f : BitString N → Bool)
    (S : Finset (Fin N))
    (h : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y) :
    (fromFunctionOnSet f S h).complexity ≤ 2 ^ S.card := by
  show ((((Finset.univ : Finset ({i // i ∈ S} → Bool)).filter
      (fun α => !f (extendFromS S α))).toList.map (clauseExcludingS S)).length)
      ≤ 2 ^ S.card
  rw [List.length_map, Finset.length_toList]
  calc ((Finset.univ : Finset ({i // i ∈ S} → Bool)).filter
            (fun α => !f (extendFromS S α))).card
      ≤ (Finset.univ : Finset ({i // i ∈ S} → Bool)).card :=
        Finset.card_filter_le _ _
    _ = Fintype.card ({i // i ∈ S} → Bool) := Finset.card_univ
    _ = 2 ^ S.card := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

end CNF
