import Mathlib.Algebra.BigOperators.Fin

/-! # Internal: Boolean foldl helpers

Shared `Fin.foldl` ↔ `List.any`/`List.all` and `∃`/`∀` lemmas used by
`Circ/Internal/NF.lean`, `Circ/Internal/AON.lean`, and
`Circ/NC1Lin/Circuit.lean` for circuit-correctness proofs. -/

lemma foldl_bor_eq_true {n : Nat} (g : Fin n → Bool) :
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

lemma foldl_band_eq_true {n : Nat} (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc && g i) true = true) ↔ (∀ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]; constructor
    · intro h; rw [Bool.and_eq_true] at h; obtain ⟨h1, h2⟩ := h
      rw [ih] at h1; intro i; exact Fin.lastCases h2 (fun j => h1 j) i
    · intro h; rw [Bool.and_eq_true]
      exact ⟨(ih _).mpr (fun j => h j.castSucc), h (Fin.last n)⟩

lemma foldl_bor_eq_list_any {α : Type} (l : List α) (p : α → Bool) :
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

lemma foldl_band_eq_list_all {α : Type} (l : List α) (p : α → Bool) :
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
