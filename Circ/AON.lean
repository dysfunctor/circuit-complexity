import Mathlib.Data.Nat.Lattice
import Circ.Basic

/-- Operations in an AND/OR basis. Negation is handled by per-input flags on gates. -/
inductive AONOp where
  | and
  | or
  deriving Repr, DecidableEq

private def AONOp.eval : (op : AONOp) → (n : Nat) → BitString n → Bool
  | .and, n, inputs => Fin.foldl n (fun acc i => acc && inputs i) true
  | .or, n, inputs => Fin.foldl n (fun acc i => acc || inputs i) false

/-- AND/OR basis with unbounded fan-in. Negation is free (per-input flags on gates). -/
def Basis.unboundedAON : Basis where
  Op := AONOp
  arity
    | .and => .unbounded
    | .or => .unbounded
  eval op n _ inputs := op.eval n inputs

/-- AND/OR basis with fan-in bounded by `k`. Negation is free (per-input flags on gates). -/
def Basis.boundedAON (k : Nat) : Basis where
  Op := AONOp
  arity
    | .and => .upto k
    | .or => .upto k
  eval op n _ inputs := op.eval n inputs

/-- Indicator circuit: outputs `true` iff the input equals `s`.

A single N-input AND gate where input `i` is wired to primary input `i`,
negated when `s i = false`. No internal gates needed. -/
def AONIndicator {N : Nat} [NeZero N] (s : BitString N) :
    Circuit Basis.unboundedAON N 1 0 where
  gates i := i.elim0
  outputs _ :=
    { op := .and, fanIn := N, arityOk := trivial,
      inputs := fun j => ⟨j.val, by omega⟩,
      negated := fun j => !(s j) }
  acyclic i := i.elim0

/-- DNF circuit computing an arbitrary `f : BitString N → Bool`.

For each of the `2^N` possible inputs `s` (decoded via `Nat.testBit`),
internal gate `i` is the indicator AND for `s` when `f s = true`, or a
trivially-false 0-input OR otherwise. The single output OR gate disjoins
all internal gates. -/
private def AONFor.mkGate {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N)) :
    Gate Basis.unboundedAON (N + 2 ^ N) :=
  if f (fun j => i.val.testBit j.val) then
    { op := .and, fanIn := N, arityOk := trivial,
      inputs := fun j => (j.castAdd (2 ^ N)),
      negated := fun j => !(i.val.testBit j.val) }
  else
    { op := .or, fanIn := 0, arityOk := trivial,
      inputs := Fin.elim0,
      negated := Fin.elim0 }

private lemma AONFor.mkGate_acyclic {N : Nat} (f : BitString N → Bool)
    (i : Fin (2 ^ N)) (k : Fin (AONFor.mkGate f i).fanIn) :
    ((AONFor.mkGate f i).inputs k).val < N + i.val := by
  revert k; unfold mkGate
  cases f (fun j => i.val.testBit j.val)
  · intro k; exact Fin.elim0 k
  · intro k; exact Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right N _)

def AONFor {N : Nat} [NeZero N] (f : BitString N → Bool) :
    Circuit Basis.unboundedAON N 1 (2 ^ N) where
  gates := AONFor.mkGate f
  outputs _ :=
    { op := .or, fanIn := 2 ^ N, arityOk := trivial,
      inputs := fun j => (j.natAdd N),
      negated := fun _ => false }
  acyclic := AONFor.mkGate_acyclic f

private lemma AONFor_wireValue_gate {N : Nat} [NeZero N] (f : BitString N → Bool)
    (x : BitString N) (i : Fin (2 ^ N)) :
    (AONFor f).wireValue x (Fin.natAdd N i) =
      (AONFor.mkGate f i).eval ((AONFor f).wireValue x) := by
  have hge : ¬ ((Fin.natAdd N i).val < N) := by simp [Fin.natAdd]
  rw [Circuit.wireValue_ge _ _ _ hge]
  congr 1
  show (AONFor f).gates _ = AONFor.mkGate f i
  simp only [AONFor]
  congr 1
  exact Fin.ext (by simp [Fin.natAdd])

@[simp] private lemma AONFor_outputs {N : Nat} [NeZero N] (f : BitString N → Bool) (j : Fin 1) :
    (AONFor f).outputs j =
      { op := .or, fanIn := 2 ^ N, arityOk := trivial,
        inputs := Fin.natAdd N, negated := fun _ => false } := rfl

@[simp] private lemma AONFor_gates {N : Nat} [NeZero N] (f : BitString N → Bool) :
    (AONFor f).gates = AONFor.mkGate f := rfl

-- Helper lemmas for AONFor_is_Correct

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

private lemma AONFor_wireValue_input {N : Nat} [NeZero N] (f : BitString N → Bool)
    (x : BitString N) (j : Fin N) :
    (AONFor f).wireValue x (j.castAdd (2 ^ N)) = x j := by
  have h : (j.castAdd (2 ^ N)).val < N := by simp [Fin.val_castAdd]
  rw [Circuit.wireValue_lt _ _ _ h]
  congr 1

private lemma xor_not_eq_true_iff (a b : Bool) : ((!b).xor a = true) ↔ (a = b) := by
  cases a <;> cases b <;> simp

private lemma mkGate_true {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = true) :
    AONFor.mkGate f i =
      { op := .and, fanIn := N, arityOk := trivial,
        inputs := fun j => (j.castAdd (2 ^ N)),
        negated := fun j => !(i.val.testBit j.val) } := by
  unfold AONFor.mkGate; simp [hfi]

private lemma mkGate_eval_false {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (wv : BitString (N + 2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = false) :
    (AONFor.mkGate f i).eval wv = false := by
  unfold AONFor.mkGate Gate.eval
  simp [hfi, Basis.unboundedAON, AONOp.eval, Fin.foldl_zero]

private lemma mkGate_eval_true_iff {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (wv : BitString (N + 2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = true) :
    (AONFor.mkGate f i).eval wv = true ↔
      ∀ j : Fin N, wv (j.castAdd (2 ^ N)) = (i.val.testBit j.val) := by
  rw [mkGate_true f i hfi]
  simp only [Gate.eval, Basis.unboundedAON, AONOp.eval]
  rw [foldl_band_eq_true]
  exact ⟨fun h j => (xor_not_eq_true_iff _ _).mp (h j),
         fun h j => (xor_not_eq_true_iff _ _).mpr (h j)⟩

private lemma exists_testBit_encode (N : Nat) (x : BitString N) :
    ∃ m : Fin (2 ^ N), ∀ j : Fin N, m.val.testBit j.val = x j := by
  induction N with
  | zero => exact ⟨⟨0, Nat.one_pos⟩, fun j => j.elim0⟩
  | succ n ih =>
    obtain ⟨m', hm'⟩ := ih (fun j => x j.castSucc)
    have hm'_bound : m'.val < 2 ^ n := m'.isLt
    refine ⟨⟨m'.val ||| (if x (Fin.last n) then 2 ^ n else 0),
            Nat.or_lt_two_pow (by omega) (by split <;> omega)⟩, ?_⟩
    intro j; simp only
    rw [Nat.testBit_or]
    exact Fin.lastCases
      (by
        simp only [Fin.val_last]
        rw [Nat.testBit_lt_two_pow hm'_bound]
        simp only [Bool.false_or]
        split <;> rename_i h
        · simp [Nat.testBit_two_pow_self, h]
        · simp [Nat.zero_testBit]
          cases hx : x (Fin.last n) <;> simp_all)
      (fun k => by
        simp only [Fin.val_castSucc]
        rw [hm' k]
        split
        · rw [Nat.testBit_two_pow]; simp [Nat.ne_of_gt k.isLt]
        · simp [Nat.zero_testBit])
      j

-- Main correctness theorem
def AONFor_is_Correct {N : Nat} [NeZero N] (f : BitString N → Bool) :
    (fun (x : BitString 1) => x 0) ∘ (AONFor f).eval = f := by
  funext x
  simp only [Function.comp, Circuit.eval, AONFor_outputs, Gate.eval,
    Basis.unboundedAON, Bool.false_xor, AONOp.eval]
  have key : ∀ i : Fin (2^N), (AONFor f).wireValue x (Fin.natAdd N i) =
      (AONFor.mkGate f i).eval ((AONFor f).wireValue x) := AONFor_wireValue_gate f x
  conv_lhs => arg 2; ext acc i; erw [key i]
  -- Goal: Fin.foldl (2^N) (fun acc i => acc || (mkGate f i).eval (wireValue x)) false = f x
  have h_iff : (Fin.foldl (2 ^ N)
      (fun acc i => acc || (AONFor.mkGate f i).eval ((AONFor f).wireValue x))
      false = true) ↔ (f x = true) := by
    rw [foldl_bor_eq_true]
    constructor
    · -- Some gate fires → f x = true
      rintro ⟨i, hi⟩
      by_cases hfi : f (fun j => i.val.testBit j.val) = true
      · rw [mkGate_eval_true_iff f i _ hfi] at hi
        have hxeq : ∀ j : Fin N, x j = i.val.testBit j.val := by
          intro j; rw [← AONFor_wireValue_input f x j]; exact hi j
        have : f x = f (fun j => i.val.testBit j.val) := congr_arg f (funext hxeq)
        rw [this]; exact hfi
      · have hfi' : f (fun j => i.val.testBit j.val) = false := by
          cases h : f (fun j => i.val.testBit j.val) <;> simp_all
        exact absurd (mkGate_eval_false f i _ hfi' ▸ hi) Bool.false_ne_true
    · -- f x = true → some gate fires
      intro hfx
      obtain ⟨m, hm⟩ := exists_testBit_encode N x
      refine ⟨m, ?_⟩
      have hfm : f (fun j => m.val.testBit j.val) = true := by
        convert hfx using 1; congr 1; funext j; exact hm j
      rw [mkGate_eval_true_iff f m _ hfm]
      intro j; rw [AONFor_wireValue_input f x j]; exact (hm j).symm
  -- Close by Bool case analysis using the ↔
  cases hfx : f x <;>
    cases hfold : Fin.foldl (2 ^ N) (fun acc i =>
      acc || (AONFor.mkGate f i).eval ((AONFor f).wireValue x)) false <;>
    simp_all
