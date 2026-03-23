import Circ.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

/-! # Internal: Restriction Infrastructure

This internal module provides the core definitions and lemmas for restrictions
(partial assignments of Boolean variables). The public API in `Circ.Restriction`
re-exports `restrict`, `IsMinterm`, and `maxMintermLength`.
-/

namespace Restriction

variable {N : Nat}

/-! ## Free and fixed variables -/

/-- Whether variable `i` is free (unassigned) under restriction `ρ`. -/
def isFree (ρ : _root_.Restriction N) (i : Fin N) : Prop := ρ i = none

instance decIsFree (ρ : _root_.Restriction N) (i : Fin N) : Decidable (ρ.isFree i) :=
  inferInstanceAs (Decidable (ρ i = none))

/-- The set of free variables under restriction `ρ`. -/
def freeVars (ρ : _root_.Restriction N) : Finset (Fin N) :=
  Finset.univ.filter ρ.isFree

/-- The number of free variables under restriction `ρ`. -/
def numFree (ρ : _root_.Restriction N) : Nat := ρ.freeVars.card

/-! ## Support -/

/-- The support of a restriction: the set of fixed (non-free) variables,
i.e., those `i` with `ρ(i) ≠ *`. -/
def support (ρ : _root_.Restriction N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ¬ρ.isFree i)

/-- The length of a restriction is the size of its support
(the number of fixed variables). -/
def length (ρ : _root_.Restriction N) : Nat := ρ.support.card

/-! ## Unfixing variables -/

/-- Unfix variable `i`, setting it to free regardless of its current value.
All other variables keep their assignment from `ρ`. -/
def unfix (ρ : _root_.Restriction N) (i : Fin N) : _root_.Restriction N :=
  fun j => if j = i then none else ρ j

/-! ## FreeVar and fillIn -/

/-- The type of free variables under restriction `ρ`: indices where `ρ` leaves
the variable unassigned. -/
def FreeVar (ρ : _root_.Restriction N) := {i : Fin N // ρ i = none}

instance instFintypeFreeVar (ρ : _root_.Restriction N) : Fintype ρ.FreeVar :=
  show Fintype {i : Fin N // ρ i = none} from inferInstance

/-- Extend a free-variable assignment to a full `N`-variable assignment
by filling in the values fixed by `ρ`. -/
def fillIn (ρ : _root_.Restriction N) (x : ρ.FreeVar → Bool) : BitString N :=
  fun i =>
    match h : ρ i with
    | some b => b
    | none => x ⟨i, h⟩

/-- Apply a restriction to a Boolean function, producing a function on the
free variables only. The fixed variables are baked in from `ρ`. -/
def applyFun (ρ : _root_.Restriction N) (f : BitString N → Bool) :
    (ρ.FreeVar → Bool) → Bool :=
  f ∘ ρ.fillIn

/-! ### fillIn properties -/

@[simp]
theorem fillIn_fixed {ρ : _root_.Restriction N} {i : Fin N} {b : Bool}
    (h : ρ i = some b) (x : ρ.FreeVar → Bool) : ρ.fillIn x i = b := by
  unfold fillIn; split <;> simp_all

@[simp]
theorem fillIn_free {ρ : _root_.Restriction N} (v : ρ.FreeVar)
    (x : ρ.FreeVar → Bool) : ρ.fillIn x v.val = x v := by
  unfold fillIn; split
  · next h => exact absurd (v.prop ▸ h : none = some _) nofun
  · rfl

/-! ## Equivalence with `Fin numFree` -/

theorem card_freeVar_eq (ρ : _root_.Restriction N) :
    Fintype.card ρ.FreeVar = ρ.numFree := by
  unfold FreeVar numFree freeVars isFree; rw [Fintype.card_subtype]

/-- Equivalence between `Fin ρ.numFree` and the free variables of a restriction,
providing a canonical indexing of free variables as a `BitString`. -/
noncomputable def freeVarEquiv (ρ : _root_.Restriction N) : Fin ρ.numFree ≃ ρ.FreeVar :=
  (finCongr ρ.card_freeVar_eq.symm).trans (Fintype.equivFin ρ.FreeVar).symm

/-! ## Sets of restrictions -/

noncomputable instance instFintypeRestriction : Fintype (_root_.Restriction N) :=
  inferInstanceAs (Fintype (Fin N → Option Bool))

/-- The set of restrictions on `N` variables with exactly `s` free variables. -/
noncomputable def sRestrictions (N s : Nat) : Finset (_root_.Restriction N) :=
  Finset.univ.filter (fun ρ => numFree ρ = s)

end Restriction
