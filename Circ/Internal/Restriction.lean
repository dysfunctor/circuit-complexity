import Circ.Basic
import Mathlib.Data.Fintype.Card

/-! # Internal: Restriction Infrastructure

This internal module provides the core definitions and lemmas for restrictions
(partial assignments of Boolean variables). The public API in `Circ.Restriction`
re-exports `restrict`, `IsMinterm`, and `maxMintermLength`.
-/

namespace Restriction

variable {N : Nat}

/-- The trivial restriction: all variables are free. -/
def trivial : _root_.Restriction N := fun _ => none

instance : Inhabited (_root_.Restriction N) := ⟨trivial⟩

theorem ext {ρ₁ ρ₂ : _root_.Restriction N} (h : ∀ i, ρ₁ i = ρ₂ i) : ρ₁ = ρ₂ :=
  funext h

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

/-- `fillIn` composed with itself is the identity: if we extract the free
variable values from a `fillIn` result, we get back the original assignment. -/
theorem fillIn_surjective {ρ : _root_.Restriction N} (x : ρ.FreeVar → Bool) :
    (fun v : ρ.FreeVar => ρ.fillIn x v.val) = x := by
  funext v; exact fillIn_free v x

/-! ## Compatibility -/

/-- Two restrictions are compatible if they agree on all commonly fixed variables. -/
def Compatible (ρ₁ ρ₂ : _root_.Restriction N) : Prop :=
  ∀ (i : Fin N) (b₁ b₂ : Bool), ρ₁ i = some b₁ → ρ₂ i = some b₂ → b₁ = b₂

theorem Compatible.symm {ρ₁ ρ₂ : _root_.Restriction N} (h : ρ₁.Compatible ρ₂) :
    ρ₂.Compatible ρ₁ :=
  fun i b₁ b₂ h₁ h₂ => (h i b₂ b₁ h₂ h₁).symm

@[simp]
theorem compatible_trivial_right (ρ : _root_.Restriction N) : ρ.Compatible trivial := by
  intro i _ b₂ _ h₂; simp [trivial] at h₂

@[simp]
theorem compatible_trivial_left (ρ : _root_.Restriction N) : trivial.Compatible ρ :=
  (compatible_trivial_right ρ).symm

/-! ## Composition -/

/-- Composition of compatible restrictions: merges the assignments of `ρ₁` and `ρ₂`.
Since `ρ₁` and `ρ₂` agree on commonly fixed variables (see `comp_comm`),
the result fixes the union of their fixed variables. -/
def comp (ρ₁ ρ₂ : _root_.Restriction N) (_hc : ρ₁.Compatible ρ₂) : _root_.Restriction N :=
  fun i => match ρ₁ i with
    | some b => some b
    | none => ρ₂ i

/-! ### Composition laws -/

theorem comp_comm {ρ₁ ρ₂ : _root_.Restriction N} (h : ρ₁.Compatible ρ₂) :
    ρ₁.comp ρ₂ h = ρ₂.comp ρ₁ h.symm := by
  apply ext; intro i; unfold comp
  cases h₁ : ρ₁ i <;> cases h₂ : ρ₂ i
  · rfl
  · rfl
  · rfl
  · exact congr_arg some (h i _ _ h₁ h₂)

@[simp]
theorem comp_trivial {ρ : _root_.Restriction N} (h : ρ.Compatible trivial) :
    ρ.comp trivial h = ρ := by
  apply ext; intro i; simp only [comp, trivial]; cases ρ i <;> rfl

@[simp]
theorem trivial_comp {ρ : _root_.Restriction N} (h : trivial.Compatible ρ) :
    trivial.comp ρ h = ρ := by
  apply ext; intro i; simp only [comp, trivial]

theorem Compatible.comp_left {ρ₁ ρ₂ ρ₃ : _root_.Restriction N}
    (h₁₂ : ρ₁.Compatible ρ₂) (h₁₃ : ρ₁.Compatible ρ₃) (h₂₃ : ρ₂.Compatible ρ₃) :
    ρ₁.Compatible (ρ₂.comp ρ₃ h₂₃) := by
  intro i b₁ b₂ hρ₁ hcomp
  unfold comp at hcomp
  cases h₂ : ρ₂ i
  · simp [h₂] at hcomp; exact h₁₃ i _ _ hρ₁ hcomp
  · simp [h₂] at hcomp; subst hcomp; exact h₁₂ i _ _ hρ₁ h₂

theorem Compatible.comp_right {ρ₁ ρ₂ ρ₃ : _root_.Restriction N}
    (h₁₂ : ρ₁.Compatible ρ₂) (h₁₃ : ρ₁.Compatible ρ₃) (h₂₃ : ρ₂.Compatible ρ₃) :
    (ρ₁.comp ρ₂ h₁₂).Compatible ρ₃ :=
  (h₁₃.symm.comp_left h₂₃.symm h₁₂).symm

theorem comp_assoc {ρ₁ ρ₂ ρ₃ : _root_.Restriction N}
    (h₁₂ : ρ₁.Compatible ρ₂) (h₂₃ : ρ₂.Compatible ρ₃) (h₁₃ : ρ₁.Compatible ρ₃) :
    (ρ₁.comp ρ₂ h₁₂).comp ρ₃ (h₁₂.comp_right h₁₃ h₂₃) =
    ρ₁.comp (ρ₂.comp ρ₃ h₂₃) (h₁₂.comp_left h₁₃ h₂₃) := by
  apply ext; intro i; simp only [comp]; cases ρ₁ i <;> rfl

/-! ### Free variable interaction -/

@[simp]
theorem isFree_trivial (i : Fin N) : trivial.isFree i := by
  simp [isFree, trivial]

theorem isFree_comp {ρ₁ ρ₂ : _root_.Restriction N} {h : ρ₁.Compatible ρ₂} {i : Fin N} :
    (ρ₁.comp ρ₂ h).isFree i ↔ ρ₁.isFree i ∧ ρ₂.isFree i := by
  simp only [isFree, comp]; cases ρ₁ i <;> simp

@[simp]
theorem freeVars_trivial : (trivial : _root_.Restriction N).freeVars = Finset.univ := by
  ext i; simp [freeVars]

@[simp]
theorem numFree_trivial : (trivial : _root_.Restriction N).numFree = N := by
  simp [numFree]

theorem freeVars_comp {ρ₁ ρ₂ : _root_.Restriction N} (h : ρ₁.Compatible ρ₂) :
    (ρ₁.comp ρ₂ h).freeVars = ρ₁.freeVars ∩ ρ₂.freeVars := by
  ext i; simp [freeVars, isFree_comp]

theorem freeVars_comp_subset_left {ρ₁ ρ₂ : _root_.Restriction N} (h : ρ₁.Compatible ρ₂) :
    (ρ₁.comp ρ₂ h).freeVars ⊆ ρ₁.freeVars := by
  rw [freeVars_comp]; exact Finset.inter_subset_left

theorem freeVars_comp_subset_right {ρ₁ ρ₂ : _root_.Restriction N} (h : ρ₁.Compatible ρ₂) :
    (ρ₁.comp ρ₂ h).freeVars ⊆ ρ₂.freeVars := by
  rw [freeVars_comp]; exact Finset.inter_subset_right

/-! ## fillIn / applyFun composition -/

/-- Composition of `fillIn`: applying the merged restriction at once is the same
as applying `ρ₁` with free variables filled in by `ρ₂` then by `x`. -/
theorem fillIn_comp {ρ₁ ρ₂ : _root_.Restriction N} (h : ρ₁.Compatible ρ₂)
    (x : (ρ₁.comp ρ₂ h).FreeVar → Bool) :
    (ρ₁.comp ρ₂ h).fillIn x = ρ₁.fillIn (fun ⟨i, hi⟩ =>
      match h₂ : ρ₂ i with
      | some b => b
      | none => x ⟨i, show (ρ₁.comp ρ₂ h) i = none by simp [comp, hi, h₂]⟩) := by
  funext i; unfold fillIn
  split <;> rename_i hci
  · unfold comp at hci; split <;> rename_i h₁i
    · simp_all
    · dsimp only; split <;> simp_all
  · unfold comp at hci; split <;> rename_i h₁i
    · simp [h₁i] at hci
    · simp [h₁i] at hci; dsimp only; split <;> simp_all

theorem applyFun_comp {ρ₁ ρ₂ : _root_.Restriction N} (h : ρ₁.Compatible ρ₂)
    (f : BitString N → Bool) (x : (ρ₁.comp ρ₂ h).FreeVar → Bool) :
    (ρ₁.comp ρ₂ h).applyFun f x = ρ₁.applyFun f (fun ⟨i, hi⟩ =>
      match h₂ : ρ₂ i with
      | some b => b
      | none => x ⟨i, show (ρ₁.comp ρ₂ h) i = none by simp [comp, hi, h₂]⟩) := by
  simp only [applyFun, Function.comp_def, fillIn_comp]

/-! ## Equivalence with `Fin numFree` -/

theorem card_freeVar_eq (ρ : _root_.Restriction N) :
    Fintype.card ρ.FreeVar = ρ.numFree := by
  unfold FreeVar numFree freeVars isFree; rw [Fintype.card_subtype]

/-- Equivalence between `Fin ρ.numFree` and the free variables of a restriction,
providing a canonical indexing of free variables as a `BitString`. -/
noncomputable def freeVarEquiv (ρ : _root_.Restriction N) : Fin ρ.numFree ≃ ρ.FreeVar :=
  (finCongr ρ.card_freeVar_eq.symm).trans (Fintype.equivFin ρ.FreeVar).symm

end Restriction
