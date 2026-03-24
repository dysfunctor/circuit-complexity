import Circ.Internal.Restriction

/-! # Restrictions — Public API

This module provides the public API for restrictions (partial assignments of
Boolean variables): applying a restriction to a Boolean function, minterms,
and the maximum minterm length.

Core definitions (`Restriction`, `isFree`, `fillIn`, etc.) are in
`Circ.Internal.Restriction` and re-exported here.

## Main definitions

* `Restriction.restrict` — apply a restriction, producing a plain `BitString` function
* `Restriction.IsMinterm` — a minimal restriction making a function constantly true
* `Restriction.maxMintermLength` — the length of the longest minterm
-/

namespace Restriction

variable {N : Nat}

/-- Apply a restriction to a Boolean function, producing a plain Boolean function
on `ρ.numFree` input bits. Free variables are ordered canonically via
`freeVarEquiv`. -/
noncomputable def restrict (ρ : Restriction N) (f : BitString N → Bool) :
    BitString ρ.numFree → Bool :=
  fun x => f (ρ.fillIn (x ∘ ρ.freeVarEquiv.symm))

/-! ## Minterms -/

/-- A restriction `ρ` makes function `f` constantly true: for every
assignment to the free variables, `f` evaluates to `true`. -/
def MakesConstTrue (ρ : Restriction N) (f : BitString N → Bool) : Prop :=
  ∀ x : BitString ρ.numFree, ρ.restrict f x = true

/-- A minterm of `f` is a restriction `ρ` that makes `f` constantly true
and is minimal: unfixing any single fixed variable breaks this property. -/
def IsMinterm (f : BitString N → Bool) (ρ : Restriction N) : Prop :=
  ρ.MakesConstTrue f ∧ ∀ i : Fin N, ¬ρ.isFree i → ¬(ρ.unfix i).MakesConstTrue f

open Classical

/-- `maxMintermLength f` is the length of the longest minterm of `f`.
Returns 0 if `f` has no minterms. -/
noncomputable def maxMintermLength {N : Nat} (f : BitString N → Bool) : Nat :=
  (Finset.univ.filter (IsMinterm f)).sup Restriction.length

end Restriction
