import Mathlib.Data.Nat.Lattice

/-! # Boolean Circuit Complexity

This file defines Boolean circuits parameterized by a basis of operations and
establishes the circuit size complexity measure for Boolean functions.

## Main definitions

* `BitString` — a string of bits of a specific length
* `Basis` — a basis of Boolean operations with arity constraints
* `Circuit` — an acyclic Boolean circuit (well-formedness by construction)
* `CompleteBasis` — typeclass for functionally complete bases
* `Circuit.size_complexity` — minimum circuit size computing a given function

## Main results

* `Circuit.size_complexity_pos` — for complete bases, size complexity is positive
-/

/-- A BitString of length n. -/
abbrev BitString n := Fin n → Bool

/-- Arity constraint for operations in a basis. -/
inductive Arity where
  | unbounded
  | exactly (k : Nat)
  | upto (k : Nat)
  deriving Repr, DecidableEq

/-- Whether `n` inputs satisfies an arity constraint. -/
def Arity.satisfiedBy : Arity → Nat → Prop
  | .unbounded, _ => True
  | .exactly k, n => n = k
  | .upto k, n => n ≤ k

instance (a : Arity) (n : Nat) : Decidable (a.satisfiedBy n) := by
  cases a <;> simp only [Arity.satisfiedBy] <;> exact inferInstance

/--
A basis of Boolean operations.

Each operation has an arity constraint and an evaluation function that computes
the output bit from any valid number of input bits.
-/
structure Basis where
  /-- The type of operations (e.g., AND, OR, NOT). -/
  Op : Type
  /-- The arity constraint for each operation. -/
  arity : Op → Arity
  /-- Evaluate an operation on `n` input bits, given that `n` satisfies the arity. -/
  eval : (op : Op) → (n : Nat) → (arity op).satisfiedBy n → BitString n → Bool

/--
A gate in a circuit over basis `B` with `W` wires available as inputs.
The gate's fan-in must satisfy the arity constraint of its operation, and each
input is wired to one of the `W` available wires.
-/
structure Gate (B : Basis) (W : Nat) where
  op : B.Op
  fanIn : Nat
  arityOk : (B.arity op).satisfiedBy fanIn
  inputs : Fin fanIn → Fin W
  /-- Per-input negation flag. Negations are free in circuit complexity. -/
  negated : Fin fanIn → Bool

/-- Evaluate a gate given a wire-value assignment. -/
def Gate.eval (g : Gate B W) (wireVal : BitString W) : Bool :=
  B.eval g.op g.fanIn g.arityOk (fun i => (g.negated i).xor (wireVal (g.inputs i)))

/--
A Boolean circuit over basis `B` with `N` inputs, `M` outputs, and `G`
internal gates.

All gates reference wires from `Fin (N + G)`. The `acyclic` field ensures
that internal gate `i` only reads wires `0, …, N + i − 1`, preventing cycles.
-/
structure Circuit (B : Basis) (N M G : Nat) [NeZero N] [NeZero M] where
  gates : Fin G → Gate B (N + G)
  outputs : Fin M → Gate B (N + G)
  acyclic : ∀ (i : Fin G) (k : Fin (gates i).fanIn),
    ((gates i).inputs k).val < N + i.val

namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- Value of wire `w` when the circuit is fed `input`.

The first `N` wires carry the primary inputs. Wire `N + i` carries the
output of internal gate `i`. -/
def wireValue (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) : Bool :=
  if h : w.val < N then
    input ⟨w.val, h⟩
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    B.eval gate.op gate.fanIn gate.arityOk
      fun k => (gate.negated k).xor (c.wireValue input (gate.inputs k))
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

theorem wireValue_lt (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireValue input w = input ⟨w.val, h⟩ := by
  unfold wireValue
  simp [h]

theorem wireValue_ge (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : ¬ (w.val < N)) :
    c.wireValue input w =
      (c.gates ⟨w.val - N, by omega⟩).eval (c.wireValue input) := by
  unfold wireValue
  simp only [h, dite_false]
  rfl

/-- Evaluate a circuit: map an `N`-bit input to an `M`-bit output. -/
def eval (c : Circuit B N M G) (input : BitString N) : BitString M :=
  fun j => (c.outputs j).eval (c.wireValue input)

/-- The size of a circuit is its total number of gates (internal + output). -/
def size (_ : Circuit B N M G) : Nat := G + M

end Circuit

/-- A basis is complete if every Boolean function can be computed by some circuit over it. -/
class CompleteBasis (B : Basis) : Prop where
  complete : ∀ {N M} [NeZero N] [NeZero M] (f : BitString N → BitString M),
    ∃ G, ∃ c : Circuit B N M G, c.eval = f

namespace Circuit
variable {B : Basis} {N M : Nat} [NeZero N] [NeZero M]

/-- The minimum size circuit over basis `B` computing a given function.
    Returns 0 if no circuit over `B` computes `f`. -/
noncomputable def size_complexity
    (B : Basis) (f : BitString N → BitString M) : Nat :=
  sInf {s | ∃ G, ∃ c : Circuit B N M G, c.size = s ∧ c.eval = f}

private theorem size_complexity_set_nonempty [CompleteBasis B]
    (f : BitString N → BitString M) :
    {s | ∃ G, ∃ c : Circuit B N M G, c.size = s ∧ c.eval = f}.Nonempty :=
  let ⟨G, c, hc⟩ := CompleteBasis.complete (B := B) f
  ⟨c.size, G, c, rfl, hc⟩

/-- For a complete basis, circuit size complexity is always positive. -/
theorem size_complexity_pos [CompleteBasis B]
    (f : BitString N → BitString M) :
    0 < size_complexity B f := by
  obtain ⟨_, _, hs, _⟩ := Nat.sInf_mem (size_complexity_set_nonempty (B := B) f)
  simp only [size_complexity]
  rw [← hs, size]
  exact Nat.add_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne M))

end Circuit
