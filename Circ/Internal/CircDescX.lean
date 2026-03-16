import Circ.Internal.CircDesc

/-! # Internal: Extended Circuit Descriptors (AND/OR/NOT/XOR)

This module defines a circuit descriptor model for a basis with four
gate types: AND, OR, NOT, XOR. All gates use a uniform fan-in-2 encoding;
NOT ignores its second input.

The purpose — like `CircDesc` — is to provide a fintype-friendly
representation whose cardinality can be computed concretely for counting
arguments.

## Main definitions

* `GateSlotX` — gate descriptor: `(opcode, (wire1, wire2), (neg1, neg2))`
* `CircDescX` — circuit descriptor: `s` gates over `N + s` wires
* `wireValDX` / `evalDX` — evaluation functions

## Main results

* `card_gateSlotX` — each gate has `16 * W²` possible values
* `card_circDescX` — a size-`s` descriptor has `(16(N+s)²)^s` values
* `arith_bound_x` — `(16(N+s)²)^s < 2^(2^N)` for `s = 2^N/(5N)`, `N ≥ 6`
* `shannon_lower_bound_x` — pigeonhole: some function needs `> 2^N/(5N)` gates
-/

/-! ## Gate and Circuit Descriptors -/

/-- Gate type: AND (0), OR (1), NOT (2), XOR (3). -/
abbrev GateOpX := Fin 4

/-- Evaluate an extended gate given two (already-negated) input values. -/
def evalGateX (op : GateOpX) (v1 v2 : Bool) : Bool :=
  match op.val, op.isLt with
  | 0, _ => v1 && v2
  | 1, _ => v1 || v2
  | 2, _ => !v1
  | 3, _ => v1.xor v2
  | n + 4, h => absurd h (by omega)

/-- A gate in a fan-in-2 AND/OR/NOT/XOR circuit over wires `0..W-1`.
    Encodes `(opcode, (wire1, wire2), (neg1, neg2))`.
    NOT uses only `wire1`; the other three use both inputs.
    Per-input negation flags mirror the `Gate` model. -/
abbrev GateSlotX (W : Nat) := GateOpX × (Fin W × Fin W) × (Bool × Bool)

/-- A circuit descriptor with `N` primary inputs and `s` gates. -/
abbrev CircDescX (N s : Nat) := Fin s → GateSlotX (N + s)

/-! ## Wire and Circuit Evaluation -/

/-- Evaluate wire `w` in an extended circuit descriptor.
    Primary input wires return the corresponding input bit.
    Gate wires evaluate their gate, with forward references defaulting
    to `false`. -/
def wireValDX {N s : Nat} (d : CircDescX N s) (input : BitString N)
    (w : Fin (N + s)) : Bool :=
  if h : w.val < N then
    input ⟨w.val, h⟩
  else
    have hi : w.val - N < s := by omega
    let (op, (w1, w2), (n1, n2)) := d ⟨w.val - N, hi⟩
    let v1 := n1.xor (if w1.val < w.val then wireValDX d input ⟨w1.val, by omega⟩ else false)
    let v2 := n2.xor (if w2.val < w.val then wireValDX d input ⟨w2.val, by omega⟩ else false)
    evalGateX op v1 v2
termination_by w.val

/-- Evaluate an extended circuit descriptor: the output is the value of
    the last gate. -/
def evalDX {N s : Nat} (hs : 0 < s) (d : CircDescX N s) : BitString N → Bool :=
  fun input => wireValDX d input ⟨N + s - 1, by omega⟩

/-! ## Cardinality Lemmas -/

theorem card_gateSlotX (W : Nat) : Fintype.card (GateSlotX W) = 16 * W ^ 2 := by
  simp [GateSlotX, GateOpX, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]; ring

theorem card_circDescX (N s : Nat) :
    Fintype.card (CircDescX N s) = (16 * (N + s) ^ 2) ^ s := by
  simp only [CircDescX, Fintype.card_fun, Fintype.card_fin]; rw [card_gateSlotX]

/-! ## Arithmetic Bound -/

/-- `(2N+4) * s < 2^N` for `s = 2^N/(5N)` and `N ≥ 6`. -/
theorem mul_s_lt_two_pow_x (N : Nat) (hN : 6 ≤ N) :
    (2 * N + 4) * (2 ^ N / (5 * N)) < 2 ^ N := by
  calc (2 * N + 4) * (2 ^ N / (5 * N))
      < (5 * N) * (2 ^ N / (5 * N)) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (s_pos N hN)
    _ ≤ 2 ^ N := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _

/-- **Key arithmetic bound**: the number of extended circuit descriptors
    of size `s = 2^N/(5N)` is strictly less than the number of Boolean
    functions on `N` inputs. -/
theorem arith_bound_x (N : Nat) (hN : 6 ≤ N) :
    (16 * (N + 2 ^ N / (5 * N)) ^ 2) ^ (2 ^ N / (5 * N)) < 2 ^ 2 ^ N := by
  set s := 2 ^ N / (5 * N)
  have hspos : 0 < s := s_pos N hN
  have h1 : 16 * (N + s) ^ 2 < 2 ^ (2 * N + 4) := by
    have hns : N + s < 2 ^ N := n_plus_s_lt N hN
    have hsq : (N + s) ^ 2 < (2 ^ N) ^ 2 := Nat.pow_lt_pow_left hns (by omega)
    have : 2 ^ (2 * N + 4) = 16 * (2 ^ N) ^ 2 := by rw [← Nat.pow_mul, Nat.pow_add]; ring_nf
    omega
  have h2 : (2 * N + 4) * s < 2 ^ N := mul_s_lt_two_pow_x N hN
  calc (16 * (N + s) ^ 2) ^ s
      < (2 ^ (2 * N + 4)) ^ s := Nat.pow_lt_pow_left h1 (by omega)
    _ = 2 ^ ((2 * N + 4) * s) := by rw [← Nat.pow_mul]
    _ < 2 ^ (2 ^ N) := Nat.pow_lt_pow_right (by omega) h2

/-! ## Main Theorem -/

/-- **Shannon counting lower bound (extended basis)**: for `N ≥ 6`, there
    exists a Boolean function on `N` inputs that cannot be computed by any
    AND/OR/NOT/XOR circuit descriptor with `2^N / (5N)` gates. -/
theorem shannon_lower_bound_x (N : Nat) (hN : 6 ≤ N) :
    ∃ f : BitString N → Bool,
      ∀ (d : CircDescX N (2 ^ N / (5 * N))),
        evalDX (s_pos N hN) d ≠ f := by
  let s := 2 ^ N / (5 * N)
  let hs := s_pos N hN
  have h_lt : ((Finset.univ : Finset (CircDescX N s)).image (evalDX (N := N) (s := s) hs)).card
      < (Finset.univ : Finset (BitString N → Bool)).card := by
    calc ((Finset.univ : Finset (CircDescX N s)).image (evalDX hs)).card
        ≤ (Finset.univ : Finset (CircDescX N s)).card := Finset.card_image_le
      _ = Fintype.card (CircDescX N s) := Finset.card_univ
      _ = (16 * (N + s) ^ 2) ^ s := card_circDescX N s
      _ < 2 ^ 2 ^ N := arith_bound_x N hN
      _ = Fintype.card (BitString N → Bool) := (card_bool_fun N).symm
      _ = (Finset.univ : Finset (BitString N → Bool)).card := (Finset.card_univ).symm
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card h_lt
  exact ⟨f, fun d hd => hf (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hd⟩)⟩
