import Circ.AON.Defs
import Circ.Internal.CircDescX

/-! # Internal: Bridge from CircDescX to Circuit Model (AND/OR/NOT/XOR)

This module connects the `CircDescX` counting model to the general
`Circuit` model for the `Basis.andOrNotXor2` basis.

The public theorem `shannon_lower_bound_circuit_x` proves that for `N ≥ 6`,
there exists a Boolean function on `N` inputs not computable by any
fan-in-2 AND/OR/NOT/XOR circuit with at most `2^N / (5N)` gates.
-/

/-! ## Encoding -/

/-- Map an `AONXOp` to its `GateOpX` (Fin 4) encoding. -/
def aonxOpToFin : AONXOp → GateOpX
  | .and => 0
  | .or  => 1
  | .not => 2
  | .xor => 3

/-- Encode a `Basis.andOrNotXor2` gate as a `GateSlotX`. -/
def encodeGateX {W W' : Nat} (g : Gate Basis.andOrNotXor2 W) (hW : W ≤ W') : GateSlotX W' :=
  have h2 := andOrNotXor2_fanIn g
  (aonxOpToFin g.op,
   (⟨(g.inputs ⟨0, by omega⟩).val, by omega⟩,
    ⟨(g.inputs ⟨1, by omega⟩).val, by omega⟩),
   (g.negated ⟨0, by omega⟩, g.negated ⟨1, by omega⟩))

/-- Encode a circuit over `Basis.andOrNotXor2` as an extended circuit
    descriptor. Internal gates map to positions `0..G-1`; the output gate
    to position `G`. -/
def circuitToDescX {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOrNotXor2 N 1 G) : CircDescX N (G + 1) := fun i =>
  if h : i.val < G then
    encodeGateX (c.gates ⟨i.val, h⟩) (by omega : N + G ≤ N + (G + 1))
  else
    encodeGateX (c.outputs 0) (by omega : N + G ≤ N + (G + 1))

/-! ## Semantic Equivalence -/

/-- Gate evaluation over `Basis.andOrNotXor2` matches the `GateSlotX`
    encoding semantics. -/
private theorem gate_eval_eq_slotX {W W' : Nat} (g : Gate Basis.andOrNotXor2 W) (hW : W ≤ W')
    (wireVal : Fin W → Bool) (wireVal' : Fin W' → Bool)
    (hwv : ∀ w : Fin W, wireVal w = wireVal' ⟨w.val, by omega⟩) :
    g.eval wireVal =
      let (op, (w1, w2), (n1, n2)) := encodeGateX g hW
      evalGateX op (n1.xor (wireVal' w1)) (n2.xor (wireVal' w2)) := by
  obtain ⟨op, fanIn, arityOk, inputs, negated⟩ := g
  change fanIn = 2 at arityOk
  subst arityOk
  cases op <;> simp [Gate.eval, Basis.andOrNotXor2, AONXOp.eval2, encodeGateX, aonxOpToFin,
    evalGateX, hwv]

/-- Wire values agree between `Circuit.wireValue` and `wireValDX` for
    wires in the range `0..N+G-1`. -/
theorem wireValue_eq_wireValDX {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOrNotXor2 N 1 G)
    (input : BitString N) (w : Fin (N + G)) :
    c.wireValue input w =
      wireValDX (circuitToDescX c) input ⟨w.val, by omega⟩ := by
  by_cases hwN : w.val < N
  · rw [Circuit.wireValue_lt _ _ _ hwN]
    conv_rhs => unfold wireValDX
    simp [hwN]
  · push_neg at hwN
    have hG : w.val - N < G := by omega
    rw [Circuit.wireValue_ge c input w (by omega)]
    have h2 : (c.gates ⟨w.val - N, hG⟩).fanIn = 2 := andOrNotXor2_fanIn _
    have hacyc0 : ((c.gates ⟨w.val - N, hG⟩).inputs ⟨0, by omega⟩).val < w.val := by
      have h := c.acyclic ⟨w.val - N, hG⟩ ⟨0, by omega⟩
      simp only [] at h; omega
    have hacyc1 : ((c.gates ⟨w.val - N, hG⟩).inputs ⟨1, by omega⟩).val < w.val := by
      have h := c.acyclic ⟨w.val - N, hG⟩ ⟨1, by omega⟩
      simp only [] at h; omega
    set gate := c.gates ⟨w.val - N, hG⟩ with gate_def
    have ih0 := wireValue_eq_wireValDX c input
      ⟨(gate.inputs ⟨0, by omega⟩).val, by omega⟩
    have ih1 := wireValue_eq_wireValDX c input
      ⟨(gate.inputs ⟨1, by omega⟩).val, by omega⟩
    conv_rhs => unfold wireValDX
    simp only [show ¬((⟨w.val, (by omega : w.val < N + (G + 1))⟩ : Fin (N + (G + 1))).val < N)
      from by simp; omega, dite_false]
    simp only [circuitToDescX, show (⟨w.val - N, (by omega : w.val - N < G + 1)⟩ :
      Fin (G + 1)).val < G from hG, dite_true, encodeGateX, Fin.val_mk]
    have hgate : ∀ h : w.val - N < G, c.gates ⟨w.val - N, h⟩ = gate :=
      fun h => (congrArg c.gates (Fin.ext rfl)).trans gate_def.symm
    simp_rw [hgate]
    simp only [hacyc0, hacyc1, ↓reduceIte]
    rw [← ih0, ← ih1]
    suffices h : ∀ (h' : ↑w - N < G) (j : Fin (c.gates ⟨↑w - N, h'⟩).fanIn),
        (c.gates ⟨↑w - N, h'⟩).negated j =
          gate.negated (j.cast (show (c.gates ⟨↑w - N, h'⟩).fanIn = gate.fanIn by
            rw [hgate h'])) by
      simp only [h, Fin.cast_mk]
      have := gate_eval_eq_slotX gate (show N + G ≤ N + G by omega)
        (c.wireValue input) (c.wireValue input) (fun _ => rfl)
      rw [this]; clear this
      simp [encodeGateX]
    intro h' j
    exact (show ∀ (g : Gate Basis.andOrNotXor2 (N + G)) (heq : g = c.gates ⟨↑w - N, h'⟩)
        (hfanIn : (c.gates ⟨↑w - N, h'⟩).fanIn = g.fanIn)
        (j : Fin (c.gates ⟨↑w - N, h'⟩).fanIn),
        (c.gates ⟨↑w - N, h'⟩).negated j = g.negated (j.cast hfanIn)
      from fun g heq _ j => by subst heq; rfl)
      _ (hgate h').symm (by simp [hgate h']) j
  termination_by w.val

/-- Circuit evaluation agrees with extended descriptor evaluation. -/
theorem circuit_eval_eq_evalDX {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOrNotXor2 N 1 G) :
    (fun x => (c.eval x) 0) = evalDX (Nat.succ_pos G) (circuitToDescX c) := by
  funext x
  simp only [Circuit.eval, evalDX]
  rw [gate_eval_eq_slotX (c.outputs 0) (by omega : N + G ≤ N + (G + 1))
    (c.wireValue x) _ (fun w => wireValue_eq_wireValDX c x w)]
  conv_rhs => unfold wireValDX
  simp only []
  simp only [circuitToDescX, show ¬((⟨N + G.succ - 1 - N, (by omega : N + G.succ - 1 - N < G + 1)⟩ :
    Fin (G + 1)).val < G) from by simp, dite_false]
  have h2 := andOrNotXor2_fanIn (c.outputs 0)
  simp only [encodeGateX, Fin.val_mk,
    show ((c.outputs 0).inputs ⟨0, by omega⟩).val < N + G.succ - 1 from by
      exact Nat.lt_of_lt_of_le ((c.outputs 0).inputs ⟨0, by omega⟩).isLt (by omega),
    show ((c.outputs 0).inputs ⟨1, by omega⟩).val < N + G.succ - 1 from by
      exact Nat.lt_of_lt_of_le ((c.outputs 0).inputs ⟨1, by omega⟩).isLt (by omega),
    ite_true]
  simp only [show ¬(N + G.succ - 1 < N) from by omega, dite_false]

/-! ## Padding -/

/-- Pad an extended descriptor to a larger size by appending copy gates.
    Each padded gate is `OR(last_output, last_output)` with no negation,
    which copies the original output value. -/
def padDescX {N s : Nat} (d : CircDescX N s) (s' : Nat) (hs : 0 < s) (h : s ≤ s') :
    CircDescX N s' := fun i =>
  if hi : i.val < s then
    let (op, (w1, w2), negs) := d ⟨i.val, hi⟩
    (op, (⟨w1.val, by omega⟩, ⟨w2.val, by omega⟩), negs)
  else
    (1, (⟨N + s - 1, by omega⟩, ⟨N + s - 1, by omega⟩), (false, false))

private theorem wireValDX_padDescX_lt {N s s' : Nat} (d : CircDescX N s) (hs : 0 < s)
    (h : s ≤ s') (x : BitString N) (w : Fin (N + s')) (hw : w.val < N + s) :
    wireValDX (padDescX d s' hs h) x w =
      wireValDX d x ⟨w.val, hw⟩ := by
  by_cases hwN : w.val < N
  · simp [wireValDX, hwN]
  · push_neg at hwN
    have hi : w.val - N < s := by omega
    conv_lhs => unfold wireValDX
    simp only [show ¬(w.val < N) from by omega, dite_false]
    conv_rhs => unfold wireValDX
    simp only [show ¬(w.val < N) from by omega, dite_false]
    simp only [padDescX, show (w.val - N) < s from hi, dite_true]
    -- Normalize all d ⟨↑w - N, _⟩ to use the same Fin proof
    have hfin : ∀ (p : ↑w - N < s), d ⟨↑w - N, p⟩ = d ⟨↑w - N, hi⟩ :=
      fun p => congrArg d (Fin.ext rfl)
    simp_rw [hfin]
    -- Show the two if-expressions agree (by IH in the true branch)
    have h_if1 : (if (d ⟨↑w - N, hi⟩).2.1.1.val < w.val
        then wireValDX (padDescX d s' hs h) x ⟨(d ⟨↑w - N, hi⟩).2.1.1.val, by omega⟩
        else false) =
      (if (d ⟨↑w - N, hi⟩).2.1.1.val < w.val
        then wireValDX d x (d ⟨↑w - N, hi⟩).2.1.1
        else false) := by
      split_ifs with hlt
      · exact wireValDX_padDescX_lt d hs h x _ (d ⟨↑w - N, hi⟩).2.1.1.isLt
      · rfl
    have h_if2 : (if (d ⟨↑w - N, hi⟩).2.1.2.val < w.val
        then wireValDX (padDescX d s' hs h) x ⟨(d ⟨↑w - N, hi⟩).2.1.2.val, by omega⟩
        else false) =
      (if (d ⟨↑w - N, hi⟩).2.1.2.val < w.val
        then wireValDX d x (d ⟨↑w - N, hi⟩).2.1.2
        else false) := by
      split_ifs with hlt
      · exact wireValDX_padDescX_lt d hs h x _ (d ⟨↑w - N, hi⟩).2.1.2.isLt
      · rfl
    simp only [h_if1, h_if2]
  termination_by w.val

private theorem wireValDX_padDescX_ge {N s s' : Nat} (d : CircDescX N s) (hs : 0 < s)
    (h : s ≤ s') (x : BitString N) (w : Fin (N + s')) (hw : N + s ≤ w.val) :
    wireValDX (padDescX d s' hs h) x w =
      wireValDX d x ⟨N + s - 1, by omega⟩ := by
  conv_lhs => unfold wireValDX
  simp only [show ¬(w.val < N) from by omega, dite_false]
  simp only [padDescX, show ¬(w.val - N < s) from by omega, dite_false]
  simp only [Bool.false_xor, show (N + s - 1 : Nat) < w.val from by omega, ↓reduceIte]
  conv_lhs => rw [show ∀ v1 v2 : Bool, evalGateX 1 v1 v2 = (v1 || v2) from fun _ _ => rfl]
  simp only [Bool.or_self]
  have hlt : N + s - 1 < N + s := by omega
  exact wireValDX_padDescX_lt d hs h x ⟨N + s - 1, by omega⟩ hlt

theorem evalDX_padDescX {N s s' : Nat} (d : CircDescX N s) (hs : 0 < s)
    (h : s ≤ s') (hs' : 0 < s') :
    evalDX hs' (padDescX d s' hs h) = evalDX hs d := by
  funext x
  simp only [evalDX]
  by_cases hsle : N + s ≤ N + s' - 1
  · rw [wireValDX_padDescX_ge d hs h x ⟨N + s' - 1, by omega⟩ (by omega)]
  · push_neg at hsle
    have : s = s' := by omega
    subst this
    exact wireValDX_padDescX_lt d hs h x ⟨N + s - 1, by omega⟩ (by omega)

/-! ## Main Theorem -/

/-- **Shannon lower bound for AND/OR/NOT/XOR circuits**: for `N ≥ 6`, there
    exists a Boolean function on `N` inputs not computable by any fan-in-2
    AND/OR/NOT/XOR circuit with at most `2^N / (5N)` total gates. -/
theorem shannon_lower_bound_circuit_x (N : Nat) [NeZero N] (hN : 6 ≤ N) :
    ∃ f : BitString N → Bool,
      ∀ G (c : Circuit Basis.andOrNotXor2 N 1 G),
        G + 1 ≤ 2 ^ N / (5 * N) →
        (fun x => (c.eval x) 0) ≠ f := by
  obtain ⟨f, hf⟩ := shannon_lower_bound_x N hN
  exact ⟨f, fun G c hsize habs => by
    have hspos := s_pos N hN
    have hG1 : 0 < G + 1 := Nat.succ_pos G
    let d := circuitToDescX c
    let d' := padDescX d (2 ^ N / (5 * N)) hG1 hsize
    have h1 : evalDX hspos d' = evalDX hG1 d := evalDX_padDescX d hG1 hsize hspos
    have h2 : (fun x => (c.eval x) 0) = evalDX hG1 d := circuit_eval_eq_evalDX c
    have h3 : evalDX hspos d' = f := by rw [h1, ← h2, habs]
    exact hf d' h3⟩
