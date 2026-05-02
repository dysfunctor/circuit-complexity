import Circ.NC1Lin
import Circ.Internal.Foldl

/-! # Σ₃ representation as a depth-3 OR-AND-OR circuit

This file packages a `Sigma3Rep N ε f` as a concrete depth-3
`Circuit Basis.unboundedAON` and defines the depth-3-circuit complexity
measure `Sigma3CircuitSize`.

## Layout

The circuit produced by `Sigma3Rep.toCircuit` has:
* **Bottom layer** (`numClauses` OR gates): one per clause across all CNFs,
  reading directly from primary inputs. Linear indexing into the
  `(i, j)` pair `(CNF, clause-within-CNF)` is via `finSigmaFinEquiv`.
* **Middle layer** (`t` AND gates): one per CNF, ANDing that CNF's
  bottom-OR clause gates.
* **Top layer**: a single output OR over the `t` middle ANDs.

## Main definitions

* `Sigma3Rep.toCircuit` — the depth-3 circuit constructor.
* `Sigma3CircuitSize` — the depth-3 OR-AND-OR complexity measure.

## Main results

* `Sigma3Rep.toCircuit_eval` — correctness.
* `Sigma3Rep.toCircuit_depth_le` — depth ≤ 3.
* `Sigma3CircuitSize_le_Sigma3` — the circuit measure is ≤ `Sigma3`.
-/

namespace Sigma3Rep

variable {N : Nat} [NeZero N] {ε : ℝ} {f : BitString N → Bool}

/-! ### Sizing -/

/-- Total clause count across all CNFs of the representation. Equals the
size of the bottom OR-layer of the corresponding depth-3 circuit. -/
def numClauses (rep : Sigma3Rep N ε f) : Nat :=
  ∑ i : Fin rep.t, (rep.cnfs i).complexity

/-- Internal-gate count of `Sigma3Rep.toCircuit`: `numClauses` bottom-OR
gates plus `t` middle-AND gates. Reducible so `omega` can see through it. -/
abbrev numGates (rep : Sigma3Rep N ε f) : Nat := rep.numClauses + rep.t

/-! ### Per-layer gate descriptions -/

/-- The bottom-OR gate for clause linear-index `m < numClauses`. -/
def bottomGate (rep : Sigma3Rep N ε f) (m : Fin rep.numClauses) :
    Gate Basis.unboundedAON (N + rep.numGates) :=
  let ij := finSigmaFinEquiv.symm m
  let clause := (rep.cnfs ij.1).clauses.get ⟨ij.2.val, ij.2.isLt⟩
  { op := AONOp.or
    fanIn := clause.length
    arityOk := trivial
    inputs := fun k => ⟨(clause.get k).var.val, by
      have := (clause.get k).var.isLt; omega⟩
    negated := fun k => !(clause.get k).polarity }

/-- The middle-AND gate for CNF `i`. Reads the `(rep.cnfs i).complexity`
bottom-OR gates whose linear indices are `finSigmaFinEquiv ⟨i, k⟩`. -/
def middleGate (rep : Sigma3Rep N ε f) (i : Fin rep.t) :
    Gate Basis.unboundedAON (N + rep.numGates) :=
  { op := AONOp.and
    fanIn := (rep.cnfs i).complexity
    arityOk := trivial
    inputs := fun k =>
      let m : Fin rep.numClauses := finSigmaFinEquiv ⟨i, k⟩
      ⟨N + m.val, by
        have := m.isLt
        unfold numGates; omega⟩
    negated := fun _ => false }

/-- The output OR gate, reading from the `t` middle-AND gates. -/
def topGate (rep : Sigma3Rep N ε f) :
    Gate Basis.unboundedAON (N + rep.numGates) :=
  { op := AONOp.or
    fanIn := rep.t
    arityOk := trivial
    inputs := fun i => ⟨N + rep.numClauses + i.val, by
      have := i.isLt; unfold numGates; omega⟩
    negated := fun _ => false }

/-! ### Internal-gate function (split out so that `acyclic` can rewrite) -/

/-- The internal-gate function of `Sigma3Rep.toCircuit`. Bottom-OR for
indices `< numClauses`, middle-AND otherwise. -/
def gateAt (rep : Sigma3Rep N ε f) (m : Fin rep.numGates) :
    Gate Basis.unboundedAON (N + rep.numGates) :=
  if h : m.val < rep.numClauses then
    rep.bottomGate ⟨m.val, h⟩
  else
    rep.middleGate ⟨m.val - rep.numClauses, by
      have hm := m.isLt; unfold numGates at hm; omega⟩

omit [NeZero N] in
@[simp] lemma gateAt_lt (rep : Sigma3Rep N ε f) (m : Fin rep.numGates)
    (h : m.val < rep.numClauses) :
    rep.gateAt m = rep.bottomGate ⟨m.val, h⟩ := dif_pos h

omit [NeZero N] in
@[simp] lemma gateAt_ge (rep : Sigma3Rep N ε f) (m : Fin rep.numGates)
    (h : ¬ m.val < rep.numClauses) :
    rep.gateAt m = rep.middleGate ⟨m.val - rep.numClauses, by
      have hm := m.isLt; unfold numGates at hm; omega⟩ :=
  dif_neg h

/-! ### The circuit -/

/-- Build a depth-3 OR-AND-OR circuit over `Basis.unboundedAON` from a
Σ₃ representation. -/
def toCircuit (rep : Sigma3Rep N ε f) :
    Circuit Basis.unboundedAON N 1 rep.numGates where
  gates := rep.gateAt
  outputs _ := rep.topGate
  acyclic m := by
    by_cases h : m.val < rep.numClauses
    · rw [rep.gateAt_lt m h]
      intro k
      dsimp only [bottomGate]
      have hVar :=
        (((rep.cnfs (finSigmaFinEquiv.symm ⟨m.val, h⟩).1).clauses.get
          ⟨(finSigmaFinEquiv.symm ⟨m.val, h⟩).2.val,
            (finSigmaFinEquiv.symm ⟨m.val, h⟩).2.isLt⟩).get k).var.isLt
      omega
    · rw [rep.gateAt_ge m h]
      intro k
      dsimp only [middleGate]
      have hk : (finSigmaFinEquiv (n := fun i' : Fin rep.t => (rep.cnfs i').complexity)
          ⟨⟨m.val - rep.numClauses, by
            have hm := m.isLt; unfold numGates at hm; omega⟩, k⟩).val < rep.numClauses :=
        (finSigmaFinEquiv _).isLt
      omega

/-! ### Depth bound

The strategy is to bound the wireDepth at every gate-output wire by `1`
(bottom-OR layer) or `2` (middle-AND layer), then add `1` for the output
gate. The dependent typing of `(c.gates i).inputs k` (with `k`'s type
depending on `c.gates i`) is sidestepped by transporting via the
`gateAt_lt`/`gateAt_ge` rewrites before introducing `k`. -/

/-- `wireDepth` at a bottom-OR wire is at most `1`. -/
private lemma toCircuit_wireDepth_bottom (rep : Sigma3Rep N ε f)
    (w : Fin (N + rep.numGates)) (hN : ¬ w.val < N)
    (hC : w.val < N + rep.numClauses) :
    rep.toCircuit.wireDepth w ≤ 1 := by
  rw [Circuit.gateWireDepth _ w hN]
  have hidx : w.val - N < rep.numClauses := by omega
  have hbound : ∀ (k : Fin (rep.toCircuit.gates
        ⟨w.val - N, by have := w.isLt; omega⟩).fanIn),
      rep.toCircuit.wireDepth
        ((rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩).inputs k) ≤ 0 := by
    show ∀ k, _
    rw [show rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩ =
        rep.bottomGate ⟨w.val - N, hidx⟩ from rep.gateAt_lt _ hidx]
    intro k
    have hlt :
        (((rep.cnfs (finSigmaFinEquiv.symm ⟨w.val - N, hidx⟩).1).clauses.get
              ⟨(finSigmaFinEquiv.symm ⟨w.val - N, hidx⟩).2.val,
                (finSigmaFinEquiv.symm ⟨w.val - N, hidx⟩).2.isLt⟩).get k).var.val < N :=
      (((rep.cnfs (finSigmaFinEquiv.symm ⟨w.val - N, hidx⟩).1).clauses.get
            ⟨(finSigmaFinEquiv.symm ⟨w.val - N, hidx⟩).2.val,
              (finSigmaFinEquiv.symm ⟨w.val - N, hidx⟩).2.isLt⟩).get k).var.isLt
    rw [Circuit.inputWireDepth _ _ hlt]
  have hfold :
      Fin.foldl (rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩).fanIn
        (fun acc k => max acc (rep.toCircuit.wireDepth
          ((rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩).inputs k))) 0
        ≤ 0 :=
    Circuit.fin_foldl_max_le_ub _ 0 0 (le_refl _) hbound
  omega

/-- `wireDepth` at a middle-AND wire is at most `2`. -/
private lemma toCircuit_wireDepth_middle (rep : Sigma3Rep N ε f)
    (w : Fin (N + rep.numGates)) (hC : N + rep.numClauses ≤ w.val) :
    rep.toCircuit.wireDepth w ≤ 2 := by
  have hN : ¬ w.val < N := by omega
  rw [Circuit.gateWireDepth _ w hN]
  have hidx : ¬ (w.val - N) < rep.numClauses := by omega
  have hbound : ∀ (k : Fin (rep.toCircuit.gates
        ⟨w.val - N, by have := w.isLt; omega⟩).fanIn),
      rep.toCircuit.wireDepth
        ((rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩).inputs k) ≤ 1 := by
    show ∀ k, _
    rw [show rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩ =
        rep.middleGate ⟨w.val - N - rep.numClauses, by
          have := w.isLt; unfold numGates at this; omega⟩ from
      rep.gateAt_ge _ hidx]
    intro k
    have hflt : (finSigmaFinEquiv
          (n := fun i'' : Fin rep.t => (rep.cnfs i'').complexity)
          ⟨⟨w.val - N - rep.numClauses, by
            have := w.isLt; unfold numGates at this; omega⟩, k⟩).val
        < rep.numClauses :=
      (finSigmaFinEquiv (n := fun i'' : Fin rep.t => (rep.cnfs i'').complexity)
        ⟨⟨w.val - N - rep.numClauses, by
          have := w.isLt; unfold numGates at this; omega⟩, k⟩).isLt
    have hwk_ge : ¬ ((rep.middleGate ⟨w.val - N - rep.numClauses, by
          have := w.isLt; unfold numGates at this; omega⟩).inputs k).val < N := by
      show ¬ (N + _ < N); omega
    have hwk_lt : ((rep.middleGate ⟨w.val - N - rep.numClauses, by
          have := w.isLt; unfold numGates at this; omega⟩).inputs k).val
        < N + rep.numClauses := by
      show N + _ < N + rep.numClauses; omega
    exact rep.toCircuit_wireDepth_bottom _ hwk_ge hwk_lt
  have hfold :
      Fin.foldl (rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩).fanIn
        (fun acc k => max acc (rep.toCircuit.wireDepth
          ((rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩).inputs k))) 0
        ≤ 1 :=
    Circuit.fin_foldl_max_le_ub _ 0 1 (Nat.zero_le _) hbound
  omega

/-- The depth-3 circuit constructed from a `Sigma3Rep` has depth at most 3. -/
theorem toCircuit_depth_le (rep : Sigma3Rep N ε f) :
    rep.toCircuit.depth ≤ 3 := by
  have h0 : rep.toCircuit.outputDepth ⟨0, by omega⟩ ≤ 3 := by
    show 1 + Fin.foldl _ _ 0 ≤ 3
    have hbound : ∀ k : Fin (rep.toCircuit.outputs ⟨0, by omega⟩).fanIn,
        rep.toCircuit.wireDepth
          ((rep.toCircuit.outputs ⟨0, by omega⟩).inputs k) ≤ 2 := by
      intro k
      have h_ge : N + rep.numClauses ≤
          ((rep.toCircuit.outputs ⟨0, by omega⟩).inputs k).val := by
        show N + rep.numClauses ≤ N + rep.numClauses + k.val; omega
      exact rep.toCircuit_wireDepth_middle _ h_ge
    have hfold :
        Fin.foldl (rep.toCircuit.outputs ⟨0, by omega⟩).fanIn
          (fun acc k => max acc (rep.toCircuit.wireDepth
            ((rep.toCircuit.outputs ⟨0, by omega⟩).inputs k))) 0 ≤ 2 :=
      Circuit.fin_foldl_max_le_ub _ 0 2 (Nat.zero_le _) hbound
    omega
  unfold Circuit.depth
  have hfold :
      Fin.foldl 1 (fun acc j => max acc (rep.toCircuit.outputDepth j)) 0 ≤ 3 :=
    Circuit.fin_foldl_max_le_ub _ 0 3 (by omega) (fun j => by
      match j with | ⟨0, _⟩ => exact h0)
  exact hfold

/-! ### Correctness

The proof descends through three layers via `wireValue` computations:
* primary inputs (`< N`) carry the input bits,
* bottom-OR wires evaluate to clause-ORs,
* middle-AND wires evaluate to `(rep.cnfs i).eval x`.

Then the output OR yields `∃ i, (rep.cnfs i).eval x`, which equals `f x`
by `rep.correctness` (since the sum of indicators equals `if f x then 1 else 0`). -/

/-- WireValue at the bottom-OR wire `⟨N + m.val, _⟩` equals the
corresponding clause's OR-eval. -/
private lemma toCircuit_wireValue_bottom (rep : Sigma3Rep N ε f)
    (m : Fin rep.numClauses) (x : BitString N) :
    rep.toCircuit.wireValue x
        ⟨N + m.val, by have := m.isLt; unfold numGates; omega⟩ =
      ((rep.cnfs (finSigmaFinEquiv.symm m).1).clauses.get
          ⟨(finSigmaFinEquiv.symm m).2.val, (finSigmaFinEquiv.symm m).2.isLt⟩).any
        (fun l => l.eval x) := by
  set w : Fin (N + rep.numGates) :=
    ⟨N + m.val, by have := m.isLt; unfold numGates; omega⟩
  have hN : ¬ w.val < N := by show ¬ N + m.val < N; omega
  have hidx : w.val - N < rep.numClauses := by
    show N + m.val - N < rep.numClauses; have := m.isLt; omega
  have h_idx_eq : (⟨w.val - N, hidx⟩ : Fin rep.numClauses) = m := by
    apply Fin.ext; show N + m.val - N = m.val; omega
  rw [Circuit.wireValue_ge _ x w hN]
  rw [show rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩ =
        rep.bottomGate ⟨w.val - N, hidx⟩ from rep.gateAt_lt _ hidx]
  rw [show (⟨w.val - N, hidx⟩ : Fin rep.numClauses) = m from h_idx_eq]
  simp only [Gate.eval, bottomGate, Basis.unboundedAON, AONOp.eval]
  set clause := (rep.cnfs (finSigmaFinEquiv.symm m).1).clauses.get
      ⟨(finSigmaFinEquiv.symm m).2.val, (finSigmaFinEquiv.symm m).2.isLt⟩
  conv_lhs => arg 2; ext acc k; arg 2
              rw [Circuit.wireValue_lt _ x _ ((clause.get k).var.isLt)]
              rw [xor_neg_polarity_eq_eval]
  exact foldl_bor_eq_list_any clause (fun l => l.eval x)

/-- WireValue at a middle-AND wire equals `(rep.cnfs i).eval x`. -/
private lemma toCircuit_wireValue_middle (rep : Sigma3Rep N ε f)
    (i : Fin rep.t) (x : BitString N) :
    rep.toCircuit.wireValue x ⟨N + rep.numClauses + i.val, by
        have := i.isLt; unfold numGates; omega⟩ =
      (rep.cnfs i).eval x := by
  set w : Fin (N + rep.numGates) :=
    ⟨N + rep.numClauses + i.val, by have := i.isLt; unfold numGates; omega⟩
  have hN : ¬ w.val < N := by show ¬ N + rep.numClauses + i.val < N; omega
  have hidx : ¬ (w.val - N) < rep.numClauses := by
    show ¬ (N + rep.numClauses + i.val - N) < rep.numClauses; omega
  have h_i_eq : (⟨w.val - N - rep.numClauses, by
      have := w.isLt; unfold numGates at this; omega⟩ : Fin rep.t) = i := by
    apply Fin.ext
    show N + rep.numClauses + i.val - N - rep.numClauses = i.val; omega
  rw [Circuit.wireValue_ge _ x w hN]
  rw [show rep.toCircuit.gates ⟨w.val - N, by have := w.isLt; omega⟩ =
        rep.middleGate ⟨w.val - N - rep.numClauses, by
          have := w.isLt; unfold numGates at this; omega⟩ from rep.gateAt_ge _ hidx]
  rw [show (⟨w.val - N - rep.numClauses, by
      have := w.isLt; unfold numGates at this; omega⟩ : Fin rep.t) = i from h_i_eq]
  change Fin.foldl (rep.cnfs i).complexity
      (fun acc (k : Fin (rep.cnfs i).complexity) =>
        acc && (false.xor (rep.toCircuit.wireValue x ((rep.middleGate i).inputs k))))
      true = (rep.cnfs i).eval x
  conv_lhs => arg 2; ext acc k; rw [Bool.false_xor]
  have h_step : ∀ k : Fin (rep.cnfs i).complexity,
      rep.toCircuit.wireValue x ((rep.middleGate i).inputs k) =
        ((rep.cnfs i).clauses.get ⟨k.val, k.isLt⟩).any (fun l => l.eval x) := by
    intro k
    have hbot := rep.toCircuit_wireValue_bottom
      (finSigmaFinEquiv (n := fun i' : Fin rep.t => (rep.cnfs i').complexity)
        ⟨i, k⟩) x
    rw [Equiv.symm_apply_apply] at hbot
    exact hbot
  conv_lhs => arg 2; ext acc k; rw [h_step k]
  show Fin.foldl (rep.cnfs i).clauses.length _ _ = _
  exact foldl_band_eq_list_all (rep.cnfs i).clauses (fun clause => clause.any (fun l => l.eval x))

/-- The depth-3 circuit constructed from a `Sigma3Rep` correctly computes `f`. -/
theorem toCircuit_eval (rep : Sigma3Rep N ε f) :
    (fun x => (rep.toCircuit.eval x) 0) = f := by
  funext x
  change Fin.foldl rep.t (fun acc (i : Fin rep.t) =>
      acc || (false.xor (rep.toCircuit.wireValue x ((rep.topGate).inputs i)))) false = f x
  have h_step : ∀ i : Fin rep.t,
      rep.toCircuit.wireValue x ((rep.topGate).inputs i) = (rep.cnfs i).eval x := by
    intro i
    have hmid := rep.toCircuit_wireValue_middle i x
    exact hmid
  conv_lhs => arg 2; ext acc i; rw [Bool.false_xor]; rw [h_step i]
  have hOR : Fin.foldl rep.t
      (fun acc (i : Fin rep.t) => acc || (rep.cnfs i).eval x) false = true ↔
      ∃ i, (rep.cnfs i).eval x = true :=
    foldl_bor_eq_true (fun i => (rep.cnfs i).eval x)
  have hsum := rep.correctness x
  by_cases hex : ∃ i, (rep.cnfs i).eval x = true
  · rw [hOR.mpr hex]
    obtain ⟨i, hi⟩ := hex
    have h_pos : 0 < ∑ j : Fin rep.t,
        (if (rep.cnfs j).eval x then 1 else 0 : ℕ) :=
      Finset.sum_pos' (fun j _ => by split_ifs <;> simp)
        ⟨i, Finset.mem_univ _, by rw [hi]; simp⟩
    cases hfx : f x
    · rw [hfx, show (if false = true then (1 : ℕ) else 0) = 0 from rfl] at hsum
      omega
    · rfl
  · push_neg at hex
    have hall : ∀ i, (rep.cnfs i).eval x = false := fun i =>
      Bool.eq_false_iff.mpr (hex i)
    have hLHS_false : Fin.foldl rep.t
        (fun acc (i : Fin rep.t) => acc || (rep.cnfs i).eval x) false = false := by
      rw [Bool.eq_false_iff]
      intro h; obtain ⟨i, hi⟩ := hOR.mp h; exact hex i hi
    rw [hLHS_false]
    have h_zero : (∑ j : Fin rep.t,
        (if (rep.cnfs j).eval x then 1 else 0 : ℕ)) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [hall j]; simp)
    rw [h_zero] at hsum
    cases hfx : f x
    · rfl
    · rw [hfx] at hsum; simp at hsum

end Sigma3Rep

/-! ## Depth-3 OR-AND-OR circuit complexity measure -/

/-- The depth-3 OR-AND-OR complexity of `f` with bottom-layer ε-clause-count
parameter: the smallest `t` such that some unbounded-fan-in AON circuit
of depth ≤ 3 computes `f` with output-OR fan-in `t`, and each middle-layer
AND gate has fan-in at most `2 ^ (N ^ ε)`. (Returns `0` if no such circuit
exists; in particular, `0` for `N = 0` since `Circuit` requires `NeZero N`.) -/
noncomputable def Sigma3CircuitSize {N : Nat}
    (ε : ℝ) (f : BitString N → Bool) : ℕ :=
  sInf {t | ∃ (_ : NeZero N) (G : ℕ) (c : Circuit Basis.unboundedAON N 1 G),
    c.depth ≤ 3 ∧
    (c.outputs 0).op = AONOp.or ∧
    (c.outputs 0).fanIn = t ∧
    (∀ k : Fin (c.outputs 0).fanIn,
      ∃ (i : Fin G),
        ((c.outputs 0).inputs k).val = N + i.val ∧
        (c.gates i).op = AONOp.and ∧
        ((c.gates i).fanIn : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) ^ ε)) ∧
    (fun x => (c.eval x) 0) = f}

/-- Per-rep bound: any `Sigma3Rep` of size `t` realizes a depth-3 OR-AND-OR
circuit of the same size, hence `Sigma3CircuitSize ε f ≤ rep.t`. -/
theorem Sigma3CircuitSize_le_of_rep {N : Nat} [hN : NeZero N]
    {ε : ℝ} {f : BitString N → Bool} (rep : Sigma3Rep N ε f) :
    Sigma3CircuitSize ε f ≤ rep.t := by
  unfold Sigma3CircuitSize
  apply Nat.sInf_le
  refine ⟨hN, rep.numGates, rep.toCircuit, rep.toCircuit_depth_le, rfl, rfl, ?_,
    rep.toCircuit_eval⟩
  intro k
  have hk : k.val < rep.t := k.isLt
  have hgate : rep.toCircuit.gates ⟨rep.numClauses + k.val, by
        unfold Sigma3Rep.numGates; omega⟩ = rep.middleGate k := by
    show rep.gateAt _ = _
    rw [rep.gateAt_ge _ (by show ¬ rep.numClauses + k.val < rep.numClauses; omega)]
    congr 1
    apply Fin.ext; show rep.numClauses + k.val - rep.numClauses = k.val; omega
  refine ⟨⟨rep.numClauses + k.val, by unfold Sigma3Rep.numGates; omega⟩, ?_, ?_, ?_⟩
  · show N + rep.numClauses + k.val = N + (rep.numClauses + k.val); omega
  · rw [hgate]; rfl
  · rw [hgate]; exact rep.clause_bound k

/-- The circuit-flavored measure `Sigma3CircuitSize` is upper bounded by
the Σ₃-rep measure `Sigma3` whenever a `Sigma3Rep` exists. -/
theorem Sigma3CircuitSize_le_Sigma3 {N : Nat} [NeZero N]
    {ε : ℝ} {f : BitString N → Bool} (h : Nonempty (Sigma3Rep N ε f)) :
    Sigma3CircuitSize ε f ≤ Sigma3 ε f := by
  obtain ⟨rep₀⟩ := h
  obtain ⟨rep, hrep⟩ : ∃ rep : Sigma3Rep N ε f, rep.t = Sigma3 ε f :=
    Nat.sInf_mem (s := {t | ∃ rep : Sigma3Rep N ε f, rep.t = t}) ⟨rep₀.t, rep₀, rfl⟩
  rw [← hrep]
  exact Sigma3CircuitSize_le_of_rep rep

/-! ## Circuit-flavored corollary of Lemma 11.1

`log Σ₃-circuit-size = O(N / log log N)` for `f ∈ NC¹_lin`. Follows
directly from `Valiant.log_sigma3_isBigO` plus `Sigma3CircuitSize_le_Sigma3`,
combined with the eventually-rep-exists lemma `sigma3Rep_exists_atTop`. -/

open Asymptotics Filter

/-- **Corollary of Lemma 11.1.** For `f ∈ NC¹_lin` and `ε > 0`,
`log Sigma3CircuitSize ε (f_N) = O(N / log log N)` as `N → ∞`. -/
theorem Valiant.log_sigma3_circuit_size_isBigO
    {f : BoolFunFamily} (hf : InNC1Lin f) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => Real.log ((Sigma3CircuitSize ε (f N) : ℕ) : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / Real.log (Real.log N)) := by
  have h_size_le : ∀ᶠ N : ℕ in atTop,
      Sigma3CircuitSize ε (f N) ≤ Sigma3 ε (f N) := by
    filter_upwards [sigma3Rep_exists_atTop hf hε, Filter.eventually_ge_atTop 1]
      with N ⟨rep⟩ hN1
    haveI : NeZero N := ⟨by omega⟩
    exact Sigma3CircuitSize_le_Sigma3 ⟨rep⟩
  have h_log_le : (fun N : ℕ => Real.log ((Sigma3CircuitSize ε (f N) : ℕ) : ℝ)) =O[atTop]
      (fun N : ℕ => Real.log ((Sigma3 ε (f N) : ℕ) : ℝ)) := by
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [h_size_le] with N hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg _),
        abs_of_nonneg (Real.log_natCast_nonneg _), one_mul]
    rcases (Sigma3CircuitSize ε (f N)).eq_zero_or_pos with hZ | hPos
    · rw [hZ, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (Nat.cast_pos.mpr hPos) (by exact_mod_cast hN)
  exact h_log_le.trans (Valiant.log_sigma3_isBigO hf hε)
