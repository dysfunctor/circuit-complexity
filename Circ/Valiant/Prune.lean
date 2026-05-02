import Circ.Valiant.CircuitDigraph
import Circ.Depth
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Finset

/-! # Pruning dead gates from a circuit

A gate of a circuit is *live* if its output wire eventually reaches some
output gate via the circuit's wiring. Dead internal chains are functionally
irrelevant (they do not affect `c.eval`) but artificially inflate the graph
depth used by Valiant's depth-reduction lemma. This file defines a
preprocessing step `Circuit.prune` that removes all dead gates while
preserving the computed function, the circuit's output depth, and the
number of gates (up to a ≤).

## Main definitions

* `Circuit.isLive` — inductive predicate: a vertex in `c.toDigraph` is
  live iff it is an output-gate vertex or has an edge to a live vertex.
* `Circuit.reachableGates` — the live internal gates, as a `Finset (Fin G)`.
* `Circuit.pruneEmb` / `Circuit.pruneIdx` — order-preserving bijection
  between the new gate indices `Fin c.reachableGates.card` and the live
  old indices. `pruneEmb ∘ pruneIdx = id` on live gates.
* `Circuit.translateInput` — rewrites a wire index from `Fin (N + G)` into
  `Fin (N + c.reachableGates.card)`, assuming the wire is live.
* `Circuit.prune` — the pruned circuit.

## Main results (this commit)

* `Circuit.prune` — the pruned circuit. Acyclicity is preserved because
  the order embedding `pruneEmb` is strictly monotone, so the
  re-indexed dependency order agrees with the original.
* `Circuit.prune_size_le` — `c.prune.size ≤ c.size`.
* `Circuit.prune_wireValue_eq` — wire-value preservation, by strong
  induction on the wire index. The gate case goes through a helper,
  `prune_gate_eval_eq_of_agree`, that equates the evaluation of the
  pruned gate at `i'` with the evaluation of the original gate at
  `c.pruneEmb i'` under pointwise wire-value agreement. Both sides
  reference the same `c.pruneEmb i'`, so no propositional substitution
  is required — this sidesteps the motive problems that arise when
  trying to rewrite `c.pruneEmb (c.pruneIdx j _) = j` through the
  pruned gate's dependently-typed fields.
* `Circuit.prune_eval_eq` — `c.prune.eval = c.eval`, by applying
  wire-value preservation at each output-gate input wire.
* `Circuit.wireDepth_input_lt` / `Circuit.wireDepth_output_input_lt` —
  gate/output inputs have strictly smaller `wireDepth`/`outputDepth`
  than the gate itself, via a `Fin.foldl`-max helper.
* `Circuit.wireDepth_lt_depth_of_isLive` — a live internal gate's
  `wireDepth` is strictly less than `c.depth` (induction on liveness).
* **`Circuit.prune_toDigraph_depth_le`** — the main consumer-facing
  bound: `c.prune.toDigraph.depth ≤ c.depth + 1`. This is what will be
  handed to `Valiant.depth_reduction` when formalizing Jukna's
  depth-reduction application in Lemma 11.1: the `G.depth ≤ 2 ^ k`
  hypothesis can be discharged with `k = ⌈log₂ (c.depth + 1)⌉`.

Deferred to later work:
* `Circuit.prune_depth_eq` (wireDepth / outputDepth / depth preservation
  under pruning).
-/

namespace Circuit

variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-! ### Liveness -/

/-- A vertex of `c.toDigraph` is **live** iff it is an output-gate vertex
or has a digraph edge to a live vertex. Equivalently: there is a directed
path from the vertex to some output gate. -/
inductive isLive (c : Circuit B N M G) : Fin (N + G + M) → Prop
  | output (j : Fin M) :
      isLive c ⟨N + G + j.val, by have := j.isLt; omega⟩
  | gate {u v : Fin (N + G + M)} (h : c.toDigraph.Adj u v) (hv : isLive c v) :
      isLive c u

/-- Classical decidability of liveness. `prune` is `noncomputable`
regardless, so there is no loss. -/
noncomputable instance (c : Circuit B N M G) (v : Fin (N + G + M)) :
    Decidable (c.isLive v) := Classical.propDecidable _

/-- If `u` has a digraph edge to a live vertex `v`, then `u` is live. -/
lemma isLive_of_adj (c : Circuit B N M G) {u v : Fin (N + G + M)}
    (h : c.toDigraph.Adj u v) (hv : c.isLive v) : c.isLive u :=
  isLive.gate h hv

/-- The vertex of any output gate is live. -/
lemma isLive_output (c : Circuit B N M G) (j : Fin M) :
    c.isLive ⟨N + G + j.val, by have := j.isLt; omega⟩ :=
  isLive.output j

/-- A live internal gate's input wires are live. -/
lemma isLive_input_of_gate (c : Circuit B N M G) {i : Fin G}
    (hi : c.isLive ⟨N + i.val, by have := i.isLt; omega⟩)
    (k : Fin (c.gates i).fanIn) :
    c.isLive ⟨((c.gates i).inputs k).val,
      by have := ((c.gates i).inputs k).isLt; omega⟩ := by
  apply isLive.gate (v := ⟨N + i.val, by have := i.isLt; omega⟩)
  · show c.toDigraphAdj _ _
    exact Or.inl ⟨i, rfl, k, rfl⟩
  · exact hi

/-- An output gate's input wires are live. -/
lemma isLive_input_of_output (c : Circuit B N M G) (j : Fin M)
    (k : Fin (c.outputs j).fanIn) :
    c.isLive ⟨((c.outputs j).inputs k).val,
      by have := ((c.outputs j).inputs k).isLt; omega⟩ := by
  apply isLive.gate (v := ⟨N + G + j.val, by have := j.isLt; omega⟩)
  · show c.toDigraphAdj _ _
    exact Or.inr ⟨j, rfl, k, rfl⟩
  · exact isLive.output j

/-- **Depth bound via liveness.** For any live vertex that falls in the
internal-gate range, `c.wireDepth` is strictly less than `c.depth`. The
proof is by induction on the liveness derivation: the `output`
constructor contradicts the range hypothesis, and the `gate` constructor
supplies an edge whose target already satisfies the bound, which
propagates backward via `wireDepth_input_lt` / `wireDepth_output_input_lt`. -/
private lemma wireDepth_lt_depth_of_isLive (c : Circuit B N M G) :
    ∀ {v : Fin (N + G + M)}, c.isLive v →
      ∀ (hlt : v.val < N + G),
        c.wireDepth ⟨v.val, hlt⟩ < c.depth := by
  intro v hv
  induction hv with
  | output j =>
    intro hlt
    exfalso
    -- v = ⟨N + G + j.val, _⟩; hlt says its val is < N + G, impossible.
    show False
    have : (⟨N + G + j.val, by have := j.isLt; omega⟩ : Fin (N + G + M)).val < N + G := hlt
    simp only at this
    omega
  | @gate u v huv hv_live ih =>
    intro hlt_u
    -- Unfold the `Adj u v` into one of the two digraph cases.
    have h_adj : c.toDigraphAdj u v := huv
    rcases h_adj with ⟨i, hv_eq, k, hk⟩ | ⟨j, hv_eq, k, hk⟩
    · -- v is internal gate `i`: `(c.gates i).inputs k` has `.val = u.val`.
      have hv_hlt : v.val < N + G := by rw [hv_eq]; have := i.isLt; omega
      have ih_v := ih hv_hlt
      have h_input_lt := c.wireDepth_input_lt i k
      have h_input_eq :
          c.wireDepth ((c.gates i).inputs k) = c.wireDepth ⟨u.val, hlt_u⟩ := by
        congr 1; exact Fin.ext hk
      have h_gate_eq :
          c.wireDepth ⟨N + i.val, by have := i.isLt; omega⟩ =
            c.wireDepth ⟨v.val, hv_hlt⟩ := by
        congr 1; exact Fin.ext hv_eq.symm
      rw [h_input_eq, h_gate_eq] at h_input_lt
      omega
    · -- v is output gate `j`: `(c.outputs j).inputs k` has `.val = u.val`.
      have h_input_lt := c.wireDepth_output_input_lt j k
      have h_input_eq :
          c.wireDepth ((c.outputs j).inputs k) = c.wireDepth ⟨u.val, hlt_u⟩ := by
        congr 1; exact Fin.ext hk
      rw [h_input_eq] at h_input_lt
      have := c.outputDepth_le_depth j
      omega

/-! ### Reachable gates -/

/-- The set of internal gate indices whose output wire is live. -/
noncomputable def reachableGates (c : Circuit B N M G) : Finset (Fin G) :=
  Finset.univ.filter
    (fun i => c.isLive ⟨N + i.val, by have := i.isLt; omega⟩)

lemma mem_reachableGates_iff (c : Circuit B N M G) (i : Fin G) :
    i ∈ c.reachableGates ↔
      c.isLive ⟨N + i.val, by have := i.isLt; omega⟩ := by
  simp [reachableGates]

/-- If a live wire references an internal gate (rather than a primary
input), that gate is reachable. -/
lemma mem_reachableGates_of_isLive (c : Circuit B N M G)
    {v : Fin (N + G + M)} (hv : c.isLive v) (hge : N ≤ v.val) (hlt : v.val < N + G) :
    (⟨v.val - N, by omega⟩ : Fin G) ∈ c.reachableGates := by
  rw [mem_reachableGates_iff]
  have heq : N + (v.val - N) = v.val := by omega
  rw [show (⟨N + (v.val - N), by omega⟩ : Fin (N + G + M)) = v from
    Fin.ext (by simpa using heq)]
  exact hv

/-! ### Re-indexing -/

/-- Order-preserving embedding of pruned gate indices back into the
original gate indices. Determined uniquely by the sorted enumeration of
live gates. -/
noncomputable def pruneEmb (c : Circuit B N M G) :
    Fin c.reachableGates.card ↪o Fin G :=
  c.reachableGates.orderEmbOfFin rfl

/-- Pruned gate indices correspond to live old gates. -/
lemma pruneEmb_mem_reachableGates (c : Circuit B N M G)
    (i' : Fin c.reachableGates.card) : c.pruneEmb i' ∈ c.reachableGates :=
  Finset.orderEmbOfFin_mem _ _ _

/-- Inverse of `pruneEmb`: map a live old gate to its index in the
sorted enumeration. -/
noncomputable def pruneIdx (c : Circuit B N M G) (i : Fin G)
    (h : i ∈ c.reachableGates) : Fin c.reachableGates.card :=
  (c.reachableGates.orderIsoOfFin rfl).symm ⟨i, h⟩

lemma pruneEmb_pruneIdx (c : Circuit B N M G) (i : Fin G)
    (h : i ∈ c.reachableGates) : c.pruneEmb (c.pruneIdx i h) = i := by
  show (c.reachableGates.orderEmbOfFin rfl) _ = i
  rw [← Finset.coe_orderIsoOfFin_apply]
  show ((c.reachableGates.orderIsoOfFin rfl)
      ((c.reachableGates.orderIsoOfFin rfl).symm ⟨i, h⟩) : Fin G) = i
  rw [OrderIso.apply_symm_apply]

lemma pruneIdx_pruneEmb (c : Circuit B N M G)
    (i' : Fin c.reachableGates.card) :
    c.pruneIdx (c.pruneEmb i') (c.pruneEmb_mem_reachableGates i') = i' := by
  show (c.reachableGates.orderIsoOfFin rfl).symm _ = i'
  have : (⟨c.pruneEmb i', c.pruneEmb_mem_reachableGates i'⟩ : c.reachableGates) =
      c.reachableGates.orderIsoOfFin rfl i' := by
    apply Subtype.ext
    rw [Finset.coe_orderIsoOfFin_apply]
    rfl
  rw [this, OrderIso.symm_apply_apply]

/-- `pruneEmb` is strictly monotone (it is an order embedding). -/
lemma pruneEmb_lt_iff (c : Circuit B N M G) (i' j' : Fin c.reachableGates.card) :
    c.pruneEmb i' < c.pruneEmb j' ↔ i' < j' :=
  (c.pruneEmb).lt_iff_lt

/-- Strictly monotone correspondence between live old-index order and
new-index order: `pruneIdx` is strictly monotone. -/
lemma pruneIdx_lt_of_lt (c : Circuit B N M G) {i j : Fin G}
    (hi : i ∈ c.reachableGates) (hj : j ∈ c.reachableGates) (h : i < j) :
    c.pruneIdx i hi < c.pruneIdx j hj := by
  rw [← c.pruneEmb_lt_iff]
  rw [c.pruneEmb_pruneIdx, c.pruneEmb_pruneIdx]
  exact h

/-! ### Translating wire references -/

/-- Rewrite a wire reference from the original circuit into the pruned
circuit, assuming the wire is live. Primary inputs keep their index; a
reference to a live gate `i` is remapped to the new index `pruneIdx i`. -/
noncomputable def translateInput (c : Circuit B N M G) (w : Fin (N + G))
    (hw : c.isLive ⟨w.val, by have := w.isLt; omega⟩) :
    Fin (N + c.reachableGates.card) :=
  if h : w.val < N then
    ⟨w.val, by omega⟩
  else
    let j : Fin G := ⟨w.val - N, by have := w.isLt; omega⟩
    have hN_le : N ≤ w.val := Nat.le_of_not_lt h
    have hG_lt : w.val < N + G := w.isLt
    have hj : j ∈ c.reachableGates :=
      c.mem_reachableGates_of_isLive hw hN_le hG_lt
    ⟨N + (c.pruneIdx j hj).val, by
      have := (c.pruneIdx j hj).isLt; omega⟩

/-- Primary-input case of `translateInput`. -/
lemma translateInput_of_lt (c : Circuit B N M G) (w : Fin (N + G))
    (hw : c.isLive ⟨w.val, by have := w.isLt; omega⟩) (h : w.val < N) :
    (c.translateInput w hw).val = w.val := by
  unfold translateInput
  rw [dif_pos h]

/-- Gate-output case of `translateInput`. -/
lemma translateInput_of_ge (c : Circuit B N M G) (w : Fin (N + G))
    (hw : c.isLive ⟨w.val, by have := w.isLt; omega⟩) (h : ¬ w.val < N) :
    (c.translateInput w hw).val = N +
      (c.pruneIdx ⟨w.val - N, by have := w.isLt; omega⟩
        (c.mem_reachableGates_of_isLive hw (Nat.le_of_not_lt h) w.isLt)).val := by
  unfold translateInput
  rw [dif_neg h]

/-! ### The pruned circuit -/

/-- The pruned circuit: same primary inputs and outputs, but internal
gates reduced to the live ones, re-indexed in sorted order. -/
noncomputable def prune (c : Circuit B N M G) :
    Circuit B N M c.reachableGates.card where
  gates i' :=
    let oldI : Fin G := c.pruneEmb i'
    let oldGate := c.gates oldI
    have hlive_oldI : c.isLive ⟨N + oldI.val, by have := oldI.isLt; omega⟩ :=
      (c.mem_reachableGates_iff oldI).mp (c.pruneEmb_mem_reachableGates i')
    { op := oldGate.op
      fanIn := oldGate.fanIn
      arityOk := oldGate.arityOk
      inputs := fun k => c.translateInput (oldGate.inputs k)
        (c.isLive_input_of_gate hlive_oldI k)
      negated := oldGate.negated }
  outputs j :=
    let oldOutput := c.outputs j
    { op := oldOutput.op
      fanIn := oldOutput.fanIn
      arityOk := oldOutput.arityOk
      inputs := fun k => c.translateInput (oldOutput.inputs k)
        (c.isLive_input_of_output j k)
      negated := oldOutput.negated }
  acyclic := by
    intro i' k
    let oldI : Fin G := c.pruneEmb i'
    let oldInput : Fin (N + G) := (c.gates oldI).inputs k
    have hoi_val : oldInput.val < N + G := oldInput.isLt
    have hoi_bnd : oldInput.val < N + G + M := by omega
    have holdI_live : c.isLive ⟨N + oldI.val, by have := oldI.isLt; omega⟩ :=
      (c.mem_reachableGates_iff oldI).mp (c.pruneEmb_mem_reachableGates i')
    have hlive_input : c.isLive ⟨oldInput.val, hoi_bnd⟩ :=
      c.isLive_input_of_gate holdI_live k
    show (c.translateInput oldInput hlive_input).val < N + i'.val
    by_cases hlt : oldInput.val < N
    · rw [c.translateInput_of_lt oldInput hlive_input hlt]
      omega
    · rw [c.translateInput_of_ge oldInput hlive_input hlt]
      have hN_le : N ≤ oldInput.val := Nat.le_of_not_lt hlt
      have hbnd : oldInput.val - N < G := by omega
      have hacyc : oldInput.val < N + oldI.val := c.acyclic oldI k
      have hmem : (⟨oldInput.val - N, hbnd⟩ : Fin G) ∈ c.reachableGates :=
        c.mem_reachableGates_of_isLive hlive_input hN_le hoi_val
      have hjFin_lt_oldI : (⟨oldInput.val - N, hbnd⟩ : Fin G) < oldI := by
        rw [Fin.lt_def]; show oldInput.val - N < oldI.val; omega
      have hpLt := c.pruneIdx_lt_of_lt hmem
        (c.pruneEmb_mem_reachableGates i') hjFin_lt_oldI
      rw [c.pruneIdx_pruneEmb] at hpLt
      have hpv : (c.pruneIdx ⟨oldInput.val - N, hbnd⟩ hmem).val < i'.val :=
        Fin.lt_def.mp hpLt
      -- After translateInput_of_ge rewrite, the goal uses pruneIdx with specific
      -- proofs. Proof irrelevance lets us identify with our hmem version.
      show N + (c.pruneIdx ⟨oldInput.val - N, hbnd⟩ hmem).val < N + i'.val
      omega

/-! ### Size bound -/

theorem prune_size_le (c : Circuit B N M G) : c.prune.size ≤ c.size := by
  show c.reachableGates.card + M ≤ G + M
  have : c.reachableGates.card ≤ G := by
    have := Finset.card_le_univ c.reachableGates
    simpa using this
  omega

/-! ### Evaluation preservation -/

/-- Helper: evaluating the pruned gate at new index `i'` with some
`wv_new` equals evaluating the original gate at the *corresponding* old
index `c.pruneEmb i'` with some `wv_old`, provided the two wire-value
functions agree on the gate's inputs (after translation). Crucially,
the equation refers to `c.pruneEmb i'` on both sides — there is no
substitution of that expression, which sidesteps the motive problems
that arise from `c.pruneEmb_pruneIdx` being only a propositional
equality. -/
private lemma prune_gate_eval_eq_of_agree
    (c : Circuit B N M G) (i' : Fin c.reachableGates.card)
    (wv_new : BitString (N + c.reachableGates.card))
    (wv_old : BitString (N + G))
    (h_agree : ∀ k : Fin (c.gates (c.pruneEmb i')).fanIn,
      wv_new (c.translateInput ((c.gates (c.pruneEmb i')).inputs k)
        (c.isLive_input_of_gate
          ((c.mem_reachableGates_iff (c.pruneEmb i')).mp
            (c.pruneEmb_mem_reachableGates i')) k)) =
      wv_old ((c.gates (c.pruneEmb i')).inputs k)) :
    (c.prune.gates i').eval wv_new =
      (c.gates (c.pruneEmb i')).eval wv_old := by
  show B.eval _ _ _ _ = B.eval _ _ _ _
  congr 1
  funext k
  -- After `funext`, the goal is the per-`k` scalar equation. Normalize
  -- `(c.prune.gates i').negated` and `(c.prune.gates i').inputs k` via
  -- `change` using the definitional structure of `c.prune.gates`, then
  -- apply `h_agree`.
  change
    ((c.gates (c.pruneEmb i')).negated k ^^
      wv_new (c.translateInput ((c.gates (c.pruneEmb i')).inputs k)
        (c.isLive_input_of_gate
          ((c.mem_reachableGates_iff (c.pruneEmb i')).mp
            (c.pruneEmb_mem_reachableGates i')) k))) =
    ((c.gates (c.pruneEmb i')).negated k ^^
      wv_old ((c.gates (c.pruneEmb i')).inputs k))
  rw [h_agree k]

/-- Key wire-value preservation lemma. For any wire `w` of the original
circuit that is live, the pruned circuit assigns the same value to its
translated wire. Proved by strong induction on `w.val`, mirroring the
structure of `wireValue`. -/
theorem prune_wireValue_eq (c : Circuit B N M G) (input : BitString N) :
    ∀ (n : ℕ) (w : Fin (N + G)) (hw_val : w.val = n)
      (hw_live : c.isLive ⟨w.val, by have := w.isLt; omega⟩),
      c.prune.wireValue input (c.translateInput w hw_live) =
        c.wireValue input w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw_val hw_live
    by_cases hlt : w.val < N
    · -- Primary input case.
      have htr := c.translateInput_of_lt w hw_live hlt
      have hlt' : (c.translateInput w hw_live).val < N := by
        rw [htr]; exact hlt
      rw [c.wireValue_lt input w hlt]
      rw [c.prune.wireValue_lt input _ hlt']
      congr 1
      apply Fin.ext
      exact htr
    · -- Gate case.
      rw [c.wireValue_ge input w hlt]
      have htr := c.translateInput_of_ge w hw_live hlt
      have hge' : ¬ (c.translateInput w hw_live).val < N := by
        rw [htr]; omega
      rw [c.prune.wireValue_ge input _ hge']
      have hN_le : N ≤ w.val := Nat.le_of_not_lt hlt
      have hjbnd : w.val - N < G := by omega
      have hj_mem : (⟨w.val - N, hjbnd⟩ : Fin G) ∈ c.reachableGates :=
        c.mem_reachableGates_of_isLive hw_live hN_le w.isLt
      set iPrune : Fin c.reachableGates.card :=
        ⟨(c.translateInput w hw_live).val - N, by
          have := (c.translateInput w hw_live).isLt; omega⟩ with hiPrune_def
      have hi1_eq : iPrune = c.pruneIdx ⟨w.val - N, hjbnd⟩ hj_mem := by
        apply Fin.ext
        show (c.translateInput w hw_live).val - N
            = (c.pruneIdx ⟨w.val - N, hjbnd⟩ hj_mem).val
        rw [htr]; omega
      have hpemb : c.pruneEmb iPrune = ⟨w.val - N, hjbnd⟩ := by
        rw [hi1_eq]; exact c.pruneEmb_pruneIdx _ hj_mem
      -- Show the inputs agree (via the induction hypothesis applied to
      -- each input wire, which has `.val < n` by acyclicity).
      have h_agree : ∀ k : Fin (c.gates (c.pruneEmb iPrune)).fanIn,
          c.prune.wireValue input
            (c.translateInput ((c.gates (c.pruneEmb iPrune)).inputs k)
              (c.isLive_input_of_gate
                ((c.mem_reachableGates_iff _).mp
                  (c.pruneEmb_mem_reachableGates iPrune)) k)) =
          c.wireValue input ((c.gates (c.pruneEmb iPrune)).inputs k) := by
        intro k
        have hacyc : ((c.gates (c.pruneEmb iPrune)).inputs k).val
            < N + (c.pruneEmb iPrune).val :=
          c.acyclic (c.pruneEmb iPrune) k
        have hpemb_val : (c.pruneEmb iPrune).val = w.val - N := by
          rw [hpemb]
        have hinp_lt_n : ((c.gates (c.pruneEmb iPrune)).inputs k).val < n := by
          rw [hpemb_val] at hacyc; omega
        exact ih _ hinp_lt_n _ rfl
          (c.isLive_input_of_gate
            ((c.mem_reachableGates_iff _).mp
              (c.pruneEmb_mem_reachableGates iPrune)) k)
      have hhelper :=
        c.prune_gate_eval_eq_of_agree iPrune (c.prune.wireValue input)
          (c.wireValue input) h_agree
      -- After `rw`s, LHS of the goal is literally
      -- `(c.prune.gates iPrune).eval (c.prune.wireValue input)` (by `set`),
      -- so hhelper rewrites it to `(c.gates (c.pruneEmb iPrune)).eval …`.
      rw [hhelper]
      -- Remaining: `(c.gates (c.pruneEmb iPrune)).eval _ = (c.gates ⟨w.val - N, _⟩).eval _`.
      -- By `hpemb`, the two `Fin G` arguments to `c.gates` have the same `.val`;
      -- they differ only in their `isLt` proofs, which are proof-irrelevant.
      congr 2

/-- **Evaluation preservation.** The pruned circuit computes the same
function as the original. Output gates are wired the same way (modulo
input translation), and their input wires are live by
`isLive_input_of_output`; applying `prune_wireValue_eq` at each input
wire closes the outer comparison. -/
theorem prune_eval_eq (c : Circuit B N M G) : c.prune.eval = c.eval := by
  funext input j
  show (c.prune.outputs j).eval (c.prune.wireValue input) =
       (c.outputs j).eval (c.wireValue input)
  -- Expand `Gate.eval` on both sides. `c.prune.outputs j` shares op /
  -- fanIn / arityOk / negated with `c.outputs j`; the only difference is
  -- that its input-wire indices are `translateInput`-translated.
  show B.eval _ _ _ _ = B.eval _ _ _ _
  congr 1
  funext k
  change
    ((c.outputs j).negated k ^^
      c.prune.wireValue input
        (c.translateInput ((c.outputs j).inputs k)
          (c.isLive_input_of_output j k))) =
    ((c.outputs j).negated k ^^
      c.wireValue input ((c.outputs j).inputs k))
  rw [c.prune_wireValue_eq input ((c.outputs j).inputs k).val
      ((c.outputs j).inputs k) rfl (c.isLive_input_of_output j k)]

/-! ### Cleanness and the graph-depth bound for the pruned circuit

A circuit is *clean* when every internal-gate vertex of its `toDigraph`
is live — i.e., no dead chains of gates. Pruning is the canonical way
to produce one.

The main theorem below, `prune_toDigraph_depth_le`, bounds the graph
depth of the pruned circuit by the original circuit's `depth + 1` —
exactly the input `Valiant.depth_reduction` needs. Proof: label each
vertex of `c.prune.toDigraph` by a natural number (`pruneLabel`) so
that every edge strictly increases the label and every label lies in
`[0, c.depth]`. Then `|image pruneLabel| ≤ c.depth + 1` and
`depth_le_image_card` closes the argument.

The labeling refers back to the *original* circuit `c` — an internal
pruned gate `i'` is labeled by `c.wireDepth` of `c.pruneEmb i'`. This
sidesteps needing to prove wireDepth preservation under pruning:
`c.pruneEmb i'` is live in `c`, so `wireDepth_lt_depth_of_isLive`
supplies the image bound directly.
-/

/-- Label each vertex of `c.prune.toDigraph` by:
* `0` for primary inputs,
* `c.wireDepth` of the *original* gate at `c.pruneEmb i'` for internal
  pruned gates `i'`,
* `c.outputDepth j` for output gate `j`. -/
noncomputable def pruneLabel (c : Circuit B N M G)
    (v : Fin (N + c.reachableGates.card + M)) : ℕ :=
  if _ : v.val < N then 0
  else if h2 : v.val < N + c.reachableGates.card then
    c.wireDepth ⟨N + (c.pruneEmb ⟨v.val - N, by omega⟩).val, by
      have := (c.pruneEmb ⟨v.val - N, by omega⟩).isLt; omega⟩
  else
    c.outputDepth ⟨v.val - (N + c.reachableGates.card), by
      have := v.isLt; omega⟩

lemma pruneLabel_of_input (c : Circuit B N M G)
    {v : Fin (N + c.reachableGates.card + M)} (h : v.val < N) :
    c.pruneLabel v = 0 := by
  unfold pruneLabel; rw [dif_pos h]

lemma pruneLabel_of_gate (c : Circuit B N M G)
    {v : Fin (N + c.reachableGates.card + M)}
    (h1 : ¬ v.val < N) (h2 : v.val < N + c.reachableGates.card) :
    c.pruneLabel v =
      c.wireDepth ⟨N + (c.pruneEmb ⟨v.val - N, by omega⟩).val, by
        have := (c.pruneEmb ⟨v.val - N, by omega⟩).isLt; omega⟩ := by
  unfold pruneLabel; rw [dif_neg h1, dif_pos h2]

lemma pruneLabel_of_output (c : Circuit B N M G)
    {v : Fin (N + c.reachableGates.card + M)}
    (h1 : ¬ v.val < N) (h2 : ¬ v.val < N + c.reachableGates.card) :
    c.pruneLabel v =
      c.outputDepth ⟨v.val - (N + c.reachableGates.card), by
        have := v.isLt; omega⟩ := by
  unfold pruneLabel; rw [dif_neg h1, dif_neg h2]

/-- `c.wireDepth ⟨w, h⟩` depends only on the value `w`, not on the
specific `Fin` bound proof (proof irrelevance at the `Fin.mk` level). -/
private lemma wireDepth_eq_of_val_eq (c : Circuit B N M G) {w1 w2 : Fin (N + G)}
    (h : w1.val = w2.val) : c.wireDepth w1 = c.wireDepth w2 := by
  congr 1
  exact Fin.ext h

/-- **Legality of `pruneLabel`.** Along every edge of `c.prune.toDigraph`,
the label strictly increases. Proved by unfolding the adjacency into
the "edge-into-gate" or "edge-into-output" case and, in each, subcasing
on whether the source is a primary input or a gate wire. Strictness
follows either from `c.wireDepth` of an internal gate being `≥ 1`
(edges from primary inputs) or from `wireDepth_input_lt` /
`wireDepth_output_input_lt` (edges from internal pruned gates). -/
lemma pruneLabel_isLegal (c : Circuit B N M G) :
    Valiant.IsLegalLabeling c.prune.toDigraph c.pruneLabel := by
  intro u v h_adj
  have h_adj' : c.prune.toDigraphAdj u v := h_adj
  -- `u.val < N + c.reachableGates.card` always: a wire that is an input
  -- of some gate must be a primary input or an internal pruned-gate
  -- wire, never an output-gate vertex.
  have hu_lt : u.val < N + c.reachableGates.card := by
    rcases h_adj' with ⟨_, _, k, hk⟩ | ⟨_, _, k, hk⟩
    · rw [← hk]; exact ((c.prune.gates _).inputs k).isLt
    · rw [← hk]; exact ((c.prune.outputs _).inputs k).isLt
  have hu_lt' : u.val < N + c.reachableGates.card + M := by
    have := u.isLt; exact this
  rcases h_adj' with ⟨i', hv_eq, k, hk⟩ | ⟨j, hv_eq, k, hk⟩
  · -- Edge into an internal pruned gate `i'`.
    have hv_nilt : ¬ v.val < N := by rw [hv_eq]; omega
    have hv_lt : v.val < N + c.reachableGates.card := by
      rw [hv_eq]; have := i'.isLt; omega
    rw [c.pruneLabel_of_gate hv_nilt hv_lt]
    -- Replace `⟨v.val - N, _⟩` with `i'` inside `c.pruneEmb` to match the
    -- ambient `i'` (same `.val`, different `isLt` proof, defeq via
    -- `Fin.ext` + proof irrelevance). We transport the entire `wireDepth`
    -- expression in one go to avoid motive issues.
    have hfin_eq : (⟨v.val - N, by omega⟩ : Fin c.reachableGates.card) = i' := by
      apply Fin.ext; show v.val - N = i'.val; rw [hv_eq]; omega
    rw [show c.wireDepth ⟨N + (c.pruneEmb ⟨v.val - N, by omega⟩).val, by
              have := (c.pruneEmb ⟨v.val - N, by omega⟩).isLt; omega⟩ =
            c.wireDepth ⟨N + (c.pruneEmb i').val, by
              have := (c.pruneEmb i').isLt; omega⟩ from by
          apply c.wireDepth_eq_of_val_eq
          show N + (c.pruneEmb ⟨v.val - N, by omega⟩).val =
            N + (c.pruneEmb i').val
          rw [hfin_eq]]
    -- Unfold the pruned gate's `k`-th input: it's
    -- `c.translateInput ((c.gates (c.pruneEmb i')).inputs k) _`.
    set wOld : Fin (N + G) := (c.gates (c.pruneEmb i')).inputs k with hwOld_def
    have hu_val :
        u.val = (c.translateInput wOld
          (c.isLive_input_of_gate
            ((c.mem_reachableGates_iff _).mp
              (c.pruneEmb_mem_reachableGates i')) k)).val := by
      show u.val = (c.translateInput ((c.gates (c.pruneEmb i')).inputs k) _).val
      rw [← hk]; rfl
    by_cases hw_input : wOld.val < N
    · -- Primary-input case: `u.val = wOld.val < N`.
      have hu_primary : u.val < N := by
        rw [hu_val, c.translateInput_of_lt wOld _ hw_input]
        exact hw_input
      rw [c.pruneLabel_of_input hu_primary]
      -- `c.wireDepth ⟨N + (c.pruneEmb i').val, _⟩ ≥ 1 > 0`.
      have h_ge1 :
          1 ≤ c.wireDepth ⟨N + (c.pruneEmb i').val, by
              have := (c.pruneEmb i').isLt; omega⟩ := by
        have hne : ¬ (⟨N + (c.pruneEmb i').val, by
            have := (c.pruneEmb i').isLt; omega⟩ : Fin (N + G)).val < N := by
          show ¬ N + (c.pruneEmb i').val < N; omega
        rw [c.gateWireDepth _ hne]
        omega
      omega
    · -- Gate case: `wOld.val ≥ N`, so the translation goes through `pruneIdx`.
      have hw_N_le : N ≤ wOld.val := Nat.le_of_not_lt hw_input
      have hw_lt : wOld.val < N + G := wOld.isLt
      have hjOld_bnd : wOld.val - N < G := by omega
      set jOld : Fin G := ⟨wOld.val - N, hjOld_bnd⟩ with hjOld_def
      -- `jOld` is reachable: it's the back-end of an input of a live gate.
      have hjOld_live :
          c.isLive ⟨wOld.val, by have := wOld.isLt; omega⟩ := by
        have h_i'_live : c.isLive ⟨N + (c.pruneEmb i').val, by
            have := (c.pruneEmb i').isLt; omega⟩ :=
          (c.mem_reachableGates_iff _).mp (c.pruneEmb_mem_reachableGates i')
        exact c.isLive_input_of_gate h_i'_live k
      have hjOld_mem : jOld ∈ c.reachableGates :=
        c.mem_reachableGates_of_isLive hjOld_live hw_N_le hw_lt
      have hu_gate_val :
          u.val = N + (c.pruneIdx jOld hjOld_mem).val := by
        rw [hu_val, c.translateInput_of_ge wOld _ (not_lt.mpr hw_N_le)]
      have hu_nilt : ¬ u.val < N := by
        rw [hu_gate_val]; omega
      have hu_rbnd : u.val < N + c.reachableGates.card := by
        rw [hu_gate_val]
        have := (c.pruneIdx jOld hjOld_mem).isLt; omega
      rw [c.pruneLabel_of_gate hu_nilt hu_rbnd]
      -- Transport the pruneLabel side to `c.wireDepth wOld` in one step.
      -- `⟨u.val - N, _⟩ = c.pruneIdx jOld hjOld_mem`, composed with
      -- `c.pruneEmb_pruneIdx`, gives `c.pruneEmb ⟨u.val - N, _⟩ = jOld`,
      -- so the LHS of the goal has `.val` equal to `N + jOld.val = wOld.val`.
      rw [show c.wireDepth ⟨N + (c.pruneEmb ⟨u.val - N, by omega⟩).val, by
                have := (c.pruneEmb ⟨u.val - N, by omega⟩).isLt; omega⟩ =
              c.wireDepth wOld from by
            apply c.wireDepth_eq_of_val_eq
            have h_pemb_eq : c.pruneEmb ⟨u.val - N, by omega⟩ = jOld := by
              have h_idx : (⟨u.val - N, by omega⟩ : Fin c.reachableGates.card)
                  = c.pruneIdx jOld hjOld_mem := by
                apply Fin.ext
                show u.val - N = (c.pruneIdx jOld hjOld_mem).val
                rw [hu_gate_val]; omega
              rw [h_idx, c.pruneEmb_pruneIdx]
            show N + (c.pruneEmb ⟨u.val - N, by omega⟩).val = wOld.val
            rw [h_pemb_eq]
            show N + jOld.val = wOld.val
            show N + (wOld.val - N) = wOld.val
            omega]
      exact c.wireDepth_input_lt (c.pruneEmb i') k
  · -- Edge into output gate `j`.
    have hv_nilt : ¬ v.val < N := by rw [hv_eq]; omega
    have hv_nilt2 : ¬ v.val < N + c.reachableGates.card := by rw [hv_eq]; omega
    rw [c.pruneLabel_of_output hv_nilt hv_nilt2]
    -- `v.val - (N + c.reachableGates.card) = j.val`, so the output index matches `j`.
    have hj_eq : (⟨v.val - (N + c.reachableGates.card), by
        have := v.isLt; omega⟩ : Fin M) = j := by
      apply Fin.ext
      show v.val - (N + c.reachableGates.card) = j.val
      rw [hv_eq]; omega
    rw [hj_eq]
    -- Unfold the pruned output's `k`-th input.
    set wOld : Fin (N + G) := (c.outputs j).inputs k with hwOld_def
    have hu_val :
        u.val = (c.translateInput wOld
          (c.isLive_input_of_output j k)).val := by
      show u.val = (c.translateInput ((c.outputs j).inputs k) _).val
      rw [← hk]; rfl
    by_cases hw_input : wOld.val < N
    · -- Primary-input source.
      have hu_primary : u.val < N := by
        rw [hu_val, c.translateInput_of_lt wOld _ hw_input]
        exact hw_input
      rw [c.pruneLabel_of_input hu_primary]
      -- `c.outputDepth j ≥ 1`.
      show 0 < c.outputDepth j
      show 0 < 1 + _
      omega
    · -- Gate source.
      have hw_N_le : N ≤ wOld.val := Nat.le_of_not_lt hw_input
      have hw_lt : wOld.val < N + G := wOld.isLt
      have hjOld_bnd : wOld.val - N < G := by omega
      set jOld : Fin G := ⟨wOld.val - N, hjOld_bnd⟩ with hjOld_def
      have hjOld_live :
          c.isLive ⟨wOld.val, by have := wOld.isLt; omega⟩ :=
        c.isLive_input_of_output j k
      have hjOld_mem : jOld ∈ c.reachableGates :=
        c.mem_reachableGates_of_isLive hjOld_live hw_N_le hw_lt
      have hu_gate_val :
          u.val = N + (c.pruneIdx jOld hjOld_mem).val := by
        rw [hu_val, c.translateInput_of_ge wOld _ (not_lt.mpr hw_N_le)]
      have hu_nilt : ¬ u.val < N := by rw [hu_gate_val]; omega
      have hu_rbnd : u.val < N + c.reachableGates.card := by
        rw [hu_gate_val]
        have := (c.pruneIdx jOld hjOld_mem).isLt; omega
      rw [c.pruneLabel_of_gate hu_nilt hu_rbnd]
      -- Transport to `c.wireDepth wOld` via the same trick as the
      -- internal-gate case.
      rw [show c.wireDepth ⟨N + (c.pruneEmb ⟨u.val - N, by omega⟩).val, by
                have := (c.pruneEmb ⟨u.val - N, by omega⟩).isLt; omega⟩ =
              c.wireDepth wOld from by
            apply c.wireDepth_eq_of_val_eq
            have h_pemb_eq : c.pruneEmb ⟨u.val - N, by omega⟩ = jOld := by
              have h_idx : (⟨u.val - N, by omega⟩ : Fin c.reachableGates.card)
                  = c.pruneIdx jOld hjOld_mem := by
                apply Fin.ext
                show u.val - N = (c.pruneIdx jOld hjOld_mem).val
                rw [hu_gate_val]; omega
              rw [h_idx, c.pruneEmb_pruneIdx]
            show N + (c.pruneEmb ⟨u.val - N, by omega⟩).val = wOld.val
            rw [h_pemb_eq]
            show N + jOld.val = wOld.val
            show N + (wOld.val - N) = wOld.val
            omega]
      exact c.wireDepth_output_input_lt j k

/-- Every `pruneLabel` value lies in `[0, c.depth]`. -/
lemma pruneLabel_le_depth (c : Circuit B N M G)
    (v : Fin (N + c.reachableGates.card + M)) :
    c.pruneLabel v ≤ c.depth := by
  unfold pruneLabel
  split_ifs with h1 h2
  · exact Nat.zero_le _
  · -- Internal gate: use `wireDepth_lt_depth_of_isLive`.
    have hi_bnd : v.val - N < c.reachableGates.card := by omega
    have h_live : c.isLive ⟨N + (c.pruneEmb ⟨v.val - N, hi_bnd⟩).val, by
        have := (c.pruneEmb ⟨v.val - N, hi_bnd⟩).isLt; omega⟩ :=
      (c.mem_reachableGates_iff _).mp
        (c.pruneEmb_mem_reachableGates ⟨v.val - N, hi_bnd⟩)
    have hbnd' : N + (c.pruneEmb ⟨v.val - N, hi_bnd⟩).val < N + G := by
      have := (c.pruneEmb ⟨v.val - N, hi_bnd⟩).isLt
      omega
    have := c.wireDepth_lt_depth_of_isLive h_live hbnd'
    exact le_of_lt this
  · -- Output: use `outputDepth_le_depth`.
    exact c.outputDepth_le_depth _

/-- **Graph-depth bound for the pruned circuit.** The pruned digraph
`c.prune.toDigraph` has depth at most `c.depth + 1`, so Valiant's
depth-reduction lemma can be applied with `2^k` as small as
`c.depth + 1`. -/
theorem prune_toDigraph_depth_le (c : Circuit B N M G) :
    c.prune.toDigraph.depth ≤ c.depth + 1 := by
  have hlegal := c.pruneLabel_isLegal
  have hbnd := Valiant.depth_le_image_card c.prune.toDigraph hlegal
  -- The image of `pruneLabel` over all vertices is a subset of
  -- `Finset.range (c.depth + 1)` (values `0, 1, …, c.depth`).
  refine hbnd.trans ?_
  calc (Finset.image c.pruneLabel Finset.univ).card
      ≤ (Finset.range (c.depth + 1)).card := by
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_image] at hn
        obtain ⟨v, _, hv⟩ := hn
        rw [Finset.mem_range]
        have := c.pruneLabel_le_depth v
        omega
    _ = c.depth + 1 := Finset.card_range _

end Circuit
