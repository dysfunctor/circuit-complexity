import Circ.Basic
import Circ.Valiant.CircuitDigraph
import Mathlib.Data.Finset.Basic

/-! # Cut circuit evaluation

Given a circuit `c` and a set `F` of "cut" edges in `c.toDigraph`,
`Circuit.cutValue c F α x w` evaluates wire `w` as if each cut wire
were a fresh variable taking the value supplied by `α`, with primary
inputs taking values from `x`.

This is the basic machinery behind Jukna's Lemma 11.1's Σ₃
construction (step 4 of the outline): after `depth_reduction` returns
a set `F` of edges to cut, the circuit "evaluated with cuts" becomes a
function of both the primary inputs `x` and the cut-wire variables
`y`. Each ψ_α(x) of the sum-of-CNFs is built by evaluating `cutValue`
with α plugged in for `y`, and consistency (`α` matching the actual
computed values) selects exactly one term of the sum for each `x`.

## Main definition

* `Circuit.cutValue c F α x w` — value of wire `w` under primary input
  `x` and cut-wire assignment `α`.

## Main results

* `Circuit.cutValue_lt` / `Circuit.cutValue_ge` — unfolding at primary
  inputs and at gates.
* `Circuit.cutValue_eq_wireValue_of_consistent` — when `α` agrees with
  the actual circuit values at the sources of cut edges, `cutValue`
  agrees with the original `wireValue` everywhere.

The "sum over α equals f(x)" of Jukna's Σ₃ argument follows from
consistency: for any given `x` there is exactly one `α` that matches
the actual cut-wire values, and `cutValue` on that `α` recovers
`wireValue`.
-/

namespace Circuit

variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- Build the edge `(input, w)` as a pair in `Fin (N + G + M) × Fin (N + G + M)`,
given that both wires live in `Fin (N + G)`. Used by both the cut-aware
evaluation (`cutValue`) and the reachable-leaves tracking (in
`CutReachable`), hence exported rather than private. -/
def mkEdge {N G M : ℕ} (input : Fin (N + G)) (w : Fin (N + G)) :
    Fin (N + G + M) × Fin (N + G + M) :=
  (⟨input.val, by have := input.isLt; omega⟩,
   ⟨w.val, by have := w.isLt; omega⟩)

/-- Evaluate wire `w` in `c` treating each cut wire (edge in `F`) as a
fresh variable whose value is supplied by `α`. Primary inputs come
from `x`. Defined by well-founded recursion on `w.val`. -/
noncomputable def cutValue (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (x : BitString N) (w : Fin (N + G)) : Bool :=
  if h : w.val < N then x ⟨w.val, h⟩
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    B.eval gate.op gate.fanIn gate.arityOk
      fun k =>
        (gate.negated k).xor
          (if h_cut : @mkEdge N G M (gate.inputs k) w ∈ F then
            α ⟨_, h_cut⟩
          else
            c.cutValue F α x (gate.inputs k))
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- At a primary input wire, `cutValue` just reads from `x`. -/
theorem cutValue_lt (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (x : BitString N) (w : Fin (N + G)) (h : w.val < N) :
    c.cutValue F α x w = x ⟨w.val, h⟩ := by
  rw [cutValue]; simp [h]

/-- At a gate wire, `cutValue` computes the gate's output using the
gate's inputs — but whenever an edge `(input, w)` is cut (i.e., in
`F`), the cut-input's value comes from `α` instead of being computed
recursively. -/
theorem cutValue_ge (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (x : BitString N) (w : Fin (N + G)) (h : ¬ w.val < N) :
    c.cutValue F α x w =
      B.eval (c.gates ⟨w.val - N, by omega⟩).op
        (c.gates ⟨w.val - N, by omega⟩).fanIn
        (c.gates ⟨w.val - N, by omega⟩).arityOk
        (fun k =>
          ((c.gates ⟨w.val - N, by omega⟩).negated k).xor
          (if h_cut : @mkEdge N G M
              ((c.gates ⟨w.val - N, by omega⟩).inputs k) w ∈ F then
            α ⟨_, h_cut⟩
          else
            c.cutValue F α x ((c.gates ⟨w.val - N, by omega⟩).inputs k))) := by
  conv_lhs => rw [cutValue]
  simp [h]

/-- **Consistency.** When `α` agrees with the original circuit's
computed values at every cut edge's source, `cutValue` produces the
same output as plain `wireValue` — for every wire.

Proved by strong induction on `w.val`: a primary-input wire matches by
construction, and a gate's inner function either uses `α` (bound by
consistency to match `wireValue`) or recurses with the inductive
hypothesis. -/
theorem cutValue_eq_wireValue_of_consistent (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (x : BitString N)
    (hα : ∀ (e : ↥F) (hsrc : e.val.1.val < N + G),
      α e = c.wireValue x ⟨e.val.1.val, hsrc⟩)
    (w : Fin (N + G)) :
    c.cutValue F α x w = c.wireValue x w := by
  suffices h_gen : ∀ n : ℕ, ∀ w : Fin (N + G), w.val = n →
      c.cutValue F α x w = c.wireValue x w by
    exact h_gen w.val w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw_val
    by_cases hlt : w.val < N
    · rw [c.cutValue_lt F α x w hlt, c.wireValue_lt x w hlt]
    · rw [c.cutValue_ge F α x w hlt, c.wireValue_ge x w hlt]
      show B.eval _ _ _ _ = (c.gates ⟨w.val - N, by omega⟩).eval (c.wireValue x)
      unfold Gate.eval
      congr 1
      funext k
      congr 1
      split_ifs with h_cut
      · have h_input_lt : ((c.gates ⟨w.val - N, by omega⟩).inputs k).val < N + G :=
          ((c.gates ⟨w.val - N, by omega⟩).inputs k).isLt
        have h_eq := hα ⟨_, h_cut⟩ h_input_lt
        rw [h_eq]
        congr 1
      · apply ih ((c.gates ⟨w.val - N, by omega⟩).inputs k).val _
          ((c.gates ⟨w.val - N, by omega⟩).inputs k) rfl
        have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
        have hval_mk : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
        rw [hval_mk] at hacyc
        show ((c.gates ⟨w.val - N, by omega⟩).inputs k).val < n
        omega

/-- **Self-consistency.** If `α` agrees with `cutValue` itself at every
cut-edge source, then `cutValue F α` agrees with `wireValue` on every
wire. (Weaker hypothesis than `cutValue_eq_wireValue_of_consistent`,
which asks for agreement with `wireValue` directly.) Used by the Σ₃
sum-over-α argument: any α whose ψ_α evaluates true must satisfy this
hypothesis, hence must coincide with the canonical
`α₀ e := wireValue x e.source`. -/
theorem cutValue_eq_wireValue_of_self_consistent (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (x : BitString N)
    (hα : ∀ (e : ↥F) (hsrc : e.val.1.val < N + G),
      c.cutValue F α x ⟨e.val.1.val, hsrc⟩ = α e)
    (w : Fin (N + G)) :
    c.cutValue F α x w = c.wireValue x w := by
  suffices h_gen : ∀ n : ℕ, ∀ w : Fin (N + G), w.val = n →
      c.cutValue F α x w = c.wireValue x w by
    exact h_gen w.val w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw_val
    by_cases hlt : w.val < N
    · rw [c.cutValue_lt F α x w hlt, c.wireValue_lt x w hlt]
    · rw [c.cutValue_ge F α x w hlt, c.wireValue_ge x w hlt]
      show B.eval _ _ _ _ = (c.gates ⟨w.val - N, by omega⟩).eval (c.wireValue x)
      unfold Gate.eval
      congr 1
      funext k
      congr 1
      have h_input_lt : ((c.gates ⟨w.val - N, by omega⟩).inputs k).val < N + G :=
        ((c.gates ⟨w.val - N, by omega⟩).inputs k).isLt
      have h_lt_n : ((c.gates ⟨w.val - N, by omega⟩).inputs k).val < n := by
        have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
        have hval_mk : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
        rw [hval_mk] at hacyc
        omega
      have h_ih := ih ((c.gates ⟨w.val - N, by omega⟩).inputs k).val h_lt_n
        ((c.gates ⟨w.val - N, by omega⟩).inputs k) rfl
      split_ifs with h_cut
      · -- Cut edge: α = cutValue at source = wireValue (by IH).
        rw [(hα ⟨_, h_cut⟩ h_input_lt).symm]
        exact h_ih
      · -- Non-cut: recurse with IH.
        exact h_ih

end Circuit
