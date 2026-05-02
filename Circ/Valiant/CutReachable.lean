import Circ.Valiant.CutValue
import Circ.Depth
import Circ.AON.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Reachable leaves of a cut-aware evaluation

For `Circuit.cutValue c F α x w`, the result depends only on a subset
of the `(x, α)` variables: the primary inputs and cut edges that are
actually consulted while recursively computing the value at `w`.

This file tracks those two "leaf" sets and proves an agreement lemma:
if `(x₁, α₁)` agrees with `(x₂, α₂)` on the reachable leaves of `w`,
then `cutValue` at `w` is the same under both.

## Main definitions

* `Circuit.cutReachableInputs c F w` — primary inputs reached from `w`
  without crossing a cut edge.
* `Circuit.cutReachableEdges c F w` — cut edges encountered during
  cut-aware evaluation at `w`.

## Main results

* `Circuit.cutValue_eq_of_agree` — agreement lemma: `cutValue` at `w`
  only depends on `x` at `cutReachableInputs` and `α` at `cutReachableEdges`.

Deferred (follow-ups):
* Size bound `|cutReachableInputs| + |cutReachableEdges| ≤ 2^d` for
  fan-in-2, where `d` is the cut-aware depth (the depth in
  `c.toDigraph.deleteEdges F`).
-/

namespace Circuit

variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- Primary inputs reached when evaluating `cutValue` at `w`: the
recursion stops at cut edges (which contribute to `cutReachableEdges`
instead) and at primary inputs. -/
noncomputable def cutReachableInputs (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) : Finset (Fin N) :=
  if h : w.val < N then
    {⟨w.val, h⟩}
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    (Finset.univ : Finset (Fin gate.fanIn)).biUnion
      (fun k =>
        if @mkEdge N G M (gate.inputs k) w ∈ F then ∅
        else c.cutReachableInputs F (gate.inputs k))
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Cut edges encountered when evaluating `cutValue` at `w`: collected
as subtype elements of `F`. -/
noncomputable def cutReachableEdges (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) : Finset (↥F) :=
  if h : w.val < N then
    (∅ : Finset (↥F))
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    (Finset.univ : Finset (Fin gate.fanIn)).biUnion
      (fun k =>
        if h_cut : @mkEdge N G M (gate.inputs k) w ∈ F then
          ({⟨_, h_cut⟩} : Finset (↥F))
        else
          c.cutReachableEdges F (gate.inputs k))
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Primary-input wire: only reachable input is itself. -/
theorem cutReachableInputs_of_input (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) (h : w.val < N) :
    c.cutReachableInputs F w = {⟨w.val, h⟩} := by
  rw [cutReachableInputs]; simp [h]

/-- Primary-input wire: no cut edges reachable. -/
theorem cutReachableEdges_of_input (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) (h : w.val < N) :
    c.cutReachableEdges F w = ∅ := by
  rw [cutReachableEdges]; simp [h]

/-- Gate-wire unfolding for `cutReachableInputs`. -/
theorem cutReachableInputs_of_gate (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) (h : ¬ w.val < N) :
    c.cutReachableInputs F w =
      (Finset.univ : Finset (Fin (c.gates ⟨w.val - N, by omega⟩).fanIn)).biUnion
        (fun k =>
          if @mkEdge N G M ((c.gates ⟨w.val - N, by omega⟩).inputs k) w ∈ F then ∅
          else c.cutReachableInputs F
            ((c.gates ⟨w.val - N, by omega⟩).inputs k)) := by
  rw [cutReachableInputs]; simp [h]

/-- Gate-wire unfolding for `cutReachableEdges`. -/
theorem cutReachableEdges_of_gate (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) (h : ¬ w.val < N) :
    c.cutReachableEdges F w =
      (Finset.univ : Finset (Fin (c.gates ⟨w.val - N, by omega⟩).fanIn)).biUnion
        (fun k =>
          if h_cut : @mkEdge N G M ((c.gates ⟨w.val - N, by omega⟩).inputs k) w ∈ F then
            ({⟨_, h_cut⟩} : Finset (↥F))
          else
            c.cutReachableEdges F
              ((c.gates ⟨w.val - N, by omega⟩).inputs k)) := by
  rw [cutReachableEdges]; simp [h]

/-- **Agreement lemma.** If `x₁`/`x₂` agree on `cutReachableInputs` and
`α₁`/`α₂` agree on `cutReachableEdges`, then `cutValue` at `w` is the
same under both. Strong induction on `w.val`. -/
theorem cutValue_eq_of_agree (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    {α₁ α₂ : ↥F → Bool} {x₁ x₂ : BitString N} (w : Fin (N + G))
    (hx : ∀ i ∈ c.cutReachableInputs F w, x₁ i = x₂ i)
    (hα : ∀ e ∈ c.cutReachableEdges F w, α₁ e = α₂ e) :
    c.cutValue F α₁ x₁ w = c.cutValue F α₂ x₂ w := by
  suffices h_gen : ∀ n : ℕ, ∀ w : Fin (N + G), w.val = n →
      ∀ (α₁ α₂ : ↥F → Bool) (x₁ x₂ : BitString N),
        (∀ i ∈ c.cutReachableInputs F w, x₁ i = x₂ i) →
        (∀ e ∈ c.cutReachableEdges F w, α₁ e = α₂ e) →
        c.cutValue F α₁ x₁ w = c.cutValue F α₂ x₂ w by
    exact h_gen w.val w rfl α₁ α₂ x₁ x₂ hx hα
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw_val α₁ α₂ x₁ x₂ hx hα
    by_cases hlt : w.val < N
    · -- Primary input case: both sides read `x i` at `i := ⟨w.val, hlt⟩`,
      -- and `hx` applies since `{⟨w.val, hlt⟩} = cutReachableInputs`.
      rw [c.cutValue_lt F α₁ x₁ w hlt, c.cutValue_lt F α₂ x₂ w hlt]
      apply hx
      rw [c.cutReachableInputs_of_input F w hlt]
      simp
    · -- Gate case.
      rw [c.cutValue_ge F α₁ x₁ w hlt, c.cutValue_ge F α₂ x₂ w hlt]
      congr 1
      funext k
      congr 1
      by_cases h_cut :
          @mkEdge N G M ((c.gates ⟨w.val - N, by omega⟩).inputs k) w ∈ F
      · -- Cut edge: both consult `α` at the edge — agreement by `hα`.
        rw [dif_pos h_cut, dif_pos h_cut]
        apply hα
        rw [c.cutReachableEdges_of_gate F w hlt, Finset.mem_biUnion]
        exact ⟨k, Finset.mem_univ _, by rw [dif_pos h_cut]; simp⟩
      · -- Non-cut: both recurse into the input wire — agreement by IH.
        rw [dif_neg h_cut, dif_neg h_cut]
        have h_lt_n :
            ((c.gates ⟨w.val - N, by omega⟩).inputs k).val < n := by
          have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
          have hval_mk : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
          rw [hval_mk] at hacyc
          omega
        have h_hx_rec :
            ∀ i ∈ c.cutReachableInputs F
                ((c.gates ⟨w.val - N, by omega⟩).inputs k), x₁ i = x₂ i := by
          intro i hi
          apply hx
          rw [c.cutReachableInputs_of_gate F w hlt, Finset.mem_biUnion]
          refine ⟨k, Finset.mem_univ _, ?_⟩
          rw [if_neg h_cut]; exact hi
        have h_hα_rec :
            ∀ e ∈ c.cutReachableEdges F
                ((c.gates ⟨w.val - N, by omega⟩).inputs k), α₁ e = α₂ e := by
          intro e he
          apply hα
          rw [c.cutReachableEdges_of_gate F w hlt, Finset.mem_biUnion]
          refine ⟨k, Finset.mem_univ _, ?_⟩
          rw [dif_neg h_cut]; exact he
        exact ih ((c.gates ⟨w.val - N, by omega⟩).inputs k).val h_lt_n _ rfl
          α₁ α₂ x₁ x₂ h_hx_rec h_hα_rec

/-! ### Cut-aware wireDepth and the fan-in-2 size bound

`cutWireDepth c F w` counts the longest chain of gates that `cutValue`
actually recurses through starting from `w` — stopping at primary
inputs and at cut edges. It mirrors `Circuit.wireDepth`'s `1 + Fin.foldl max`
shape except that each input contributes `0` if its edge to `w` is cut.

For fan-in-2 circuits, the total number of variables `cutValue` consults
at `w` — primary inputs plus cut edges — is at most `2^(cutWireDepth w)`.
This is the tight bound Jukna needs: after `depth_reduction` produces
`F` with `(c.prune.toDigraph.deleteEdges F).depth ≤ 2^(k-r)`, each wire's
`cutWireDepth` will be `≤ 2^(k-r) = ε log n`, so each per-wire
CNF has at most `2^(n^ε)` clauses. -/

/-- Depth of the cut-aware recursion starting at `w`. At a gate, adds 1
and takes the max over inputs, counting each cut input as depth 0
(since the recursion stops there). -/
noncomputable def cutWireDepth (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) : ℕ :=
  if h : w.val < N then 0
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    1 + Fin.foldl gate.fanIn
      (fun acc k =>
        max acc
          (if @mkEdge N G M (gate.inputs k) w ∈ F then 0
           else c.cutWireDepth F (gate.inputs k)))
      0
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

theorem cutWireDepth_of_input (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) (h : w.val < N) :
    c.cutWireDepth F w = 0 := by
  rw [cutWireDepth]; simp [h]

theorem cutWireDepth_of_gate (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) (h : ¬ w.val < N) :
    c.cutWireDepth F w =
      1 + Fin.foldl (c.gates ⟨w.val - N, by omega⟩).fanIn
        (fun acc k =>
          max acc
            (if @mkEdge N G M
                ((c.gates ⟨w.val - N, by omega⟩).inputs k) w ∈ F then 0
             else c.cutWireDepth F
                    ((c.gates ⟨w.val - N, by omega⟩).inputs k)))
        0 := by
  rw [cutWireDepth]; simp [h]

/-- Input-bound for `cutWireDepth`: at any gate, each input's contribution
(either `0` for cut edges, or the input's own `cutWireDepth`) is at most
`cutWireDepth w - 1`. -/
lemma cutWireDepth_input_contrib_lt (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (w : Fin (N + G)) (h : ¬ w.val < N)
    (k : Fin (c.gates ⟨w.val - N, by omega⟩).fanIn) :
    (if @mkEdge N G M
        ((c.gates ⟨w.val - N, by omega⟩).inputs k) w ∈ F then 0
     else c.cutWireDepth F
            ((c.gates ⟨w.val - N, by omega⟩).inputs k)) <
      c.cutWireDepth F w := by
  rw [c.cutWireDepth_of_gate F w h]
  have hge :=
    Circuit.fin_foldl_max_ge
      (fun k' =>
        if @mkEdge N G M
            ((c.gates ⟨w.val - N, by omega⟩).inputs k') w ∈ F then 0
        else c.cutWireDepth F
              ((c.gates ⟨w.val - N, by omega⟩).inputs k')) 0 k
  omega

set_option maxHeartbeats 800000 in
/-- **Fan-in-2 combined-size bound.** The number of primary inputs and
cut edges reached by `cutValue` at `w` is at most `2^(cutWireDepth w)`.
Strong induction on `w.val`: primary inputs contribute `1 = 2^0`; a
fan-in-2 gate either cuts its input (contribution `1 = 2^0`) or
recurses (contribution `≤ 2^(cutWireDepth input) ≤ 2^(cutWireDepth w - 1)`
by IH + `cutWireDepth_input_contrib_lt`). Fan-in = 2 gives the `2^` bump. -/
theorem cutReachable_card_le_pow_cutDepth
    (c : Circuit Basis.andOr2 N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M))) (w : Fin (N + G)) :
    (c.cutReachableInputs F w).card + (c.cutReachableEdges F w).card ≤
      2 ^ c.cutWireDepth F w := by
  suffices h_gen : ∀ n : ℕ, ∀ w : Fin (N + G), w.val = n →
      (c.cutReachableInputs F w).card + (c.cutReachableEdges F w).card ≤
        2 ^ c.cutWireDepth F w by
    exact h_gen w.val w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw_val
    by_cases hlt : w.val < N
    · -- Primary input: 1 + 0 ≤ 2^0 = 1.
      rw [c.cutReachableInputs_of_input F w hlt,
          c.cutReachableEdges_of_input F w hlt,
          c.cutWireDepth_of_input F w hlt]
      simp
    · -- Gate case. Shorten the proof with named abbreviations for the
      -- gate and its per-`k` contribution, then decompose the calc into
      -- simple `Nat.le_trans` steps to keep elaboration fast.
      rw [c.cutReachableInputs_of_gate F w hlt,
          c.cutReachableEdges_of_gate F w hlt]
      set gate := c.gates ⟨w.val - N, by omega⟩ with hgate_def
      let contribI : Fin gate.fanIn → Finset (Fin N) := fun k =>
        if @mkEdge N G M (gate.inputs k) w ∈ F then ∅
        else c.cutReachableInputs F (gate.inputs k)
      let contribE : Fin gate.fanIn → Finset (↥F) := fun k =>
        if h_cut : @mkEdge N G M (gate.inputs k) w ∈ F then
          ({⟨_, h_cut⟩} : Finset (↥F))
        else c.cutReachableEdges F (gate.inputs k)
      have hfanIn : gate.fanIn = 2 := andOr2_fanIn gate
      have hcwd_ge1 : 1 ≤ c.cutWireDepth F w := by
        rw [c.cutWireDepth_of_gate F w hlt]; omega
      have h_each : ∀ k : Fin gate.fanIn,
          (contribI k).card + (contribE k).card ≤
            2 ^ (c.cutWireDepth F w - 1) := by
        intro k
        by_cases h_cut : @mkEdge N G M (gate.inputs k) w ∈ F
        · -- Cut: 0 + 1 ≤ 2^(cutWireDepth w - 1) (since ≥ 1).
          show (contribI k).card + (contribE k).card ≤ _
          simp only [contribI, contribE, if_pos h_cut, dif_pos h_cut]
          simp
          exact Nat.one_le_two_pow
        · -- Non-cut: ≤ 2^(cutWireDepth input) ≤ 2^(cutWireDepth w - 1) by IH.
          show (contribI k).card + (contribE k).card ≤ _
          simp only [contribI, contribE, if_neg h_cut, dif_neg h_cut]
          have h_ih := by
            refine ih (gate.inputs k).val ?_ (gate.inputs k) rfl
            have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
            have hval_mk : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
            rw [hval_mk] at hacyc
            change ((c.gates ⟨w.val - N, by omega⟩).inputs k).val < n
            omega
          have h_cwd_le :
              c.cutWireDepth F (gate.inputs k) ≤ c.cutWireDepth F w - 1 := by
            have hcontrib := c.cutWireDepth_input_contrib_lt F w hlt k
            rw [if_neg h_cut] at hcontrib
            change c.cutWireDepth F ((c.gates ⟨w.val - N, by omega⟩).inputs k) ≤ _
            omega
          exact h_ih.trans (Nat.pow_le_pow_right (by decide) h_cwd_le)
      -- Step 1: split biUnion card into sum of per-`k` cards.
      have h1 :
          (Finset.univ.biUnion contribI).card + (Finset.univ.biUnion contribE).card ≤
            (∑ k, (contribI k).card) + (∑ k, (contribE k).card) :=
        add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      -- Step 2: combine into a single sum of per-`k` totals.
      have h2 :
          (∑ k, (contribI k).card) + (∑ k, (contribE k).card) =
            ∑ k, ((contribI k).card + (contribE k).card) :=
        (Finset.sum_add_distrib).symm
      -- Step 3: per-`k` total is bounded by `2^(cutWireDepth w - 1)`.
      have h3 :
          ∑ k, ((contribI k).card + (contribE k).card) ≤
            ∑ _k : Fin gate.fanIn, 2 ^ (c.cutWireDepth F w - 1) :=
        Finset.sum_le_sum (fun k _ => h_each k)
      -- Step 4: evaluate the constant sum as `fanIn * 2^(…)`.
      have h4 :
          (∑ _k : Fin gate.fanIn, 2 ^ (c.cutWireDepth F w - 1)) =
            gate.fanIn * 2 ^ (c.cutWireDepth F w - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
      -- Step 5: fanIn = 2 and `2 * 2^(d-1) = 2^d`.
      have h5 : gate.fanIn * 2 ^ (c.cutWireDepth F w - 1) = 2 ^ c.cutWireDepth F w := by
        rw [hfanIn]
        conv_rhs =>
          rw [show c.cutWireDepth F w = (c.cutWireDepth F w - 1) + 1 from by omega]
        rw [pow_succ]; exact mul_comm _ _
      calc (Finset.univ.biUnion contribI).card + (Finset.univ.biUnion contribE).card
          ≤ _ := h1
        _ = _ := h2
        _ ≤ _ := h3
        _ = _ := h4
        _ = _ := h5

/-! ### Connecting `cutWireDepth` to the deleted digraph's depth -/

/-- Edge deletion preserves acyclicity: any walk in `G.deleteEdges F` is
also a walk in `G`, so the walk-length set only shrinks. -/
lemma _root_.Digraph.IsAcyclic.deleteEdges {V : Type*} {G : Digraph V}
    (hac : Digraph.IsAcyclic G) (F : Finset (V × V)) :
    Digraph.IsAcyclic (G.deleteEdges F) := by
  obtain ⟨b, hb⟩ := hac
  refine ⟨b, ?_⟩
  rintro m ⟨p, hp⟩
  apply hb
  refine ⟨p, ?_⟩
  intro i h_i
  exact (hp i h_i).1

/-- Witness walk: for every wire `w` with `cutWireDepth ≥ 1`, there is a
directed path in `c.toDigraph.deleteEdges F` of `cutWireDepth w` nodes.
Constructed by strong induction on `w.val`: at a gate with
`cutWireDepth = 1` take the singleton walk `{w}`; at a gate with
`cutWireDepth ≥ 2`, the argmax over non-cut inputs is a wire with
`cutWireDepth = cutWireDepth w - 1 ≥ 1`, and the IH walk extends by
the (non-cut) input edge. -/
lemma exists_walk_of_cutDepth (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M))) (w : Fin (N + G))
    (h_pos : 1 ≤ c.cutWireDepth F w) :
    ∃ p : Fin (c.cutWireDepth F w) → Fin (N + G + M),
      (c.toDigraph.deleteEdges F).IsDirectedPath p := by
  -- Strengthened form: walk of length `m` (= cutWireDepth F w) ending at
  -- `w`'s vertex. The extra `ends-at` assertion is what makes the
  -- extension step work: the IH gives a walk ending at the argmax input,
  -- and we append the edge from that input to `w`.
  suffices h_gen : ∀ n m : ℕ, ∀ w : Fin (N + G), w.val = n →
      c.cutWireDepth F w = m → ∀ (hm : 1 ≤ m),
      ∃ p : Fin m → Fin (N + G + M),
        (c.toDigraph.deleteEdges F).IsDirectedPath p ∧
        p ⟨m - 1, Nat.sub_lt (by omega) Nat.one_pos⟩ =
          ⟨w.val, by have := w.isLt; omega⟩ by
    obtain ⟨p, hp, _⟩ := h_gen w.val (c.cutWireDepth F w) w rfl rfl h_pos
    exact ⟨p, hp⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m w hw_val hcwd hm_pos
    -- `w` is not a primary input (otherwise cutWireDepth = 0 ≠ m ≥ 1).
    have hlt : ¬ w.val < N := by
      intro hlt
      rw [c.cutWireDepth_of_input F w hlt] at hcwd
      omega
    -- Inner max value: L = m - 1, since cutWireDepth w = 1 + L.
    let inner : Fin (c.gates ⟨w.val - N, by omega⟩).fanIn → ℕ := fun k =>
      if @mkEdge N G M ((c.gates ⟨w.val - N, by omega⟩).inputs k) w ∈ F then 0
      else c.cutWireDepth F ((c.gates ⟨w.val - N, by omega⟩).inputs k)
    have hcwd_gate := c.cutWireDepth_of_gate F w hlt
    let L := Fin.foldl (c.gates ⟨w.val - N, by omega⟩).fanIn
      (fun acc k => max acc (inner k)) 0
    have hL_def : L = Fin.foldl (c.gates ⟨w.val - N, by omega⟩).fanIn
        (fun acc k => max acc (inner k)) 0 := rfl
    have h_m_eq : m = 1 + L := by
      have : c.cutWireDepth F w = 1 + L := hcwd_gate
      omega
    by_cases hL : L = 0
    · -- `cutWireDepth = 1`: singleton walk `{w}`.
      have hm_one : m = 1 := by omega
      subst hm_one
      refine ⟨fun _ => ⟨w.val, by have := w.isLt; omega⟩, ?_, rfl⟩
      intro i hi
      exfalso
      have := i.isLt
      omega
    · -- `cutWireDepth ≥ 2`: extend IH walk by the argmax non-cut input.
      have hL_pos : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL
      have h_fanIn_pos : 0 < (c.gates ⟨w.val - N, by omega⟩).fanIn := by
        by_contra h
        push_neg at h
        have h0 : (c.gates ⟨w.val - N, by omega⟩).fanIn = 0 := Nat.le_zero.mp h
        -- For empty fanIn, `L = Fin.foldl 0 _ 0 = 0`, contradicting `hL`.
        have aux : ∀ (k : ℕ) (_ : k = 0) (g : ℕ → Fin k → ℕ), Fin.foldl k g 0 = 0 := by
          intro k hk g; subst hk; exact Fin.foldl_zero g 0
        exact hL (aux _ h0 _)
      have h_ne : (Finset.univ : Finset
          (Fin (c.gates ⟨w.val - N, by omega⟩).fanIn)).Nonempty :=
        Finset.univ_nonempty_iff.mpr ⟨⟨0, h_fanIn_pos⟩⟩
      obtain ⟨k_max, _, hmax⟩ :=
        Finset.exists_max_image Finset.univ inner h_ne
      -- `inner k_max = L`: matches the fold upper and lower bounds.
      have h_inner_k_max : inner k_max = L := by
        apply Nat.le_antisymm
        · exact Circuit.fin_foldl_max_ge inner 0 k_max
        · apply Circuit.fin_foldl_max_le_ub
          · omega
          · intro k'
            exact hmax k' (Finset.mem_univ _)
      -- k_max is not a cut edge (else its contribution would be 0 < L).
      have h_cut_not :
          @mkEdge N G M ((c.gates ⟨w.val - N, by omega⟩).inputs k_max) w ∉ F := by
        intro h_cut
        have h0 : inner k_max = 0 := by simp only [inner, if_pos h_cut]
        omega
      -- cutWireDepth of the argmax input = L.
      have h_u_cwd :
          c.cutWireDepth F ((c.gates ⟨w.val - N, by omega⟩).inputs k_max) = L := by
        have := h_inner_k_max
        simp only [inner, if_neg h_cut_not] at this
        exact this
      have h_u_lt :
          ((c.gates ⟨w.val - N, by omega⟩).inputs k_max).val < n := by
        have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k_max
        have hval_mk : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
        rw [hval_mk] at hacyc
        change ((c.gates ⟨w.val - N, by omega⟩).inputs k_max).val < n
        omega
      obtain ⟨p', hp'_path, hp'_last⟩ :=
        ih ((c.gates ⟨w.val - N, by omega⟩).inputs k_max).val h_u_lt L _ rfl
          h_u_cwd hL_pos
      -- Extend `p'` (length L = m - 1, ending at input k_max's vertex)
      -- by `w`'s vertex.
      have hm_L : m - 1 = L := by omega
      let w_vtx : Fin (N + G + M) := ⟨w.val, by have := w.isLt; omega⟩
      let p : Fin m → Fin (N + G + M) := fun i =>
        if hi : i.val < m - 1 then
          p' ⟨i.val, by rw [← hm_L]; exact hi⟩
        else
          w_vtx
      refine ⟨p, ?_, ?_⟩
      · -- Directed-path property: check each consecutive pair.
        intro i hii
        by_cases hi_plus_lt : i.val + 1 < m - 1
        · -- Both indices fall in the `p'` range.
          have hi_lt : i.val < m - 1 := by omega
          show (c.toDigraph.deleteEdges F).Adj (p i) (p _)
          simp only [p, dif_pos hi_lt, dif_pos hi_plus_lt]
          have h_in_L : i.val + 1 < L := by rw [← hm_L]; exact hi_plus_lt
          exact hp'_path ⟨i.val, by
            have : i.val < L := by omega
            exact this⟩ h_in_L
        · -- i + 1 = m - 1 = L: append the edge `input → w`.
          have h_i_plus : i.val + 1 = m - 1 := by omega
          have hi_lt : i.val < m - 1 := by omega
          have h_not : ¬ (i.val + 1) < m - 1 := by omega
          show (c.toDigraph.deleteEdges F).Adj (p i) (p _)
          simp only [p, dif_pos hi_lt, dif_neg h_not]
          have h_i_eq : i.val = L - 1 := by omega
          have hp_cast : p' ⟨i.val, by
              have : i.val < L := by omega
              exact this⟩ = p' ⟨L - 1, by omega⟩ := by
            congr 1
            apply Fin.ext
            exact h_i_eq
          rw [hp_cast, hp'_last]
          -- Adj in `deleteEdges F`: the toDigraph edge exists and is not in F.
          refine ⟨?_, ?_⟩
          · -- toDigraph: gate at position `w.val - N` has input
            -- `gate.inputs k_max` at slot k_max.
            left
            refine ⟨⟨w.val - N, by omega⟩, ?_, k_max, rfl⟩
            show w.val = N + (w.val - N); omega
          · -- Not in F: follows from h_cut_not via the mkEdge encoding.
            intro h_in
            apply h_cut_not
            show @mkEdge N G M
                ((c.gates ⟨w.val - N, by omega⟩).inputs k_max) w ∈ F
            convert h_in using 2
      · -- Last element is `w`'s vertex.
        show p _ = _
        have h_not : ¬ (m - 1 : ℕ) < m - 1 := lt_irrefl _
        simp only [p, dif_neg h_not]
        rfl

/-- **Cut-aware wireDepth vs. deleted-graph depth.** For every wire `w`,
`cutWireDepth F w ≤ (c.toDigraph.deleteEdges F).depth`. Combined with
`Valiant.depth_reduction`'s output, this gives the bound on the
per-subcircuit input count that Jukna needs: `2^cutWireDepth ≤ 2^(2^(k-r))
= 2^(n^ε)` after plugging in the Valiant parameters. -/
theorem cutWireDepth_le_deleted_depth (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M))) (w : Fin (N + G)) :
    c.cutWireDepth F w ≤ (c.toDigraph.deleteEdges F).depth := by
  by_cases h : 1 ≤ c.cutWireDepth F w
  · obtain ⟨p, hp⟩ := c.exists_walk_of_cutDepth F w h
    have h_mem : c.cutWireDepth F w ∈
        { m | ∃ p : Fin m → Fin (N + G + M),
              (c.toDigraph.deleteEdges F).IsDirectedPath p } :=
      ⟨p, hp⟩
    have h_bdd : Digraph.IsAcyclic (c.toDigraph.deleteEdges F) :=
      c.toDigraph_acyclic.deleteEdges F
    show c.cutWireDepth F w ≤ sSup _
    exact le_csSup h_bdd h_mem
  · push_neg at h
    have : c.cutWireDepth F w = 0 := by omega
    rw [this]
    exact Nat.zero_le _

end Circuit
