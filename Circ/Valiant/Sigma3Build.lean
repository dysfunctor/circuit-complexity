import Circ.Valiant.CutReachable
import Circ.NF.FromFunction
import Circ.AON.Defs

/-! # Σ₃ representation construction

Given a fan-in-2 single-output circuit `c`, a cut-edge set `F` from
`Valiant.depth_reduction`, and a per-edge assignment `α : ↥F → Bool`,
this file builds a single CNF `psiCNF c F α` on the primary inputs that:

* equals `1` iff `α` matches the actual circuit's wire-values at every
  cut edge's source AND the output (with cuts substituted by `α`)
  evaluates to `1`,
* has clause count bounded by `(|F| + 1) · 2 ^ (2 ^ (deletedDepth + 1))`,
* whose sum over `α : ↥F → Bool` is exactly the circuit's output, viewed
  as a `0/1` value.

These are the three properties needed to package the family
`{psiCNF c F α}` into a `Sigma3Rep`.

## Main definitions

* `Circuit.mkOutputEdge` — encode an edge from a wire into an output gate.
* `Circuit.cutOutputValue` — output value with cuts replaced by `α`.
* `Circuit.outputCutReachableInputs` / `outputCutReachableEdges` — the
  variable supports of `cutOutputValue` as a function of `(x, α)`.

## Main results

* `Circuit.cutOutputValue_eq_of_agree` — agreement lemma for
  `cutOutputValue`.
-/

namespace Circuit

variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- Build the digraph edge `(input, output_j)` as a pair in
`Fin (N + G + M) × Fin (N + G + M)`. Counterpart of `mkEdge` for edges
into output gates. -/
def mkOutputEdge {N G M : ℕ} (input : Fin (N + G)) (j : Fin M) :
    Fin (N + G + M) × Fin (N + G + M) :=
  (⟨input.val, by have := input.isLt; omega⟩,
   ⟨N + G + j.val, by have := j.isLt; omega⟩)

/-- Output value of `c` at output gate `j` under cut-aware wire
evaluation: each output input wire whose edge is cut by `F` is replaced
by the corresponding `α` value, and otherwise uses `c.cutValue`. -/
noncomputable def cutOutputValue (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (x : BitString N) (j : Fin M) : Bool :=
  B.eval (c.outputs j).op (c.outputs j).fanIn (c.outputs j).arityOk
    fun k =>
      ((c.outputs j).negated k).xor
        (if h_cut : @mkOutputEdge N G M ((c.outputs j).inputs k) j ∈ F then
          α ⟨_, h_cut⟩
         else
          c.cutValue F α x ((c.outputs j).inputs k))

/-- Primary inputs that `cutOutputValue` consults: union over the output
gate's input wires of `cutReachableInputs` (with cut output-incident
wires contributing nothing). -/
noncomputable def outputCutReachableInputs (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (j : Fin M) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin (c.outputs j).fanIn)).biUnion
    (fun k =>
      if @mkOutputEdge N G M ((c.outputs j).inputs k) j ∈ F then ∅
      else c.cutReachableInputs F ((c.outputs j).inputs k))

/-- Cut edges that `cutOutputValue` consults: the output-incident cut
edges directly, plus `cutReachableEdges` for non-cut output input wires. -/
noncomputable def outputCutReachableEdges (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (j : Fin M) : Finset (↥F) :=
  (Finset.univ : Finset (Fin (c.outputs j).fanIn)).biUnion
    (fun k =>
      if h_cut : @mkOutputEdge N G M ((c.outputs j).inputs k) j ∈ F then
        ({⟨_, h_cut⟩} : Finset (↥F))
      else
        c.cutReachableEdges F ((c.outputs j).inputs k))

/-- **Agreement lemma for the output.** `cutOutputValue` depends on `x`
only through `outputCutReachableInputs` and on `α` only through
`outputCutReachableEdges`. -/
theorem cutOutputValue_eq_of_agree (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    {α₁ α₂ : ↥F → Bool} {x₁ x₂ : BitString N} (j : Fin M)
    (hx : ∀ i ∈ c.outputCutReachableInputs F j, x₁ i = x₂ i)
    (hα : ∀ e ∈ c.outputCutReachableEdges F j, α₁ e = α₂ e) :
    c.cutOutputValue F α₁ x₁ j = c.cutOutputValue F α₂ x₂ j := by
  unfold cutOutputValue
  congr 1
  funext k
  congr 1
  by_cases h_cut : @mkOutputEdge N G M ((c.outputs j).inputs k) j ∈ F
  · -- Cut output edge: both sides take α.
    rw [dif_pos h_cut, dif_pos h_cut]
    apply hα
    rw [outputCutReachableEdges, Finset.mem_biUnion]
    exact ⟨k, Finset.mem_univ _, by rw [dif_pos h_cut]; simp⟩
  · -- Non-cut output edge: both sides recurse via cutValue.
    rw [dif_neg h_cut, dif_neg h_cut]
    apply c.cutValue_eq_of_agree F ((c.outputs j).inputs k)
    · intro i hi
      apply hx
      rw [outputCutReachableInputs, Finset.mem_biUnion]
      exact ⟨k, Finset.mem_univ _, by rw [if_neg h_cut]; exact hi⟩
    · intro e he
      apply hα
      rw [outputCutReachableEdges, Finset.mem_biUnion]
      exact ⟨k, Finset.mem_univ _, by rw [dif_neg h_cut]; exact he⟩

/-! ### Per-piece CNFs

For each fixed `α : ↥F → Bool`, we build:

* `outputCNF c F α j` — a CNF on `BitString N` whose evaluation at `x`
  equals `cutOutputValue c F α x j`.
* `consistencyCNF c F α e` — a CNF whose evaluation at `x` equals
  `decide (c.cutValue F α x e.source = α e)`, encoding the consistency
  check at cut edge `e`.

Both use `CNF.fromFunctionOnSet` with the appropriate reachable-input
support, so each CNF has at most `2 ^ |support|` clauses. -/

/-- CNF on `BitString N` whose evaluation at `x` is `cutOutputValue F α x j`.
Built via `fromFunctionOnSet` on the support `outputCutReachableInputs`. -/
noncomputable def outputCNF (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (j : Fin M) : CNF N :=
  CNF.fromFunctionOnSet
    (fun x => c.cutOutputValue F α x j)
    (c.outputCutReachableInputs F j)
    (fun _ _ hxy =>
      c.cutOutputValue_eq_of_agree F j hxy (fun _ _ => rfl))

theorem outputCNF_eval (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (j : Fin M) (x : BitString N) :
    (c.outputCNF F α j).eval x = c.cutOutputValue F α x j :=
  CNF.fromFunctionOnSet_eval _ _ _ x

theorem outputCNF_complexity_le (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (j : Fin M) :
    (c.outputCNF F α j).complexity ≤ 2 ^ (c.outputCutReachableInputs F j).card :=
  CNF.fromFunctionOnSet_complexity_le _ _ _

/-- The "source wire" of an edge `e ∈ F` whose source falls within the
wire range `[0, N + G)`. Used to define `consistencyCNF`. -/
def edgeSourceWire {N G M : ℕ}
    {F : Finset (Fin (N + G + M) × Fin (N + G + M))}
    (e : ↥F) (h : e.val.1.val < N + G) : Fin (N + G) :=
  ⟨e.val.1.val, h⟩

/-- CNF on `BitString N` whose evaluation at `x` is `decide (cutValue F α x s = α e)`,
i.e., `1` iff `α` matches `cutValue` at `e`'s source. Support is
`cutReachableInputs F s`, giving `≤ 2 ^ |support|` clauses. -/
noncomputable def consistencyCNF (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (e : ↥F) (h : e.val.1.val < N + G) : CNF N :=
  let s : Fin (N + G) := edgeSourceWire e h
  CNF.fromFunctionOnSet
    (fun x => decide (c.cutValue F α x s = α e))
    (c.cutReachableInputs F s)
    (fun x y hxy => by
      show decide (c.cutValue F α x s = α e) = decide (c.cutValue F α y s = α e)
      rw [c.cutValue_eq_of_agree F s hxy (fun _ _ => rfl)])

theorem consistencyCNF_eval (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (e : ↥F) (h : e.val.1.val < N + G) (x : BitString N) :
    (c.consistencyCNF F α e h).eval x =
      decide (c.cutValue F α x (edgeSourceWire e h) = α e) :=
  CNF.fromFunctionOnSet_eval _ _ _ x

theorem consistencyCNF_complexity_le (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (e : ↥F) (h : e.val.1.val < N + G) :
    (c.consistencyCNF F α e h).complexity ≤
      2 ^ (c.cutReachableInputs F (edgeSourceWire e h)).card :=
  CNF.fromFunctionOnSet_complexity_le _ _ _

/-! ### Combining: psiCNF -/

/-- All consistency CNFs as a list, one per edge in `F`. The hypothesis
`hF` certifies that every edge in `F` has its source within the wire
range; this holds for any `F` derived from `c.toDigraph.edgeFinset`. -/
noncomputable def consistencyCNFs (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool)
    (hF : ∀ e ∈ F, e.1.val < N + G) : List (CNF N) :=
  F.attach.toList.map fun e => c.consistencyCNF F α e (hF e.val e.property)

/-- The Σ₃ "ψ_α" CNF: output cut-aware value AND all consistency checks. -/
noncomputable def psiCNF (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (j : Fin M)
    (hF : ∀ e ∈ F, e.1.val < N + G) : CNF N :=
  (c.outputCNF F α j).and (CNF.bigAnd (c.consistencyCNFs F α hF))

theorem psiCNF_eval (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (j : Fin M)
    (hF : ∀ e ∈ F, e.1.val < N + G) (x : BitString N) :
    (c.psiCNF F α j hF).eval x =
      (c.cutOutputValue F α x j &&
        (c.consistencyCNFs F α hF).all (fun φ => φ.eval x)) := by
  rw [psiCNF, CNF.and_eval, c.outputCNF_eval, CNF.bigAnd_eval]

theorem consistencyCNFs_eval_iff (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (hF : ∀ e ∈ F, e.1.val < N + G) (x : BitString N) :
    (c.consistencyCNFs F α hF).all (fun φ => φ.eval x) = true ↔
      ∀ e : ↥F, c.cutValue F α x (edgeSourceWire e (hF e.val e.property)) = α e := by
  constructor
  · intro hall e
    have he_mem : c.consistencyCNF F α e (hF e.val e.property) ∈
        c.consistencyCNFs F α hF := by
      simp only [consistencyCNFs, List.mem_map, Finset.mem_toList, Finset.mem_attach,
        true_and]
      exact ⟨e, rfl⟩
    have heval : (c.consistencyCNF F α e (hF e.val e.property)).eval x = true :=
      List.all_eq_true.mp hall _ he_mem
    rw [c.consistencyCNF_eval F α e (hF e.val e.property), decide_eq_true_eq] at heval
    exact heval
  · intro hcons
    rw [List.all_eq_true]
    intro φ hφ
    simp only [consistencyCNFs, List.mem_map, Finset.mem_toList, Finset.mem_attach,
      true_and] at hφ
    obtain ⟨e, he⟩ := hφ
    rw [← he, c.consistencyCNF_eval F α e (hF e.val e.property), decide_eq_true_eq]
    exact hcons e

/-! ### Sum-over-α equals the circuit output -/

/-- Canonical "consistent" α for input `x`: each edge maps to the
`wireValue` at its source. -/
noncomputable def canonicalAlpha (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (hF : ∀ e ∈ F, e.1.val < N + G) (x : BitString N) : ↥F → Bool :=
  fun e => c.wireValue x ⟨e.val.1.val, hF e.val e.property⟩

/-- The canonical α satisfies the consistency hypothesis of
`cutValue_eq_wireValue_of_consistent`. -/
private lemma canonicalAlpha_eq_wireValue (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (hF : ∀ e ∈ F, e.1.val < N + G) (x : BitString N) :
    ∀ (e : ↥F) (hsrc : e.val.1.val < N + G),
      c.canonicalAlpha F hF x e = c.wireValue x ⟨e.val.1.val, hsrc⟩ := by
  intro e hsrc
  show c.wireValue x ⟨e.val.1.val, hF e.val e.property⟩ =
    c.wireValue x ⟨e.val.1.val, hsrc⟩
  rfl

/-- For the canonical α, `cutValue` equals `wireValue` everywhere. -/
private lemma cutValue_canonicalAlpha (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (hF : ∀ e ∈ F, e.1.val < N + G) (x : BitString N) (w : Fin (N + G)) :
    c.cutValue F (c.canonicalAlpha F hF x) x w = c.wireValue x w :=
  c.cutValue_eq_wireValue_of_consistent F (c.canonicalAlpha F hF x) x
    (c.canonicalAlpha_eq_wireValue F hF x) w

/-- For the canonical α, the cut-aware output equals the circuit's
output: every output input wire's contribution (cut or non-cut) reduces
to `wireValue x (input k)`. -/
private lemma cutOutputValue_canonicalAlpha (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (hF : ∀ e ∈ F, e.1.val < N + G) (x : BitString N) (j : Fin M) :
    c.cutOutputValue F (c.canonicalAlpha F hF x) x j = (c.eval x) j := by
  show B.eval _ _ _ _ = (c.outputs j).eval (c.wireValue x)
  unfold Gate.eval
  congr 1
  funext k
  congr 1
  by_cases h_cut : @mkOutputEdge N G M ((c.outputs j).inputs k) j ∈ F
  · rw [dif_pos h_cut]
    show c.canonicalAlpha F hF x ⟨_, h_cut⟩ = c.wireValue x ((c.outputs j).inputs k)
    show c.wireValue x ⟨((c.outputs j).inputs k).val, _⟩ =
      c.wireValue x ((c.outputs j).inputs k)
    rfl
  · rw [dif_neg h_cut]
    exact c.cutValue_canonicalAlpha F hF x ((c.outputs j).inputs k)

/-- **Uniqueness.** Any α whose ψ_α evaluates true at `x` must be the
canonical α. The argument: ψ_α true ⇒ all consistency checks pass ⇒
cutValue F α x = wireValue x by `cutValue_eq_wireValue_of_self_consistent`
⇒ α e = cutValue F α x e.source = wireValue x e.source = canonicalAlpha e. -/
private lemma alpha_eq_canonical_of_consistent (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (hF : ∀ e ∈ F, e.1.val < N + G) (x : BitString N)
    (hcons : ∀ e : ↥F,
      c.cutValue F α x (edgeSourceWire e (hF e.val e.property)) = α e) :
    α = c.canonicalAlpha F hF x := by
  funext e
  have h_eq_w : c.cutValue F α x ⟨e.val.1.val, hF e.val e.property⟩ =
      c.wireValue x ⟨e.val.1.val, hF e.val e.property⟩ := by
    apply c.cutValue_eq_wireValue_of_self_consistent F α x
    intro e' hsrc'
    have h := hcons e'
    show c.cutValue F α x _ = α e'
    have : (⟨e'.val.1.val, hsrc'⟩ : Fin (N + G)) =
        edgeSourceWire e' (hF e'.val e'.property) := rfl
    rw [this]
    exact h
  have h_α := hcons e
  show α e = c.canonicalAlpha F hF x e
  rw [show c.canonicalAlpha F hF x e =
    c.wireValue x ⟨e.val.1.val, hF e.val e.property⟩ from rfl,
      ← h_eq_w, ← h_α]
  rfl

/-- **Sum-over-α equals f.** For each `x`, exactly one `α` (the
canonical one) makes `ψ_α(x)` true; on that α, `ψ_α(x) = (c.eval x) j`. -/
theorem sum_psiCNF_eval_eq (c : Circuit B N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (j : Fin M) (hF : ∀ e ∈ F, e.1.val < N + G) (x : BitString N) :
    (∑ α : ↥F → Bool, (if (c.psiCNF F α j hF).eval x then 1 else 0 : ℕ)) =
      if (c.eval x) j then 1 else 0 := by
  classical
  set α₀ := c.canonicalAlpha F hF x with hα₀_def
  have hα₀_eval : (c.psiCNF F α₀ j hF).eval x = (c.eval x) j := by
    rw [c.psiCNF_eval F α₀ j hF]
    have hcons : (c.consistencyCNFs F α₀ hF).all (fun φ => φ.eval x) = true := by
      rw [List.all_eq_true]
      intro φ hφ_mem
      simp only [consistencyCNFs, List.mem_map, Finset.mem_toList, Finset.mem_attach,
        true_and] at hφ_mem
      obtain ⟨e, he⟩ := hφ_mem
      rw [← he, c.consistencyCNF_eval F α₀ e (hF e.val e.property), decide_eq_true_eq]
      show c.cutValue F α₀ x _ = α₀ e
      rw [c.cutValue_canonicalAlpha F hF x]
      rfl
    rw [hcons, Bool.and_true]
    exact c.cutOutputValue_canonicalAlpha F hF x j
  -- Sum equals the α₀ contribution alone.
  rw [show (∑ α : ↥F → Bool, (if (c.psiCNF F α j hF).eval x then 1 else 0 : ℕ)) =
      ∑ α ∈ Finset.univ, (if (c.psiCNF F α j hF).eval x then 1 else 0 : ℕ) from rfl]
  rw [Finset.sum_eq_single α₀]
  · rw [hα₀_eval]
  · -- For α ≠ α₀: ψ_α x = false.
    intro α _ hαne
    have h_eval_false : (c.psiCNF F α j hF).eval x = false := by
      by_contra heval
      apply hαne
      have heval_true : (c.psiCNF F α j hF).eval x = true := by
        cases hb : (c.psiCNF F α j hF).eval x
        · exact absurd hb heval
        · rfl
      rw [c.psiCNF_eval F α j hF, Bool.and_eq_true] at heval_true
      obtain ⟨_, hcons⟩ := heval_true
      rw [c.consistencyCNFs_eval_iff F α hF x] at hcons
      exact c.alpha_eq_canonical_of_consistent F α hF x hcons
    rw [h_eval_false]; rfl
  · intro h; exact absurd (Finset.mem_univ α₀) h

/-! ### Complexity bounds and Σ₃ packaging -/

/-- Per-wire bound: cutReachableInputs has at most `2 ^ deletedDepth` inputs. -/
lemma cutReachableInputs_card_le_pow_deleted_depth
    (c : Circuit Basis.andOr2 N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M))) (w : Fin (N + G)) :
    (c.cutReachableInputs F w).card ≤ 2 ^ (c.toDigraph.deleteEdges F).depth := by
  have h1 := c.cutReachable_card_le_pow_cutDepth F w
  have h2 := c.cutWireDepth_le_deleted_depth F w
  calc (c.cutReachableInputs F w).card
      ≤ (c.cutReachableInputs F w).card + (c.cutReachableEdges F w).card :=
        Nat.le_add_right _ _
    _ ≤ 2 ^ c.cutWireDepth F w := h1
    _ ≤ 2 ^ (c.toDigraph.deleteEdges F).depth :=
        Nat.pow_le_pow_right two_pos h2

/-- Output's input cone (cut-aware) for fan-in-2 has at most `2 ^ (d+1)` inputs. -/
lemma outputCutReachableInputs_card_le
    (c : Circuit Basis.andOr2 N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M))) (j : Fin M) :
    (c.outputCutReachableInputs F j).card ≤
      2 ^ ((c.toDigraph.deleteEdges F).depth + 1) := by
  set d := (c.toDigraph.deleteEdges F).depth
  have hfanIn : (c.outputs j).fanIn = 2 := andOr2_fanIn (c.outputs j)
  have h_each : ∀ k : Fin (c.outputs j).fanIn,
      (if @mkOutputEdge N G M ((c.outputs j).inputs k) j ∈ F then
         (∅ : Finset (Fin N))
       else c.cutReachableInputs F ((c.outputs j).inputs k)).card ≤ 2 ^ d := by
    intro k
    by_cases h_cut : @mkOutputEdge N G M ((c.outputs j).inputs k) j ∈ F
    · simp [h_cut]
    · simp only [if_neg h_cut]
      exact c.cutReachableInputs_card_le_pow_deleted_depth F _
  calc (c.outputCutReachableInputs F j).card
      ≤ ∑ k : Fin (c.outputs j).fanIn,
          (if @mkOutputEdge N G M ((c.outputs j).inputs k) j ∈ F then
             (∅ : Finset (Fin N))
           else c.cutReachableInputs F ((c.outputs j).inputs k)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k : Fin (c.outputs j).fanIn, 2 ^ d :=
          Finset.sum_le_sum (fun k _ => h_each k)
    _ = (c.outputs j).fanIn * 2 ^ d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    _ = 2 * 2 ^ d := by rw [hfanIn]
    _ = 2 ^ (d + 1) := by rw [pow_succ]; ring

/-- `outputCNF` has at most `2 ^ (2 ^ (d+1))` clauses. -/
lemma outputCNF_complexity_le_pow_pow
    (c : Circuit Basis.andOr2 N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (j : Fin M) :
    (c.outputCNF F α j).complexity ≤
      2 ^ (2 ^ ((c.toDigraph.deleteEdges F).depth + 1)) := by
  exact (c.outputCNF_complexity_le F α j).trans
    (Nat.pow_le_pow_right two_pos
      (c.outputCutReachableInputs_card_le F j))

/-- Each consistency CNF has at most `2 ^ (2 ^ d)` clauses. -/
lemma consistencyCNF_complexity_le_pow_pow
    (c : Circuit Basis.andOr2 N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (e : ↥F) (h : e.val.1.val < N + G) :
    (c.consistencyCNF F α e h).complexity ≤
      2 ^ (2 ^ (c.toDigraph.deleteEdges F).depth) := by
  exact (c.consistencyCNF_complexity_le F α e h).trans
    (Nat.pow_le_pow_right two_pos
      (c.cutReachableInputs_card_le_pow_deleted_depth F _))

/-- **Per-α complexity bound.** Each `ψ_α` has at most
`(|F| + 1) · 2 ^ (2 ^ (d + 1))` clauses, where `d = (deleteEdges F).depth`. -/
theorem psiCNF_complexity_le
    (c : Circuit Basis.andOr2 N M G)
    (F : Finset (Fin (N + G + M) × Fin (N + G + M)))
    (α : ↥F → Bool) (j : Fin M)
    (hF : ∀ e ∈ F, e.1.val < N + G) :
    (c.psiCNF F α j hF).complexity ≤
      (F.card + 1) * 2 ^ (2 ^ ((c.toDigraph.deleteEdges F).depth + 1)) := by
  set d := (c.toDigraph.deleteEdges F).depth
  rw [psiCNF, CNF.and_complexity, CNF.bigAnd_complexity]
  -- Output term ≤ 2^(2^(d+1))
  have h_out := c.outputCNF_complexity_le_pow_pow F α j
  -- Each consistency term ≤ 2^(2^d) ≤ 2^(2^(d+1))
  have h_pow_le : (2 : ℕ) ^ (2 ^ d) ≤ 2 ^ (2 ^ (d + 1)) :=
    Nat.pow_le_pow_right two_pos
      (Nat.pow_le_pow_right two_pos (by omega))
  have h_each : ∀ φ ∈ c.consistencyCNFs F α hF,
      φ.complexity ≤ 2 ^ (2 ^ (d + 1)) := by
    intro φ hφ
    simp only [consistencyCNFs, List.mem_map, Finset.mem_toList, Finset.mem_attach,
      true_and] at hφ
    obtain ⟨e, he⟩ := hφ
    rw [← he]
    exact (c.consistencyCNF_complexity_le_pow_pow F α e _).trans h_pow_le
  -- Sum of consistency complexities ≤ |F| * 2^(2^(d+1)).
  have h_sum :
      ((c.consistencyCNFs F α hF).map CNF.complexity).sum ≤
        F.card * 2 ^ (2 ^ (d + 1)) := by
    have h_len : (c.consistencyCNFs F α hF).length = F.card := by
      simp only [consistencyCNFs, List.length_map, Finset.length_toList,
        Finset.card_attach]
    have hbound :
        ((c.consistencyCNFs F α hF).map CNF.complexity).sum ≤
          (c.consistencyCNFs F α hF).length * 2 ^ (2 ^ (d + 1)) := by
      have : ∀ n ∈ (c.consistencyCNFs F α hF).map CNF.complexity,
          n ≤ 2 ^ (2 ^ (d + 1)) := by
        intro n hn
        rw [List.mem_map] at hn
        obtain ⟨φ, hφ, hn_eq⟩ := hn
        rw [← hn_eq]
        exact h_each φ hφ
      have hL : ((c.consistencyCNFs F α hF).map CNF.complexity).length =
          (c.consistencyCNFs F α hF).length := List.length_map _
      calc ((c.consistencyCNFs F α hF).map CNF.complexity).sum
          ≤ ((c.consistencyCNFs F α hF).map CNF.complexity).length *
              2 ^ (2 ^ (d + 1)) :=
            List.sum_le_card_nsmul _ _ this
        _ = (c.consistencyCNFs F α hF).length * 2 ^ (2 ^ (d + 1)) := by rw [hL]
    rw [h_len] at hbound
    exact hbound
  -- Combine.
  calc (c.outputCNF F α j).complexity +
          ((c.consistencyCNFs F α hF).map CNF.complexity).sum
      ≤ 2 ^ (2 ^ (d + 1)) + F.card * 2 ^ (2 ^ (d + 1)) :=
        Nat.add_le_add h_out h_sum
    _ = (F.card + 1) * 2 ^ (2 ^ (d + 1)) := by ring

end Circuit
