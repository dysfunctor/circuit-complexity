import Circ.Basic
import Circ.Valiant
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-! # Circuit → Digraph Translation

Package a `Circuit B N M G` as a `Digraph` so that `Valiant.depth_reduction`
can be applied to it. This translation is basis-agnostic: it works for any
`B`, any fan-in. Fan-in-specific bounds (e.g. `S ≤ 2 · size` for fan-in-2)
are stated separately, downstream of this file.

## Vertex encoding

Vertices are `Fin (N + G + M)`, laid out contiguously:

* `0 ≤ v.val < N`       — primary inputs
* `N ≤ v.val < N + G`   — internal gates (gate `i` ↔ vertex `N + i`)
* `N + G ≤ v.val`       — output gates (output `j` ↔ vertex `N + G + j`)

Since each `Gate` records its fan-in wires as `Fin (N + G)`, every gate
input naturally lands at a vertex index in `[0, N + G)`.

## Main definitions

* `Circuit.toDigraph` — the digraph associated to a circuit.

## Main results

* `Circuit.toDigraph_lt_of_adj` — along every edge `u → v`, `u.val < v.val`.
* `Circuit.toDigraph_acyclic` — the digraph is acyclic (from the `.val` order).
* `Circuit.toDigraph_edgeFinset_card_le` — the edge count is bounded by the
  total fan-in of all internal and output gates.

## Simple-graph caveat

`Digraph` is a *simple* digraph: parallel wires (e.g. `AND(x, x)`) collapse
to a single edge. This is fine for the averaging step of `depth_reduction`,
which only needs an upper bound on the edge count. It will matter again
when the `Σ₃` construction translates cut edges back to cut wires — there
each input position of each gate is a distinct wire, which is handled by
the fan-in-indexed sum, not by the digraph itself.
-/

namespace Circuit

variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- Adjacency predicate for the circuit digraph. Split out from
`toDigraph` so decidability can be derived by `unfold`-based inference. -/
def toDigraphAdj (c : Circuit B N M G) (u v : Fin (N + G + M)) : Prop :=
  (∃ i : Fin G, v.val = N + i.val ∧
    ∃ k : Fin (c.gates i).fanIn, ((c.gates i).inputs k).val = u.val) ∨
  (∃ j : Fin M, v.val = N + G + j.val ∧
    ∃ k : Fin (c.outputs j).fanIn, ((c.outputs j).inputs k).val = u.val)

instance (c : Circuit B N M G) (u v : Fin (N + G + M)) :
    Decidable (c.toDigraphAdj u v) := by
  unfold toDigraphAdj
  exact inferInstance

/-- The digraph associated to a circuit. An edge `u → v` exists iff
wire `u` is an input of the gate (internal or output) encoded by vertex
`v`. See the module docstring for the vertex encoding. -/
def toDigraph (c : Circuit B N M G) : Digraph (Fin (N + G + M)) where
  Adj := c.toDigraphAdj

instance (c : Circuit B N M G) : DecidableRel c.toDigraph.Adj := fun u v =>
  inferInstanceAs (Decidable (c.toDigraphAdj u v))

/-- Along every edge of the circuit digraph, the source's vertex index is
strictly less than the destination's. For edges into an internal gate this
is exactly the circuit's `acyclic` field; for edges into an output gate it
is `.val < N + G ≤ N + G + j.val`. -/
lemma toDigraph_lt_of_adj (c : Circuit B N M G)
    {u v : Fin (N + G + M)} (h : c.toDigraph.Adj u v) : u.val < v.val := by
  have h : c.toDigraphAdj u v := h
  rcases h with ⟨i, hv, k, hk⟩ | ⟨j, hv, k, hk⟩
  · have hacyc : ((c.gates i).inputs k).val < N + i.val := c.acyclic i k
    rw [← hk, hv]; exact hacyc
  · have hlt : ((c.outputs j).inputs k).val < N + G := ((c.outputs j).inputs k).isLt
    rw [← hk, hv]; omega

/-- Along a directed walk, `.val` is at least the walk index: the `k`-th
vertex has vertex index `≥ k`. Follows by induction on `k` using
`toDigraph_lt_of_adj`. -/
private lemma toDigraph_path_val_ge (c : Circuit B N M G)
    {m : ℕ} {p : Fin m → Fin (N + G + M)}
    (hp : c.toDigraph.IsDirectedPath p) :
    ∀ k : ℕ, (hk : k < m) → k ≤ (p ⟨k, hk⟩).val := by
  intro k
  induction k with
  | zero => intros; exact Nat.zero_le _
  | succ k ih =>
    intro hsk
    have hk : k < m := by omega
    have hadj : c.toDigraph.Adj (p ⟨k, hk⟩) (p ⟨k + 1, hsk⟩) := hp ⟨k, hk⟩ hsk
    have hvlt : (p ⟨k, hk⟩).val < (p ⟨k + 1, hsk⟩).val :=
      c.toDigraph_lt_of_adj hadj
    have hgek := ih hk
    omega

/-- The circuit digraph is acyclic: any directed walk has length at most
`N + G + M`, bounded by the number of vertices. -/
theorem toDigraph_acyclic (c : Circuit B N M G) :
    Digraph.IsAcyclic c.toDigraph := by
  refine ⟨N + G + M, ?_⟩
  rintro m ⟨p, hp⟩
  by_cases hm : m = 0
  · omega
  · have hm' : m - 1 < m := by omega
    have hge := c.toDigraph_path_val_ge hp (m - 1) hm'
    have hlt := (p ⟨m - 1, hm'⟩).isLt
    omega

/-- The circuit digraph's edge count is bounded by the total fan-in of
all gates (internal + output). Each directed edge `u → v` is witnessed by
some `(i, k)` or `(j, k)` pair — gate index + input position — and
different edges need different witnesses, so the cardinality of the
witness set (total fan-in) bounds the edge count.

The bound is strict whenever the circuit has parallel wires (two input
positions of the same gate reading from the same source): the simple
digraph collapses those, while the witness set counts them separately.
This only helps later bounds. -/
theorem toDigraph_edgeFinset_card_le (c : Circuit B N M G) :
    c.toDigraph.edgeFinset.card ≤
      (∑ i : Fin G, (c.gates i).fanIn) + (∑ j : Fin M, (c.outputs j).fanIn) := by
  -- Witness set: gate-input pairs for internal gates ⊕ for output gates.
  let D₁ : Type := Σ i : Fin G, Fin (c.gates i).fanIn
  let D₂ : Type := Σ j : Fin M, Fin (c.outputs j).fanIn
  let f : D₁ ⊕ D₂ → Fin (N + G + M) × Fin (N + G + M) := fun x =>
    match x with
    | Sum.inl ⟨i, k⟩ =>
        (⟨((c.gates i).inputs k).val, by
            have h1 := ((c.gates i).inputs k).isLt
            have h2 := i.isLt
            omega⟩,
         ⟨N + i.val, by have := i.isLt; omega⟩)
    | Sum.inr ⟨j, k⟩ =>
        (⟨((c.outputs j).inputs k).val, by
            have h1 := ((c.outputs j).inputs k).isLt
            have h2 := j.isLt
            omega⟩,
         ⟨N + G + j.val, by have := j.isLt; omega⟩)
  -- Every edge in the digraph is the image of some witness.
  have hcov : c.toDigraph.edgeFinset ⊆ (Finset.univ : Finset (D₁ ⊕ D₂)).image f := by
    intro e he
    rw [Digraph.mem_edgeFinset] at he
    have he' : c.toDigraphAdj e.1 e.2 := he
    rcases he' with ⟨i, hv, k, hk⟩ | ⟨j, hv, k, hk⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inl ⟨i, k⟩, Finset.mem_univ _,
          Prod.ext (Fin.ext hk) (Fin.ext hv.symm)⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inr ⟨j, k⟩, Finset.mem_univ _,
          Prod.ext (Fin.ext hk) (Fin.ext hv.symm)⟩
  calc c.toDigraph.edgeFinset.card
      ≤ ((Finset.univ : Finset (D₁ ⊕ D₂)).image f).card :=
        Finset.card_le_card hcov
    _ ≤ (Finset.univ : Finset (D₁ ⊕ D₂)).card := Finset.card_image_le
    _ = Fintype.card (D₁ ⊕ D₂) := Finset.card_univ
    _ = Fintype.card D₁ + Fintype.card D₂ := Fintype.card_sum
    _ = (∑ i : Fin G, (c.gates i).fanIn) + (∑ j : Fin M, (c.outputs j).fanIn) := by
        show Fintype.card (Σ i : Fin G, Fin (c.gates i).fanIn) +
              Fintype.card (Σ j : Fin M, Fin (c.outputs j).fanIn) = _
        rw [Fintype.card_sigma, Fintype.card_sigma]
        simp

end Circuit
