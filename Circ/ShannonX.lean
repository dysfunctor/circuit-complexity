import Circ.Internal.BridgeX

/-! # Shannon Counting Lower Bound (AND/OR/NOT/XOR Basis)

For `N ≥ 6`, there exists a Boolean function on `N` inputs that cannot be
computed by any fan-in-2 AND/OR/NOT/XOR circuit with fewer than `2^N / (5N)`
gates.

This extends `shannon_lower_bound_circuit` (which targets the AND/OR basis)
to the richer AND/OR/NOT/XOR basis. The proof uses the same pigeonhole
counting strategy: even with 4 gate types (AND, OR, NOT, XOR) and per-input
negation flags, the number of circuits of bounded size remains smaller than
the number of Boolean functions.

## Main results

* `shannon_lower_bound_circuit_x` — existence of a hard function for the
  AND/OR/NOT/XOR basis.
* `shannon_size_complexity_x` — the same bound stated in terms of
  `Circuit.size_complexity` (requires `CompleteBasis Basis.andOrNotXor2`).
-/

/-- **Shannon lower bound for AND/OR/NOT/XOR in terms of `size_complexity`**:
    for `N ≥ 6`, there exists a Boolean function whose fan-in-2
    AND/OR/NOT/XOR circuit complexity exceeds `2^N / (5N)`. -/
theorem shannon_size_complexity_x (N : Nat) [NeZero N] (hN : 6 ≤ N)
    [CompleteBasis Basis.andOrNotXor2] :
    ∃ f : BitString N → Bool,
      Circuit.size_complexity Basis.andOrNotXor2 f > 2 ^ N / (5 * N) := by
  obtain ⟨f, hf⟩ := shannon_lower_bound_circuit_x N hN
  refine ⟨f, ?_⟩
  by_contra hle; push_neg at hle
  obtain ⟨G, c, hs, hc⟩ := Circuit.size_complexity_witness (B := Basis.andOrNotXor2) f
  have : c.size ≤ 2 ^ N / (5 * N) := hs ▸ hle
  exact hf G c (by rw [Circuit.size] at this; omega) hc
