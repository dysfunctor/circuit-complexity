import Circ.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-! # Depth lemmas

Shared depth-related lemmas extracted for reuse across the depth/reachability
infrastructure. All are consequences of the `1 + Fin.foldl max` shape of
`Circuit.wireDepth` on gates and `Circuit.outputDepth` on outputs.

## Main results

* `Circuit.wireDepth_input_lt` — a gate's input wire has strictly smaller
  `wireDepth` than the gate itself.
* `Circuit.wireDepth_output_input_lt` — an output gate's input wire has
  strictly smaller `wireDepth` than the output's `outputDepth`.
* `Circuit.outputDepth_le_depth` — every output's `outputDepth` is at
  most the circuit's `depth`.

These were originally inlined in `Circ/Valiant/Prune.lean`; moving them
here lets both `Prune.lean` and `Circ/ReachableInputs.lean` share the
machinery without duplication.
-/

/-! ### `Fin.foldl`-with-`max` helpers

These are the workhorse lemmas: `Fin.foldl` with body `(fun acc k => max acc (f k))`
is an upper bound both on the initial accumulator and on every `f k`.
Public so downstream files (notably `Circ/Valiant/CutReachable.lean`) can
reuse them for analogous `1 + Fin.foldl max` definitions. -/

lemma Circuit.fin_foldl_max_ge_init :
    ∀ {n : ℕ} (f : Fin n → ℕ) (acc₀ : ℕ),
      acc₀ ≤ Fin.foldl n (fun acc k => max acc (f k)) acc₀ := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n' ih =>
    intro f acc₀
    rw [Fin.foldl_succ]
    calc acc₀
        ≤ max acc₀ (f 0) := le_max_left _ _
      _ ≤ Fin.foldl n' (fun acc k => max acc (f k.succ)) (max acc₀ (f 0)) :=
            ih (fun k => f k.succ) (max acc₀ (f 0))

/-- `Fin.foldl` with `(max _ (f _))` is at most any joint upper bound of
the initial accumulator and the function `f`. Combined with
`fin_foldl_max_ge` this pins the fold value to the `Finset.sup`. -/
lemma Circuit.fin_foldl_max_le_ub :
    ∀ {n : ℕ} (f : Fin n → ℕ) (acc₀ B : ℕ),
      acc₀ ≤ B → (∀ k, f k ≤ B) →
      Fin.foldl n (fun acc k => max acc (f k)) acc₀ ≤ B := by
  intro n
  induction n with
  | zero => intros f acc₀ _ hinit _; simpa using hinit
  | succ n' ih =>
    intro f acc₀ B hinit h
    rw [Fin.foldl_succ]
    exact ih (fun k => f k.succ) (max acc₀ (f 0)) B (max_le hinit (h 0))
      (fun k => h k.succ)

lemma Circuit.fin_foldl_max_ge :
    ∀ {n : ℕ} (f : Fin n → ℕ) (acc₀ : ℕ) (k : Fin n),
      f k ≤ Fin.foldl n (fun acc k' => max acc (f k')) acc₀ := by
  intro n
  induction n with
  | zero => intros _ _ k; exact k.elim0
  | succ n' ih =>
    intro f acc₀ k
    rw [Fin.foldl_succ]
    by_cases hk : k = 0
    · subst hk
      calc f 0
          ≤ max acc₀ (f 0) := le_max_right _ _
        _ ≤ Fin.foldl n' (fun acc k' => max acc (f k'.succ)) (max acc₀ (f 0)) :=
              Circuit.fin_foldl_max_ge_init (fun k' => f k'.succ) (max acc₀ (f 0))
    · obtain ⟨k', rfl⟩ : ∃ k' : Fin n', k = k'.succ :=
        ⟨k.pred hk, (Fin.succ_pred k hk).symm⟩
      exact ih (fun j => f j.succ) (max acc₀ (f 0)) k'

namespace Circuit

variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- A gate input's `wireDepth` is strictly less than the gate's own
`wireDepth`: the gate's depth is `1 + max` over its inputs. -/
lemma wireDepth_input_lt (c : Circuit B N M G) (i : Fin G)
    (k : Fin (c.gates i).fanIn) :
    c.wireDepth ((c.gates i).inputs k) <
    c.wireDepth ⟨N + i.val, by have := i.isLt; omega⟩ := by
  have hne : ¬ (⟨N + i.val, by have := i.isLt; omega⟩ : Fin (N + G)).val < N := by
    show ¬ (N + i.val) < N; omega
  rw [c.gateWireDepth _ hne]
  have heq :
      (⟨(⟨N + i.val, by have := i.isLt; omega⟩ : Fin (N + G)).val - N,
        by
          have := (⟨N + i.val, by have := i.isLt; omega⟩ : Fin (N + G)).isLt
          omega⟩ : Fin G) = i := by
    apply Fin.ext
    show (N + i.val) - N = i.val
    omega
  rw [heq]
  have hge :=
    Circuit.fin_foldl_max_ge (fun k' => c.wireDepth ((c.gates i).inputs k')) 0 k
  omega

/-- A gate input's `wireDepth` is strictly less than the `outputDepth`
of the output gate it feeds. -/
lemma wireDepth_output_input_lt (c : Circuit B N M G) (j : Fin M)
    (k : Fin (c.outputs j).fanIn) :
    c.wireDepth ((c.outputs j).inputs k) < c.outputDepth j := by
  show c.wireDepth ((c.outputs j).inputs k) < 1 + _
  have hge :=
    Circuit.fin_foldl_max_ge (fun k' => c.wireDepth ((c.outputs j).inputs k')) 0 k
  omega

/-- Every output gate's `outputDepth` is at most the circuit's `depth`. -/
lemma outputDepth_le_depth (c : Circuit B N M G) (j : Fin M) :
    c.outputDepth j ≤ c.depth := by
  have := Circuit.fin_foldl_max_ge (fun j' => c.outputDepth j') 0 j
  show c.outputDepth j ≤ Fin.foldl M _ 0
  exact this

end Circuit
