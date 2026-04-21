import Circ.AON.Defs
import Circ.NF.Defs
import Circ.Valiant
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-! # Lemma 11.1 (Valiant 1983): NC¹_lin implies small Σ₃ complexity

If a Boolean function family is in the class `NC¹_lin` of log-depth,
linear-size fan-in-2 circuits, then its Σ₃ complexity — the smallest
number of CNFs (each with at most `2 ^ (n ^ ε)` clauses) needed to
represent it as a real-valued sum — satisfies
`log Σ₃(f_n) = O(n / log log n)`.

This is an important conditional statement: a super-linear lower bound on
`log Σ₃(f_n)` for an explicit `f` would give the first super-linear lower
bound on log-depth fan-in-2 circuits, resolving a long-standing open
problem (Jukna, *Boolean Function Complexity*, §11).

## Main definitions

* `InNC1Lin` — the class `NC¹_lin` of log-depth, linear-size fan-in-2
  AND/OR circuits. Any Boolean function of at most two variables is
  computable by a depth-`O(1)`, size-`O(1)` fan-in-2 AND/OR/NOT formula,
  so this is the same class (up to constants) as the textbook
  "binary circuit" formulation.
* `Sigma3Rep` — a "sum-of-CNFs" representation of a Boolean function.
* `Sigma3` — the size of the smallest such representation.

## Main statement

* `Valiant.log_sigma3_isBigO` — Lemma 11.1: for `f ∈ NC¹_lin` and `ε > 0`,
  `N ↦ log Σ₃_ε(f_N)` is `O(N / log log N)`.
-/

/-! ### The class NC¹_lin -/

/-- A Boolean function family is in **NC¹_lin** if there exist constants
`c₁, c₂` such that for every input length `N ≥ 1`, some fan-in-2 AND/OR
circuit (with free negation) of depth at most `c₁ · log₂ N + c₁` and size
at most `c₂ · N + c₂` computes `f N`.

Jukna's textbook formulation allows any 2-input Boolean function as a
gate; since every such function has a constant-size fan-in-2 AND/OR/NOT
formula, the two formulations define the same class up to constants in
`c₁` and `c₂`. -/
def InNC1Lin (f : BoolFunFamily) : Prop :=
  ∃ c₁ c₂ : Nat, ∀ (N : Nat) [NeZero N],
    ∃ (G : Nat) (c : Circuit Basis.andOr2 N 1 G),
      c.depth ≤ c₁ * Nat.log 2 N + c₁ ∧
      c.size ≤ c₂ * N + c₂ ∧
      (fun x => (c.eval x) 0) = f N

/-! ### The Σ₃ complexity measure -/

/-- A **Σ₃-representation** of a Boolean function `f : BitString N → Bool`
with clause-size parameter `ε > 0`: a collection of `t` CNFs, each with at
most `2 ^ (N ^ ε)` clauses, whose `0/1` values in `ℕ` sum to `f(x)` for
every input `x`.

Summing in `ℕ` enforces both correctness and the Σ₃ middle-layer
restriction (at most one CNF — i.e. one middle-layer AND gate — fires on
any input). Without this restriction the measure would collapse to
ordinary Σ₃-formula size. -/
structure Sigma3Rep (N : Nat) (ε : ℝ) (f : BitString N → Bool) where
  t : Nat
  cnfs : Fin t → CNF N
  clause_bound : ∀ i, ((cnfs i).complexity : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) ^ ε)
  correctness : ∀ x : BitString N,
    (∑ i : Fin t, ((cnfs i).eval x).toNat) = (f x).toNat

/-- **Σ₃(f)**: the smallest number of CNFs in any Σ₃-representation of
`f` with clause-size parameter `ε`. Returns `0` if no such representation
exists (by the Nat `sInf` convention). -/
noncomputable def Sigma3 {N : Nat} (ε : ℝ) (f : BitString N → Bool) : ℕ :=
  sInf {t | ∃ rep : Sigma3Rep N ε f, rep.t = t}

/-! ### Lemma 11.1 statement -/

open Asymptotics Filter

/-- **Lemma 11.1** (Valiant, 1983). If `f ∈ NC¹_lin` then
`log Σ₃(f_n) = O(n / log log n)`.

Formally: for every `ε > 0`, `N ↦ log Σ₃_ε(f_N)` is `O(N / log log N)`
as `N → ∞`. The implied `O`-constant depends on `f` and `ε`.

The proof (not formalized here) applies Valiant's depth-reduction lemma
(`Valiant.depth_reduction`) to a log-depth, linear-size circuit for `f_n`:
removing a small number of wires splits the circuit into subcircuits of
depth at most `ε log n`, each of which computes a function of at most
`2 ^ (ε log n) = n ^ ε` inputs — small enough to flatten into a CNF with
at most `2 ^ (n ^ ε)` clauses. The number of such subcircuit choices is
bounded by `2 ^ O(n / log log n)`. -/
theorem Valiant.log_sigma3_isBigO
    {f : BoolFunFamily} (hf : InNC1Lin f) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => Real.log ((Sigma3 ε (f N) : ℕ) : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / Real.log (Real.log N)) := by
  sorry
