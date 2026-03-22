import Circ.AC0.Defs
import Circ.Internal.AC0
import Circ.Internal.RestrictionCombinatorics
import Circ.XOR
import Circ.Restriction

/-! # AC0 — The AC0 Complexity Class

This module re-exports the AC0 definitions and main results.

## Definitions (from `Circ.AC0.Defs`)

* `BoolFunFamily` — a family of Boolean functions indexed by input length
* `InAC0` — predicate: the family is in AC0 (constant depth, polynomial size,
  unbounded fan-in AND/OR)
* `InAC0NFTree` — predicate: the family is computed by constant-depth,
  polynomial-leaf-count ACNF trees

## Main results (from `Circ.Internal.AC0`)

* `Gate.dedup` / `Circuit.dedup` — gate and circuit deduplication
* `Circuit.dedup_eval` — deduplication preserves evaluation
* `Circuit.dedup_depth_le` — depth does not increase after deduplication
* `Circuit.dedup_maxFanIn_le` — maxFanIn ≤ 2 * (N + G) after deduplication
* `InAC0_implies_InAC0NFTree` — every AC0 family is in AC0NFTree
* `not_InAC0NFTree_implies_not_InAC0` — contrapositive for lower bounds
* `parity_not_in_AC0` — the parity function is not in AC0
-/

/-- The parity (XOR) function family: the `N`-input XOR for each input length. -/
def parityFamily : BoolFunFamily := fun N => Schnorr.xorBool N

/-- **Parity is not in AC0** (Furst–Saxe–Sipser / Håstad).

The N-input XOR function cannot be computed by any constant-depth,
polynomial-size family of unbounded-fan-in AND/OR circuits. -/
theorem parity_not_in_AC0 : ¬InAC0 parityFamily :=
  not_InAC0NFTree_implies_not_InAC0 _ parity_not_in_AC0NFTree

/-! ## Switching Lemma -/

open Classical

/-- **Razborov's Lemma** (Razborov, 1995).

If `φ` is a CNF formula on `N` variables with clause width `φ.width`,
then the number of restrictions in `R^s` (leaving exactly `s` free variables)
whose restricted function has a minterm longer than `d` satisfies:

    |Bad_φ(s, d)| ≤ |R^{s-d}| · (2 · width)^d

This is the key combinatorial counting lemma underlying the switching lemma.
The proof proceeds by an encoding/decoding (compression) argument: each "bad"
restriction `ρ` (with `s` free variables and `maxMintermLength > d`) can be
encoded as a pair `(γ, advice)` where `γ` has `s - d` free variables and
`advice ∈ {0, …, 2w-1}^d`, and this encoding is injective. -/
theorem razborov_lemma {N : Nat} (φ : CNF N) (s d : Nat) :
    ((Restriction.sRestrictions N s).filter (fun ρ =>
      Restriction.maxMintermLength (ρ.restrict φ.eval) > d)).card ≤
    (Restriction.sRestrictions N (s - d)).card * (2 * φ.width) ^ d := by
  sorry

/-- **Switching Lemma** (Håstad, 1986).

Let `φ` be a CNF formula on `N` variables with clause width `φ.width`.
Among all restrictions leaving exactly `s` free variables, the number
whose restricted function has a minterm longer than `d` satisfies:

    |{ρ | numFree ρ = s ∧ maxMintermLength(φ|_ρ) > d}| · N ^ d
      ≤ |{ρ | numFree ρ = s}| · (8 · width · s) ^ d

This is the counting (set-size) form of the probabilistic statement
`Prob[min(f_ρ) > d] ≤ (8pt)^d` with `p = s / N`.

Follows from `razborov_lemma` (the counting bound) and `sRestrictions_ratio_bound`
(the combinatorial ratio bound on restriction set sizes). -/
theorem switching_lemma {N : Nat} (φ : CNF N) (s d : Nat)
    (hds : d ≤ s) (h2sN : 2 * s ≤ N) :
    ((Restriction.sRestrictions N s).filter (fun ρ =>
      Restriction.maxMintermLength (ρ.restrict φ.eval) > d)).card * N ^ d ≤
    (Restriction.sRestrictions N s).card * (8 * φ.width * s) ^ d := by
  calc ((Restriction.sRestrictions N s).filter (fun ρ =>
          Restriction.maxMintermLength (ρ.restrict φ.eval) > d)).card * N ^ d
      ≤ (Restriction.sRestrictions N (s - d)).card * (2 * φ.width) ^ d * N ^ d :=
          Nat.mul_le_mul_right _ (razborov_lemma φ s d)
    _ = (Restriction.sRestrictions N (s - d)).card * N ^ d * (2 * φ.width) ^ d := by
          rw [mul_right_comm]
    _ ≤ (Restriction.sRestrictions N s).card * (4 * s) ^ d * (2 * φ.width) ^ d :=
          Nat.mul_le_mul_right _ (sRestrictions_ratio_bound N s d hds h2sN)
    _ = (Restriction.sRestrictions N s).card * (8 * φ.width * s) ^ d := by
          rw [mul_assoc, ← mul_pow]
          simp [mul_comm, mul_assoc, mul_left_comm]
