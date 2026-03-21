import Circ.Restriction
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset

/-! # Internal: Restriction Combinatorics

Combinatorial counting lemmas for sets of restrictions, used in the
switching lemma proof.

## Main results

* `sRestrictions_ratio_bound` — `|R^{s-d}| · N^d ≤ |R^s| · (4s)^d`
-/

open Classical

/-- Bijection between restrictions with free-variable set `S` and
Boolean functions on the complement of `S`. -/
private noncomputable def Restriction.fiberEquiv {N : Nat} (S : Finset (Fin N)) :
    {ρ : Restriction N // Restriction.freeVars ρ = S} ≃ ({i : Fin N // i ∉ S} → Bool) where
  toFun x := fun ⟨i, hi⟩ =>
    have : x.val i ≠ none := by
      intro heq
      exact hi (x.prop ▸ by simp [Restriction.freeVars, Restriction.isFree, heq])
    (x.val i).get (Option.ne_none_iff_isSome.mp this)
  invFun f := ⟨fun i => if h : i ∈ S then none else some (f ⟨i, h⟩), by
    ext i; simp only [Restriction.freeVars, Restriction.isFree,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ S <;> simp [hi]⟩
  left_inv := by
    intro ⟨ρ, hρ⟩; apply Subtype.ext; funext i
    by_cases h : ρ i = none
    · simp [show i ∈ S from by rw [← hρ]; simp [Restriction.freeVars, Restriction.isFree, h], h]
    · have : i ∉ S := by
        intro hi; rw [← hρ] at hi
        exact h (by simpa [Restriction.freeVars, Restriction.isFree] using hi)
      simp [this, Option.some_get]
  right_inv := by intro f; funext ⟨i, hi⟩; simp [hi]

/-- Each fiber `{ρ | freeVars ρ = S}` has exactly `2^(N - s)` elements
when `|S| = s`, since such a restriction is determined by its Boolean
values on the `N - s` non-free variables. -/
private lemma Restriction.fiber_card {N : Nat} (S : Finset (Fin N)) (hs : S.card = s) :
    (Finset.univ.filter (fun ρ : Restriction N => Restriction.freeVars ρ = S)).card =
    2 ^ (N - s) := by
  rw [show _ = Fintype.card {ρ : Restriction N // Restriction.freeVars ρ = S} from
    (Fintype.card_subtype _).symm,
    Fintype.card_congr (Restriction.fiberEquiv S), Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype_compl (· ∈ S), Fintype.card_coe, Fintype.card_fin]
  omega

/-- Cardinality of `sRestrictions`: the number of restrictions on `N` variables
with exactly `s` free variables is `C(N, s) · 2^{N-s}`. -/
private lemma sRestrictions_card (N s : Nat) (hs : s ≤ N) :
    (Restriction.sRestrictions N s).card = N.choose s * 2 ^ (N - s) := by
  have hbij : Restriction.sRestrictions N s =
      (Finset.powersetCard s Finset.univ).biUnion
        (fun S => Finset.univ.filter
          (fun ρ : Restriction N => Restriction.freeVars ρ = S)) := by
    ext ρ; simp only [Restriction.sRestrictions, Restriction.numFree, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨Restriction.freeVars ρ, ⟨Finset.subset_univ _, h⟩, rfl⟩,
      fun ⟨S, ⟨_, hcard⟩, hfv⟩ => hfv ▸ hcard⟩
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.powersetCard s (Finset.univ : Finset (Fin N))))
      (fun S => Finset.univ.filter
        (fun ρ : Restriction N => Restriction.freeVars ρ = S)) := by
    intro S _ T _ hST
    simp only [Finset.disjoint_filter, Finset.mem_univ, true_implies]
    intro ρ h1 h2; exact hST (h1 ▸ h2)
  rw [hbij, Finset.card_biUnion hdisj]
  rw [Finset.sum_congr rfl (fun S hS =>
    Restriction.fiber_card S (Finset.mem_powersetCard.mp hS).2)]
  rw [Finset.sum_const, Finset.card_powersetCard]
  simp [Fintype.card_fin]

/-- Core descending-factorial inequality:
  `s! / (s-d)! · (2N)^d ≤ (N-s+d)! / (N-s)! · (4s)^d`
when `d ≤ s` and `2s ≤ N`. Proved by induction on `d`. -/
private lemma descFactorial_mul_pow_le (s N : Nat) (h2sN : 2 * s ≤ N) :
    ∀ d, d ≤ s →
      s.descFactorial d * (2 * N) ^ d ≤
      (N - s + d).descFactorial d * (4 * s) ^ d := by
  intro d hds
  induction d with
  | zero => simp
  | succ d ih =>
    have ih' := ih (by omega : d ≤ s)
    rw [Nat.descFactorial_succ s d, Nat.descFactorial_succ (N - s + (d + 1)) d]
    have hnsub : N - s + (d + 1) - d = N - s + 1 := by omega
    rw [hnsub, pow_succ, pow_succ]
    have h_inner : s.descFactorial d * (2 * N) ^ d ≤
        (N - s + (d + 1)).descFactorial d * (4 * s) ^ d :=
      calc s.descFactorial d * (2 * N) ^ d
          ≤ (N - s + d).descFactorial d * (4 * s) ^ d := ih'
        _ ≤ (N - s + (d + 1)).descFactorial d * (4 * s) ^ d := by
            apply Nat.mul_le_mul_right
            exact Nat.descFactorial_le d (by omega)
    have h_factor : (s - d) * (2 * N) ≤ (N - s + 1) * (4 * s) :=
      calc (s - d) * (2 * N)
          ≤ s * (4 * (N - s + 1)) := Nat.mul_le_mul (by omega) (by omega)
        _ = (N - s + 1) * (4 * s) := by simp [mul_comm, mul_left_comm]
    calc (s - d) * s.descFactorial d * ((2 * N) ^ d * (2 * N))
        = (s - d) * (2 * N) * (s.descFactorial d * (2 * N) ^ d) := by
          simp [mul_comm, mul_assoc, mul_left_comm]
      _ ≤ (s - d) * (2 * N) * ((N - s + (d + 1)).descFactorial d * (4 * s) ^ d) :=
          Nat.mul_le_mul_left _ h_inner
      _ ≤ ((N - s + 1) * (4 * s)) * ((N - s + (d + 1)).descFactorial d * (4 * s) ^ d) :=
          Nat.mul_le_mul_right _ h_factor
      _ = (N - s + 1) * (N - s + (d + 1)).descFactorial d * ((4 * s) ^ d * (4 * s)) := by
          simp [mul_comm, mul_assoc, mul_left_comm]

/-- Combinatorial ratio bound for restriction sets.

The number of restrictions with `s - d` free variables times `N ^ d` is at most
the number with `s` free variables times `(4 · s) ^ d`. This follows from the
binomial coefficient identity

    C(N, s-d) · 2^{N-s+d} · N^d ≤ C(N, s) · 2^{N-s} · (4s)^d

which holds because `C(N, s-d) / C(N, s) ≤ (2s/N)^d` when `2s ≤ N`. -/
theorem sRestrictions_ratio_bound (N s d : Nat) (hds : d ≤ s) (h2sN : 2 * s ≤ N) :
    (Restriction.sRestrictions N (s - d)).card * N ^ d ≤
    (Restriction.sRestrictions N s).card * (4 * s) ^ d := by
  rw [sRestrictions_card N (s - d) (by omega), sRestrictions_card N s (by omega)]
  suffices h : N.choose (s - d) * (2 * N) ^ d ≤ N.choose s * (4 * s) ^ d by
    have h_exp : N - (s - d) = N - s + d := by omega
    rw [h_exp, pow_add]
    calc N.choose (s - d) * (2 ^ (N - s) * 2 ^ d) * N ^ d
        = 2 ^ (N - s) * (N.choose (s - d) * (2 ^ d * N ^ d)) := by
          simp [mul_comm, mul_assoc, mul_left_comm]
      _ = 2 ^ (N - s) * (N.choose (s - d) * (2 * N) ^ d) := by
          rw [← mul_pow]
      _ ≤ 2 ^ (N - s) * (N.choose s * (4 * s) ^ d) :=
          Nat.mul_le_mul_left _ h
      _ = N.choose s * 2 ^ (N - s) * (4 * s) ^ d := by
          simp [mul_comm, mul_assoc, mul_left_comm]
  have h_desc := descFactorial_mul_pow_le s N h2sN d hds
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h_desc
  have h_choose : s.choose d * (2 * N) ^ d ≤ (N - s + d).choose d * (4 * s) ^ d := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos d)
    simp only [mul_assoc] at h_desc ⊢; exact h_desc
  have h_id : N.choose s * s.choose d = N.choose (s - d) * (N - s + d).choose d := by
    have h1 := Nat.choose_mul (show s - d ≤ s from Nat.sub_le s d) (n := N)
    rw [Nat.choose_symm hds, show N - (s - d) = N - s + d from by omega,
        show s - (s - d) = d from by omega] at h1
    exact h1
  suffices (N - s + d).choose d * (N.choose (s - d) * (2 * N) ^ d) ≤
      (N - s + d).choose d * (N.choose s * (4 * s) ^ d) from
    Nat.le_of_mul_le_mul_left this (Nat.choose_pos (by omega))
  calc (N - s + d).choose d * (N.choose (s - d) * (2 * N) ^ d)
      = N.choose (s - d) * (N - s + d).choose d * (2 * N) ^ d := by
        simp [mul_comm, mul_assoc, mul_left_comm]
    _ = N.choose s * s.choose d * (2 * N) ^ d := by rw [← h_id]
    _ = N.choose s * (s.choose d * (2 * N) ^ d) := by
        simp [mul_assoc]
    _ ≤ N.choose s * ((N - s + d).choose d * (4 * s) ^ d) :=
        Nat.mul_le_mul_left _ h_choose
    _ = (N - s + d).choose d * (N.choose s * (4 * s) ^ d) := by
        simp [mul_comm, mul_left_comm]
