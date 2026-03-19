import Circ.AC0.Defs
import Circ.Internal.NF
import Mathlib.Data.List.Dedup
import Mathlib.Data.Fintype.Prod

/-! # Internal: AC0 Proof Machinery

Gate and circuit deduplication for unbounded-fan-in AND/OR circuits,
used to prove that AC0 implies AC0NF.

## Main results

* `Gate.dedup` — remove duplicate (wire, polarity) pairs from a gate
* `Gate.dedup_eval` — deduplication preserves gate evaluation
* `Gate.dedup_fanIn_le` — deduped fan-in ≤ 2 * W
* `Gate.dedup_inputs_mem` — every deduped input was an original input
* `Circuit.dedup` — deduplicate all gates in a circuit
* `Circuit.dedup_eval` — deduplication preserves circuit evaluation
* `Circuit.dedup_depth_le` — depth does not increase
* `Circuit.dedup_maxFanIn_le` — maxFanIn ≤ 2 * (N + G)
* `InAC0_implies_InAC0NF` — AC0 ⊆ AC0NF
* `not_InAC0NF_implies_not_InAC0` — contrapositive for lower bounds
-/

/-! ## Gate deduplication

Remove duplicate `(input wire, negation flag)` pairs from unbounded-fan-in
AND/OR gates. Since AND and OR are idempotent, this preserves gate semantics
while bounding fan-in by `2 * W` (the number of distinct wire–polarity pairs). -/

namespace Gate

/-- Remove duplicate (input wire, negation flag) pairs from an unbounded-AON gate. -/
def dedup (g : Gate Basis.unboundedAON W) : Gate Basis.unboundedAON W :=
  let pairs := (List.ofFn (fun k : Fin g.fanIn => (g.inputs k, g.negated k))).dedup
  { op := g.op
    fanIn := pairs.length
    arityOk := by rcases g.op <;> trivial
    inputs := fun k => (pairs.get k).1
    negated := fun k => (pairs.get k).2 }

/-- Every input of the deduped gate was an input of the original gate. -/
theorem dedup_inputs_mem (g : Gate Basis.unboundedAON W) (j : Fin g.dedup.fanIn) :
    ∃ k : Fin g.fanIn, g.dedup.inputs j = g.inputs k ∧
      g.dedup.negated j = g.negated k := by
  simp only [dedup]
  set pairs := (List.ofFn (fun k : Fin g.fanIn => (g.inputs k, g.negated k))).dedup
  have hmem : pairs.get j ∈ List.ofFn (fun k : Fin g.fanIn => (g.inputs k, g.negated k)) :=
    List.mem_dedup.mp (List.get_mem pairs j)
  rw [List.mem_ofFn] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, congr_arg Prod.fst hk.symm, congr_arg Prod.snd hk.symm⟩

private theorem foldl_and_init (n : Nat) (f : Fin n → Bool) (a : Bool) :
    Fin.foldl n (fun acc k => acc && f k) a =
    (a && Fin.foldl n (fun acc k => acc && f k) true) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.true_and]
    rw [ih (fun k => f k.succ) (a && f 0)]
    rw [ih (fun k => f k.succ) (f 0)]
    simp [Bool.and_assoc]

private theorem foldl_or_init (n : Nat) (f : Fin n → Bool) (a : Bool) :
    Fin.foldl n (fun acc k => acc || f k) a =
    (a || Fin.foldl n (fun acc k => acc || f k) false) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.false_or]
    rw [ih (fun k => f k.succ) (a || f 0)]
    rw [ih (fun k => f k.succ) (f 0)]
    simp [Bool.or_assoc]

private theorem foldl_and_true_iff (n : Nat) (f : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc && f i) true = true) ↔ ∀ i, f i = true := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Bool.true_and, foldl_and_init, Bool.and_eq_true, ih]
    constructor
    · intro ⟨h0, hall⟩ i; exact Fin.cases h0 hall i
    · intro h; exact ⟨h 0, fun j => h j.succ⟩

private theorem foldl_or_true_iff (n : Nat) (f : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc || f i) false = true) ↔ ∃ i, f i = true := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Bool.false_or, foldl_or_init, Bool.or_eq_true, ih]
    constructor
    · rintro (h0 | ⟨j, hj⟩)
      · exact ⟨0, h0⟩
      · exact ⟨j.succ, hj⟩
    · intro ⟨i, hi⟩
      obtain ⟨_ | m, hlt⟩ := i
      · exact .inl hi
      · exact .inr ⟨⟨m, by omega⟩, hi⟩

/-- Deduplication preserves gate evaluation. -/
theorem dedup_eval (g : Gate Basis.unboundedAON W) (wireVal : BitString W) :
    g.dedup.eval wireVal = g.eval wireVal := by
  simp only [Gate.eval, Basis.unboundedAON, dedup]
  set origPairs := List.ofFn (fun k : Fin g.fanIn => (g.inputs k, g.negated k))
  set pairs := origPairs.dedup
  rw [Bool.eq_iff_iff]
  cases g.op <;> simp only [AONOp.eval]
  · -- AND: both true iff every input bit is true
    rw [foldl_and_true_iff, foldl_and_true_iff]
    constructor
    · -- dedup all-true → original all-true
      intro h k
      have hmem : (g.inputs k, g.negated k) ∈ pairs :=
        List.mem_dedup.mpr (List.mem_ofFn.mpr ⟨k, rfl⟩)
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
      have hval := h j; rw [hj] at hval; exact hval
    · -- original all-true → dedup all-true
      intro h j
      have hmem : pairs.get j ∈ origPairs :=
        List.mem_dedup.mp (List.get_mem pairs j)
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hmem
      rw [← congr_arg Prod.fst hk, ← congr_arg Prod.snd hk]
      exact h k
  · -- OR: both true iff some input bit is true
    rw [foldl_or_true_iff, foldl_or_true_iff]
    constructor
    · rintro ⟨j, hj⟩
      have hmem : pairs.get j ∈ origPairs :=
        List.mem_dedup.mp (List.get_mem pairs j)
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hmem
      refine ⟨k, ?_⟩
      rw [← congr_arg Prod.fst hk, ← congr_arg Prod.snd hk] at hj
      exact hj
    · rintro ⟨k, hk⟩
      have hmem : (g.inputs k, g.negated k) ∈ pairs :=
        List.mem_dedup.mpr (List.mem_ofFn.mpr ⟨k, rfl⟩)
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
      refine ⟨j, ?_⟩
      rw [← congr_arg Prod.fst hj.symm, ← congr_arg Prod.snd hj.symm]
      exact hk

/-- The fan-in of a deduped gate is at most `2 * W` (number of wire–polarity pairs). -/
theorem dedup_fanIn_le (g : Gate Basis.unboundedAON W) :
    g.dedup.fanIn ≤ 2 * W := by
  show (List.ofFn (fun k : Fin g.fanIn => (g.inputs k, g.negated k))).dedup.length ≤ 2 * W
  have hnd := List.nodup_dedup (List.ofFn (fun k : Fin g.fanIn => (g.inputs k, g.negated k)))
  calc (List.ofFn _).dedup.length
      ≤ Fintype.card (Fin W × Bool) := hnd.length_le_card
    _ = 2 * W := by simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; omega

end Gate

/-! ## Circuit deduplication -/

namespace Circuit
variable {N G : Nat} [NeZero N]

/-- Deduplicate all gates in a circuit, preserving acyclicity. -/
def dedup (c : Circuit Basis.unboundedAON N 1 G) : Circuit Basis.unboundedAON N 1 G where
  gates i := (c.gates i).dedup
  outputs j := (c.outputs j).dedup
  acyclic i k := by
    obtain ⟨k', hk', _⟩ := Gate.dedup_inputs_mem (c.gates i) k
    rw [hk']
    exact c.acyclic i k'

/-- Gate evaluation depends only on the wire values at the gate's inputs. -/
private theorem Gate.eval_congr {B : Basis} {W : Nat} (g : Gate B W)
    (wv1 wv2 : BitString W) (h : ∀ k : Fin g.fanIn, wv1 (g.inputs k) = wv2 (g.inputs k)) :
    g.eval wv1 = g.eval wv2 := by
  simp only [Gate.eval]; congr 1; funext i; congr 1; exact h i

/-- Deduplication preserves wire values. -/
theorem dedup_wireValue (c : Circuit Basis.unboundedAON N 1 G) (input : BitString N)
    (w : Fin (N + G)) : c.dedup.wireValue input w = c.wireValue input w := by
  by_cases hw : w.val < N
  · simp [wireValue_lt, hw]
  · have hG : w.val - N < G := by omega
    rw [wireValue_ge c.dedup input w hw, wireValue_ge c input w hw]
    change (c.gates ⟨w.val - N, hG⟩).dedup.eval (c.dedup.wireValue input) = _
    rw [Gate.dedup_eval]
    exact Gate.eval_congr (c.gates ⟨w.val - N, hG⟩) _ _ fun k =>
      dedup_wireValue c input ((c.gates ⟨w.val - N, hG⟩).inputs k)
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Deduplication preserves circuit evaluation. -/
theorem dedup_eval (c : Circuit Basis.unboundedAON N 1 G) :
    c.dedup.eval = c.eval := by
  funext input j
  simp only [Circuit.eval]
  have hwv : c.dedup.wireValue input = c.wireValue input :=
    funext (dedup_wireValue c input)
  show (c.outputs j).dedup.eval (c.dedup.wireValue input) = (c.outputs j).eval (c.wireValue input)
  rw [Gate.dedup_eval, hwv]

/-- `Fin.foldl` with `max` satisfies the init-extraction property. -/
private theorem foldl_max_init' (n : Nat) (f : Fin n → Nat) (a : Nat) :
    Fin.foldl n (fun acc k => max acc (f k)) a =
    max a (Fin.foldl n (fun acc k => max acc (f k)) 0) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Nat.zero_max]
    rw [ih (fun k => f k.succ) (max a (f 0))]
    rw [ih (fun k => f k.succ) (f 0)]
    simp [Nat.max_assoc]

/-- Max of a `Fin.foldl` with `max` is bounded when every element is bounded. -/
private theorem foldl_max_le_bound (n : Nat) (f : Fin n → Nat) (bound : Nat)
    (h : ∀ i, f i ≤ bound) :
    Fin.foldl n (fun acc i => max acc (f i)) 0 ≤ bound := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Nat.zero_max, foldl_max_init']
    exact Nat.max_le.mpr ⟨h 0, ih (fun k => f k.succ) (fun k => h k.succ)⟩

/-- An element is ≤ the `Fin.foldl` max. -/
private theorem le_foldl_max (n : Nat) (f : Fin n → Nat) (i : Fin n) :
    f i ≤ Fin.foldl n (fun acc k => max acc (f k)) 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [Fin.foldl_succ, Nat.zero_max, foldl_max_init']
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih (fun k => f k.succ) j) (Nat.le_max_right _ _)

/-- Wire depth does not increase after deduplication. -/
theorem dedup_wireDepth_le (c : Circuit Basis.unboundedAON N 1 G) (w : Fin (N + G)) :
    c.dedup.wireDepth w ≤ c.wireDepth w := by
  by_cases hw : w.val < N
  · simp [wireDepth_lt, hw]
  · have hG : w.val - N < G := by omega
    rw [wireDepth_ge c.dedup w hw, wireDepth_ge c w hw]
    apply Nat.add_le_add_left
    apply foldl_max_le_bound
    intro k
    obtain ⟨k', hk', _⟩ := Gate.dedup_inputs_mem (c.gates ⟨w.val - N, hG⟩) k
    calc c.dedup.wireDepth ((c.gates ⟨w.val - N, hG⟩).dedup.inputs k)
        ≤ c.wireDepth ((c.gates ⟨w.val - N, hG⟩).dedup.inputs k) :=
          dedup_wireDepth_le c _
      _ = c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k') := by rw [hk']
      _ ≤ Fin.foldl _ (fun acc k => max acc (c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k))) 0 :=
          le_foldl_max _ (fun k => c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k)) k'
termination_by w.val
decreasing_by
  obtain ⟨k', hk'i, _⟩ := Gate.dedup_inputs_mem (c.gates ⟨w.val - N, hG⟩) k
  simp only [Circuit.dedup] at *
  rw [hk'i]
  have := c.acyclic ⟨w.val - N, hG⟩ k'
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Circuit depth does not increase after deduplication. -/
theorem dedup_depth_le (c : Circuit Basis.unboundedAON N 1 G) :
    c.dedup.depth ≤ c.depth := by
  simp only [Circuit.depth]
  apply Nat.add_le_add_left
  apply foldl_max_le_bound
  intro k
  obtain ⟨k', hk', _⟩ := Gate.dedup_inputs_mem (c.outputs 0) k
  calc c.dedup.wireDepth ((c.outputs 0).dedup.inputs k)
      ≤ c.wireDepth ((c.outputs 0).dedup.inputs k) := dedup_wireDepth_le c _
    _ = c.wireDepth ((c.outputs 0).inputs k') := by rw [hk']
    _ ≤ _ := le_foldl_max _ (fun k => c.wireDepth ((c.outputs 0).inputs k)) k'

/-- MaxFanIn of deduped circuit is at most `2 * (N + G)`. -/
theorem dedup_maxFanIn_le (c : Circuit Basis.unboundedAON N 1 G) :
    c.dedup.maxFanIn ≤ 2 * (N + G) := by
  simp only [Circuit.maxFanIn]
  apply Nat.max_le.mpr
  constructor
  · apply foldl_max_le_bound
    intro i; exact Gate.dedup_fanIn_le (c.gates i)
  · exact Gate.dedup_fanIn_le (c.outputs 0)

end Circuit

/-! ## AC0 → AC0NF -/

private theorem pow_mul_pow_le_pow_add {N c d : Nat} (hN : 2 ≤ N) :
    (2 * (N + N ^ c)) ^ d ≤ N ^ ((c + 3) * d) := by
  suffices h : 2 * (N + N ^ c) ≤ N ^ (c + 3) by
    calc (2 * (N + N ^ c)) ^ d ≤ (N ^ (c + 3)) ^ d := Nat.pow_le_pow_left h d
      _ = N ^ ((c + 3) * d) := by rw [Nat.pow_mul]
  have hN_pos : 0 < N := by omega
  have h1 : N ≤ N ^ (c + 1) := by
    calc N = N ^ 1 := (Nat.pow_one N).symm
      _ ≤ N ^ (c + 1) := Nat.pow_le_pow_right hN_pos (by omega)
  have h4 : 4 ≤ N ^ 2 := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
  have h2 : N ^ c ≤ N ^ (c + 1) := Nat.pow_le_pow_right hN_pos (by omega)
  calc 2 * (N + N ^ c)
      ≤ 2 * (2 * N ^ (c + 1)) := by omega
    _ = 4 * N ^ (c + 1) := by omega
    _ ≤ N ^ 2 * N ^ (c + 1) := Nat.mul_le_mul_right _ h4
    _ = N ^ (c + 3) := by rw [← Nat.pow_add]; congr 1; omega

/-- For `N = 1`, every function on 1 bit has an ACNF with leaf count ≤ 1. -/
private def acnfOneBit (f : BitString 1 → Bool) : (b : Bool) × ACNF 1 b :=
  match f (fun _ => true), f (fun _ => false) with
  | true, true => ⟨true, .and []⟩
  | false, false => ⟨false, .or []⟩
  | true, false => ⟨true, .lit ⟨0, true⟩⟩
  | false, true => ⟨false, .lit ⟨0, false⟩⟩

private theorem acnfOneBit_eval (f : BitString 1 → Bool) :
    (acnfOneBit f).2.eval = f := by
  have hbs : ∀ x : BitString 1, x = fun _ => x 0 :=
    fun x => funext fun ⟨0, _⟩ => rfl
  funext x; rw [hbs x]
  simp only [acnfOneBit]
  cases hT : f (fun _ => true) <;> cases hF : f (fun _ => false) <;>
    simp [ACNF.eval, ACNF.eval.evalAll, ACNF.eval.evalAny, Literal.eval] <;>
    cases x 0 <;> simp_all

private theorem acnfOneBit_depth_le (f : BitString 1 → Bool) :
    (acnfOneBit f).2.depth ≤ 1 := by
  simp only [acnfOneBit]
  cases f (fun _ => true) <;> cases f (fun _ => false) <;>
    simp [ACNF.depth, ACNF.depth.depthAll, ACNF.depth.depthAny]

private theorem acnfOneBit_leafCount_le (f : BitString 1 → Bool) :
    (acnfOneBit f).2.leafCount ≤ 1 := by
  simp only [acnfOneBit]
  cases f (fun _ => true) <;> cases f (fun _ => false) <;>
    simp [ACNF.leafCount, ACNF.leafCount.leafCountAll, ACNF.leafCount.leafCountAny]

/-- Every AC0 function family is also in AC0NF. -/
theorem InAC0_implies_InAC0NF (f : BoolFunFamily) : InAC0 f → InAC0NF f := by
  intro ⟨d, c, hf⟩
  refine ⟨d, (c + 3) * d, fun N inst => ?_⟩
  obtain ⟨G, circ, hdepth, hsize, heval⟩ := @hf N inst
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hN1 : N = 1
  · -- N = 1: construct ACNF directly (circuit approach gives leafCount > 1^c')
    subst hN1
    exact ⟨(acnfOneBit (f 1)).1, (acnfOneBit (f 1)).2,
      Nat.le_trans (acnfOneBit_depth_le _)
        (by have : circ.depth ≤ d := hdepth; simp [Circuit.depth] at this; omega),
      by simp [acnfOneBit_leafCount_le],
      acnfOneBit_eval _⟩
  · -- N ≥ 2: dedup the circuit, then convert to ACNF
    have hN2 : 2 ≤ N := by omega
    set circ' := circ.dedup
    have hG_le : G ≤ N ^ c := by have := hsize; simp [Circuit.size] at this; omega
    use circ'.toACNF.1, circ'.toACNF.2
    refine ⟨?depth, ?leafCount, ?eval⟩
    case eval =>
      funext x
      rw [Circuit.toACNF_eval, congr_fun (congr_fun circ.dedup_eval x) 0]
      exact congr_fun heval x
    case depth =>
      exact Nat.le_trans (Circuit.toACNF_depth_le circ') (Nat.le_trans circ.dedup_depth_le hdepth)
    case leafCount =>
      calc circ'.toACNF.2.leafCount
          ≤ circ'.maxFanIn ^ circ'.depth := Circuit.toACNF_leafCount_le circ'
        _ ≤ (2 * (N + G)) ^ circ'.depth := by
            exact Nat.pow_le_pow_left circ.dedup_maxFanIn_le _
        _ ≤ (2 * (N + G)) ^ d := by
            apply Nat.pow_le_pow_right (by omega)
            exact Nat.le_trans circ.dedup_depth_le hdepth
        _ ≤ (2 * (N + N ^ c)) ^ d := by
            apply Nat.pow_le_pow_left
            exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hG_le _)
        _ ≤ N ^ ((c + 3) * d) := pow_mul_pow_le_pow_add (hN := hN2)

/-- Contrapositive: a function not in AC0NF is not in AC0. -/
theorem not_InAC0NF_implies_not_InAC0 (f : BoolFunFamily) : ¬InAC0NF f → ¬InAC0 f :=
  fun h => h ∘ InAC0_implies_InAC0NF f
