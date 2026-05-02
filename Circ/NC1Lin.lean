import Circ.AON.Defs
import Circ.NF.Defs
import Circ.Valiant
import Circ.Valiant.Prune
import Circ.Valiant.Sigma3Build
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Archimedean

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
`c₁` and `c₂`.

The additive `+ c₁`, `+ c₂` handle small `N` cleanly: for `N = 1`,
`log₂ 1 = 0` but a circuit still has depth ≥ 1, and the additive term
absorbs this slack without affecting the `O(log N)`, `O(N)` asymptotics. -/
def InNC1Lin (f : BoolFunFamily) : Prop :=
  ∃ c₁ c₂ : Nat, ∀ (N : Nat) [NeZero N],
    ∃ (G : Nat) (c : Circuit Basis.andOr2 N 1 G),
      c.depth ≤ c₁ * Nat.log2 N + c₁ ∧
      c.size ≤ c₂ * N + c₂ ∧
      (fun x => (c.eval x) 0) = f N

/-! ### The Σ₃ complexity measure -/

/-- A **Σ₃-representation** of a Boolean function `f : BitString N → Bool`
with clause-size parameter `ε > 0`: a collection of `t` CNFs, each with at
most `2 ^ (N ^ ε)` clauses, whose values — viewed as `0` or `1` in `ℕ` —
sum to `f(x)` for every input `x`.

The `sum = f(x)` condition simultaneously enforces two properties:

* **Correctness**: exactly one CNF evaluates to `1` when `f(x) = 1`, and
  none when `f(x) = 0`.
* **Middle-layer restriction**: at most one CNF outputs `1` on any input
  — equivalently, at most one "AND gate" on the middle layer of the
  corresponding Σ₃-circuit fires. (This restriction is what makes
  `Σ₃(f_n)` a meaningful measure: without it, the top `OR` gate would
  make this just the `Σ₃`-formula size in the unrestricted sense.)

Because we work over `ℕ`, the sum enforces both facts: `sum x ∈ {0, 1}`
implies no two CNFs can be simultaneously `1`. -/
structure Sigma3Rep (N : Nat) (ε : ℝ) (f : BitString N → Bool) where
  t : Nat
  cnfs : Fin t → CNF N
  clause_bound : ∀ i, ((cnfs i).complexity : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) ^ ε)
  correctness : ∀ x : BitString N,
    (∑ i : Fin t, (if (cnfs i).eval x then 1 else 0 : ℕ)) =
      (if f x then 1 else 0)

/-- **Σ₃(f)**: the smallest number of CNFs in any Σ₃-representation of
`f` with clause-size parameter `ε`. Returns `0` if no such representation
exists (by the Nat `sInf` convention). -/
noncomputable def Sigma3 {N : Nat} (ε : ℝ) (f : BitString N → Bool) : ℕ :=
  sInf {t | ∃ rep : Sigma3Rep N ε f, rep.t = t}

/-! ### Packaging cuts as a Σ₃-representation -/

/-- **Sigma3Rep from a cut-edge family.** Given a fan-in-2 single-output
circuit `c` and a cut-edge set `F` (with sources in the wire range)
together with a per-α clause-count bound, the family `{ψ_α}_α : ↥F → Bool`
is a `Sigma3Rep` of `(fun x => (c.eval x) 0)`. -/
noncomputable def Sigma3RepFromCutCircuit
    {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G)
    (F : Finset (Fin (N + G + 1) × Fin (N + G + 1)))
    (hF : ∀ e ∈ F, e.1.val < N + G)
    {ε : ℝ}
    (h_clause : ∀ α : ↥F → Bool,
      ((c.psiCNF F α 0 hF).complexity : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) ^ ε)) :
    Sigma3Rep N ε (fun x => (c.eval x) 0) where
  t := Fintype.card (↥F → Bool)
  cnfs := fun i => c.psiCNF F ((Fintype.equivFin (↥F → Bool)).symm i) 0 hF
  clause_bound := fun _ => h_clause _
  correctness := fun x =>
    (Equiv.sum_comp (Fintype.equivFin (↥F → Bool)).symm _).trans
      (c.sum_psiCNF_eval_eq F 0 hF x)

/-- `Sigma3 ε f ≤ 2 ^ |F|` whenever a cut-edge set `F` yields a per-α
clause-count bound — i.e., the Σ₃ representation built from `{ψ_α}` has
size `2^|F|`. -/
theorem Sigma3_le_pow_card
    {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G)
    (F : Finset (Fin (N + G + 1) × Fin (N + G + 1)))
    (hF : ∀ e ∈ F, e.1.val < N + G)
    {ε : ℝ}
    (h_clause : ∀ α : ↥F → Bool,
      ((c.psiCNF F α 0 hF).complexity : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) ^ ε)) :
    Sigma3 ε (fun x => (c.eval x) 0) ≤ 2 ^ F.card := by
  unfold Sigma3
  apply Nat.sInf_le
  refine ⟨Sigma3RepFromCutCircuit c F hF h_clause, ?_⟩
  show Fintype.card (↥F → Bool) = 2 ^ F.card
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-! ### Lemma 11.1 statement -/

open Asymptotics Filter

set_option maxHeartbeats 490000 in
/-- **Heart of Lemma 11.1.** For `f ∈ NC¹_lin` and `ε > 0`, there is a
constant `K > 0` such that for all sufficiently large `N`,
`Sigma3 ε (f N) ≤ 2 ^ (K · N / log log N)`.

The proof has three asymptotic ingredients:

1. **Parameter selection.** Given `c : Circuit Basis.andOr2 N 1 G` from
   `hf` with `c.depth ≤ c₁ · log₂ N + c₁` and `c.size ≤ c₂ N + c₂`:
   * `k_N := max(Nat.log2(depth_p+1)+1, Nat.log2(Nat.log2 N)+1)`, ensuring
     `k_N ≥ Ω(log log N)` uniformly.
   * `r_N := r₀` (constant in N), chosen so that `2^r₀ ≥ 8(c₁+1)/ε`.

2. **Application of `Valiant.depth_reduction`.** Yields `F_N` with:
   * `k_N · |F_N| ≤ r₀ · S_N` where `S_N ≤ 2(c₂+1)(N+1)` (fan-in-2).
   * `(deleteEdges F_N).depth ≤ 2^(k_N - r₀)`.

3. **Per-α clause-count bound + count bound.** Combine
   `psiCNF_complexity_le` with the depth bound to get `≤ 2^(N^ε)` per α
   (asymptotic). Combine `k_N · F.card ≤ r₀ · S` with
   `Real.log(Real.log N) ≤ (k_N + 1) · Real.log 2` to get
   `F.card · log(log N) ≤ K · N`.

Combine via `Sigma3_le_pow_card`: `Sigma3 ≤ 2^|F_N|`, with `|F_N| ≤ K ·
N / log log N`. Set `K := 4(c₂+1) · log 2 · (r₀+1) + 1`. -/
private lemma sigma3_le_pow_K_N_log_log_N
    {f : BoolFunFamily} (hf : InNC1Lin f) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ((Sigma3 ε (f N) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (K * (N : ℝ) / Real.log (Real.log N)) ∧
      Nonempty (Sigma3Rep N ε (f N)) := by
  obtain ⟨c₁, c₂, hf_circuit⟩ := hf
  obtain ⟨r₀, hr₀⟩ : ∃ r : ℕ, (16 * (c₁ + 1) : ℝ) / ε ≤ 2 ^ r :=
    let ⟨r, hr⟩ := pow_unbounded_of_one_lt _ one_lt_two
    ⟨r, hr.le⟩
  obtain ⟨ε_inv, hε_inv⟩ : ∃ n : ℕ, 1 / ε ≤ (n : ℝ) := exists_nat_ge _
  set K : ℝ := 4 * (c₂ + 1) * Real.log 2 * (r₀ + 1) + 1 with hK_def
  set M_F : ℕ := 2 * r₀ * (c₂ + 1) + 1 with hM_F_def
  have hPolyEvent : ∀ᶠ N : ℕ in Filter.atTop,
      (M_F : ℝ) * ((N : ℝ) + 1) ≤ (2 : ℝ) ^ ((N : ℝ) ^ (ε / 4)) := by
    have hε4 : (0 : ℝ) < ε / 4 := by linarith
    have h_log_o : (fun N : ℕ => Real.log ((N : ℝ)))
        =o[Filter.atTop] (fun N : ℕ => (N : ℝ) ^ (ε / 4)) :=
      (isLittleO_log_rpow_atTop hε4).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have h_log2_4_pos : (0 : ℝ) < Real.log 2 / 4 := by linarith
    have h_eventual_log := (Asymptotics.isLittleO_iff.mp h_log_o) h_log2_4_pos
    have h_pow_tend_atTop : Filter.Tendsto
        (fun N : ℕ => (Real.log 2 / 4) * (N : ℝ) ^ (ε / 4))
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop h_log2_4_pos
        ((tendsto_rpow_atTop hε4).comp tendsto_natCast_atTop_atTop)
    have h_const_event : ∀ᶠ N : ℕ in Filter.atTop,
        Real.log (M_F : ℝ) + Real.log 2 + 1 ≤ (Real.log 2 / 4) * (N : ℝ) ^ (ε / 4) :=
      h_pow_tend_atTop.eventually_ge_atTop _
    filter_upwards [h_eventual_log, h_const_event,
      Filter.eventually_ge_atTop (1 : ℕ)]
      with N h_log_le h_const_le hN1
    have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN_pos_R : (0 : ℝ) < (N : ℝ) := by linarith
    have h_M_F_pos_R : (0 : ℝ) < (M_F : ℝ) := by positivity
    have h_N1_pos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have h_pow_nn : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 4) := Real.rpow_nonneg hN_pos_R.le _
    have h_logN_bound : Real.log (N : ℝ) ≤ (Real.log 2 / 4) * (N : ℝ) ^ (ε / 4) := by
      have h_logN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN_real
      simpa [Real.norm_eq_abs, abs_of_nonneg h_logN_nn, abs_of_nonneg h_pow_nn]
        using h_log_le
    have h_logN1 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log (N : ℝ) := by
      rw [← Real.log_mul (by norm_num) hN_pos_R.ne']
      exact Real.log_le_log h_N1_pos (add_one_le_two_mul hN_real)
    have h_log_MN1 : Real.log ((M_F : ℝ) * ((N : ℝ) + 1)) ≤
        (Real.log 2 / 2) * (N : ℝ) ^ (ε / 4) := by
      rw [Real.log_mul h_M_F_pos_R.ne' h_N1_pos.ne']
      linarith [h_logN1, h_const_le, h_logN_bound]
    have h_MN1_pos : (0 : ℝ) < (M_F : ℝ) * ((N : ℝ) + 1) := by positivity
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((N : ℝ) ^ (ε / 4)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [← Real.log_le_log_iff h_MN1_pos h_pow_pos, Real.log_rpow (by norm_num)]
    nlinarith [h_log_MN1, h_pow_nn, h_log2_pos.le]
  refine ⟨K, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (16 : ℕ),
    Filter.eventually_ge_atTop (2 ^ (2 ^ r₀ * (ε_inv + 1) + 1)),
    Filter.eventually_ge_atTop (2 ^ (8 * ε_inv + 1)),
    hPolyEvent]
    with N hN_ge_16 hN_shallow hN_eps_inv hPoly
  have hN_pos : 0 < N := by omega
  haveI : NeZero N := ⟨Nat.ne_of_gt hN_pos⟩
  obtain ⟨G, c, hd_le, hs_le, hf_eq⟩ := hf_circuit N
  have hf_eq' : (fun x => (c.prune.eval x) 0) = f N := by
    rw [c.prune_eval_eq]; exact hf_eq
  set depth_p : ℕ := c.prune.toDigraph.depth
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hN_pos_R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN_real_ge : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_16
  have h_logN_gt_1 : (1 : ℝ) < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hN_pos_R).mpr (by linarith [Real.exp_one_lt_three])
  have h_logN_pos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  have h_loglogN_pos : (0 : ℝ) < Real.log (Real.log N) := Real.log_pos h_logN_gt_1
  have h_log2N_ge_1 : 1 ≤ Nat.log2 N :=
    (Nat.le_log2 (by omega : N ≠ 0)).mpr (by show (2 : ℕ) ≤ N; omega)
  by_cases h_deep : 2 ^ r₀ ≤ depth_p + 1
  · -- ### Deep regime: depth_p + 1 ≥ 2^r₀.
    -- For the count bound, we need k_N to grow as Ω(log log N). Take
    -- `k_N := max(Nat.log2(depth_p+1)+1, Nat.log2(Nat.log2 N)+1)`. Both
    -- choices give 2^k_N ≥ depth_p (the precondition) AND k_N ≥ r₀ in the
    -- deep regime (large enough N), AND k_N ≥ Nat.log2(Nat.log2 N) ≈ log log N.
    set k_N : ℕ := max (Nat.log2 (depth_p + 1) + 1) (Nat.log2 (Nat.log2 N) + 1)
    have h_r_le_k : r₀ ≤ k_N := by
      have : r₀ ≤ Nat.log2 (depth_p + 1) := (Nat.le_log2 (by omega)).mpr h_deep
      exact (Nat.le_succ_of_le this).trans (le_max_left _ _)
    have h_2k_ge : depth_p ≤ 2 ^ k_N := by
      have h_pow_le : 2 ^ (Nat.log2 (depth_p + 1) + 1) ≤ 2 ^ k_N :=
        Nat.pow_le_pow_right (by decide) (le_max_left _ _)
      have := (@Nat.lt_log2_self (depth_p + 1)).trans_le h_pow_le
      omega
    obtain ⟨F, hF_sub, hF_card_ineq, hF_depth⟩ :=
      Valiant.depth_reduction c.prune.toDigraph (k := k_N) (r := r₀) h_r_le_k h_2k_ge
    have hF_src : ∀ e ∈ F, e.1.val < N + c.reachableGates.card := by
      intro e he
      rcases (Digraph.mem_edgeFinset.mp (hF_sub he) : c.prune.toDigraphAdj e.1 e.2) with
        ⟨i, _, k', hk'⟩ | ⟨j, _, k', hk'⟩
      · have := ((c.prune.gates i).inputs k').isLt; omega
      · have := ((c.prune.outputs j).inputs k').isLt; omega
    have hSize_le : c.prune.size ≤ c.size := c.prune_size_le
    have hS_le : c.prune.toDigraph.edgeFinset.card ≤ 2 * c.prune.size := by
      have h1 := c.prune.toDigraph_edgeFinset_card_le
      simp only [andOr2_fanIn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul] at h1
      show c.prune.toDigraph.edgeFinset.card ≤ 2 * (c.reachableGates.card + 1)
      omega
    have hS_le_N : c.prune.toDigraph.edgeFinset.card ≤ 2 * (c₂ * N + c₂) :=
      hS_le.trans (by omega)
    have h_clause : ∀ α : ↥F → Bool,
        ((c.prune.psiCNF F α 0 hF_src).complexity : ℝ) ≤
          (2 : ℝ) ^ ((N : ℝ) ^ ε) := by
      intro α
      set d := (c.prune.toDigraph.deleteEdges F).depth
      have h_psi_le : (c.prune.psiCNF F α 0 hF_src).complexity ≤
          (F.card + 1) * 2 ^ (2 ^ (d + 1)) :=
        c.prune.psiCNF_complexity_le F α 0 hF_src
      have h_dp_le : depth_p + 1 ≤ c₁ * Nat.log2 N + c₁ + 2 := by
        have h_pdg : c.prune.toDigraph.depth ≤ c.depth + 1 :=
          c.prune_toDigraph_depth_le
        omega
      have h_log2_succ_pow : ∀ (m : ℕ), m ≠ 0 →
          (2 : ℕ) ^ (Nat.log2 m + 1) ≤ 2 * m := fun m hm => by
        rw [pow_succ]; linarith [Nat.log2_self_le hm]
      have h_2kN_le_nat : (2 : ℕ) ^ k_N ≤ 2 * (c₁ + 1) * (Nat.log2 N + 1) := by
        rcases le_total (Nat.log2 (depth_p + 1) + 1) (Nat.log2 (Nat.log2 N) + 1) with h | h
        · rw [show k_N = Nat.log2 (Nat.log2 N) + 1 from max_eq_right h]
          calc (2 : ℕ) ^ (Nat.log2 (Nat.log2 N) + 1)
              ≤ 2 * Nat.log2 N := h_log2_succ_pow _ (by omega)
            _ ≤ 2 * (c₁ + 1) * (Nat.log2 N + 1) := by linarith [h_log2N_ge_1]
        · rw [show k_N = Nat.log2 (depth_p + 1) + 1 from max_eq_left h]
          calc (2 : ℕ) ^ (Nat.log2 (depth_p + 1) + 1)
              ≤ 2 * (depth_p + 1) := h_log2_succ_pow _ (by omega)
            _ ≤ 2 * (c₁ + 1) * (Nat.log2 N + 1) := by linarith [h_dp_le, h_log2N_ge_1]
      have h_2kN_le_real : ((2 ^ k_N : ℕ) : ℝ) ≤
          2 * ((c₁ : ℝ) + 1) * ((Nat.log2 N : ℝ) + 1) := by
        exact_mod_cast h_2kN_le_nat
      have h_pow_split : (2 : ℕ) ^ (k_N - r₀) * 2 ^ r₀ = 2 ^ k_N :=
        pow_sub_mul_pow 2 h_r_le_k
      have h_d_le : (d : ℝ) ≤ ((2 ^ (k_N - r₀) : ℕ) : ℝ) := by
        exact_mod_cast hF_depth.trans_eq (Nat.pow_div h_r_le_k (by decide))
      have h_pow_split_real : ((2 ^ (k_N - r₀) : ℕ) : ℝ) * ((2 ^ r₀ : ℕ) : ℝ) ≤
          2 * ((c₁ : ℝ) + 1) * ((Nat.log2 N : ℝ) + 1) := by
        rw [← Nat.cast_mul, h_pow_split]; exact h_2kN_le_real
      have h_2r0_ge : (16 * ((c₁ : ℝ) + 1)) / ε ≤ ((2 ^ r₀ : ℕ) : ℝ) := by
        push_cast; exact hr₀
      have h_d_le_real : (d : ℝ) ≤ ε * ((Nat.log2 N : ℝ) + 1) / 8 := by
        have h_pkr_nn : (0 : ℝ) ≤ ((2 ^ (k_N - r₀) : ℕ) : ℝ) := by positivity
        have h_step : ((2 ^ (k_N - r₀) : ℕ) : ℝ) * ((16 * ((c₁ : ℝ) + 1)) / ε) ≤
            2 * ((c₁ : ℝ) + 1) * ((Nat.log2 N : ℝ) + 1) :=
          (mul_le_mul_of_nonneg_left h_2r0_ge h_pkr_nn).trans h_pow_split_real
        have h_pkr_le_div : ((2 ^ (k_N - r₀) : ℕ) : ℝ) ≤
            ε * ((Nat.log2 N : ℝ) + 1) / 8 := by
          rw [show ε * ((Nat.log2 N : ℝ) + 1) / 8 =
              (2 * ((c₁ : ℝ) + 1) * ((Nat.log2 N : ℝ) + 1)) /
                ((16 * ((c₁ : ℝ) + 1)) / ε) by field_simp; ring]
          rw [le_div_iff₀ (by positivity)]
          linarith
        exact h_d_le.trans h_pkr_le_div
      have h_log2N_ge_eps : (Nat.log2 N : ℝ) ≥ 8 * (ε_inv : ℝ) + 1 := by
        have : 8 * ε_inv + 1 ≤ Nat.log2 N := (Nat.le_log2 (by omega)).mpr hN_eps_inv
        exact_mod_cast this
      have h_8_inv : 8 / ε ≤ 8 * (ε_inv : ℝ) := by
        rw [show (8 : ℝ) / ε = 8 * (1 / ε) from by ring]; gcongr
      have h_d1_le_real : ((d : ℝ) + 1) ≤ ε * (Nat.log2 N : ℝ) / 4 := by
        have h_nl_ge : (8 : ℝ) / ε ≤ (Nat.log2 N : ℝ) - 1 := by linarith
        have h_eN_ge : (8 : ℝ) ≤ ε * ((Nat.log2 N : ℝ) - 1) := by
          rw [mul_comm]; exact (div_le_iff₀ hε).mp h_nl_ge
        linarith
      have h_log2N_le_real : (Nat.log2 N : ℝ) ≤ Real.log N / Real.log 2 := by
        simpa [Real.logb] using Real.log2_le_logb N
      have h_2_d1_le : (2 : ℝ) ^ ((d : ℝ) + 1) ≤ (N : ℝ) ^ (ε / 4) := by
        have h_exp_le : ε * (Nat.log2 N : ℝ) / 4 ≤ ε * (Real.log N / Real.log 2) / 4 := by
          linarith [mul_le_mul_of_nonneg_left h_log2N_le_real hε.le]
        calc (2 : ℝ) ^ ((d : ℝ) + 1)
            ≤ (2 : ℝ) ^ (ε * (Nat.log2 N : ℝ) / 4) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) h_d1_le_real
          _ ≤ (2 : ℝ) ^ (ε * (Real.log N / Real.log 2) / 4) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp_le
          _ = (N : ℝ) ^ (ε / 4) := by
              rw [show ε * (Real.log N / Real.log 2) / 4 = Real.logb 2 N * (ε / 4) by
                    simp [Real.logb]; ring,
                  Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
                  Real.rpow_logb (by norm_num) (by norm_num) hN_pos_R]
      have h_2pow_2pow_le : (((2 : ℕ) ^ (2 ^ (d + 1)) : ℕ) : ℝ) ≤
          (2 : ℝ) ^ ((N : ℝ) ^ (ε / 4)) := by
        push_cast [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h_2_d1_le
      have h_F1_real : ((F.card + 1 : ℕ) : ℝ) ≤ (M_F : ℝ) * ((N : ℝ) + 1) := by
        have h_kN_pos : 0 < k_N := (Nat.succ_pos _).trans_le (le_max_right _ _)
        have h_F_card : F.card ≤ r₀ * (2 * (c₂ * N + c₂)) :=
          (Nat.le_mul_of_pos_left _ h_kN_pos).trans
            (hF_card_ineq.trans (Nat.mul_le_mul_left _ hS_le_N))
        have : F.card + 1 ≤ M_F * (N + 1) := by nlinarith
        exact_mod_cast this
      have h_2_eps4_le : 2 * (N : ℝ) ^ (ε / 4) ≤ (N : ℝ) ^ ε := by
        have h_logN_ge : Real.log (N : ℝ) ≥ ((Nat.log2 N : ℝ)) * Real.log 2 :=
          (le_div_iff₀ h_log2_pos).mp h_log2N_le_real
        have h_step1 : Real.log 2 ≤ (3 * ε / 4) * Real.log (N : ℝ) := by
          have h_3eps_nn : (0 : ℝ) ≤ 3 * ε / 4 := by linarith
          have h_eps_einv : 1 ≤ ε * ε_inv := by
            rw [mul_comm]; exact (div_le_iff₀ hε).mp hε_inv
          have h_factor : (1 : ℝ) ≤ (3 * ε / 4) * (Nat.log2 N : ℝ) := by
            have := mul_le_mul_of_nonneg_left h_log2N_ge_eps h_3eps_nn
            nlinarith [h_eps_einv]
          calc Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
            _ ≤ ((3 * ε / 4) * (Nat.log2 N : ℝ)) * Real.log 2 :=
                mul_le_mul_of_nonneg_right h_factor h_log2_pos.le
            _ ≤ (3 * ε / 4) * Real.log N := by
                rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h_logN_ge h_3eps_nn
        have h_2_le : (2 : ℝ) ≤ (N : ℝ) ^ (3 * ε / 4) :=
          Real.le_rpow_of_log_le hN_pos_R h_step1
        have h_split : (N : ℝ) ^ ε = (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (3 * ε / 4) := by
          rw [← Real.rpow_add hN_pos_R]; congr 1; ring
        rw [h_split]
        have h_pow_nn : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 4) := Real.rpow_nonneg hN_pos_R.le _
        calc 2 * (N : ℝ) ^ (ε / 4) = (N : ℝ) ^ (ε / 4) * 2 := by ring
          _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (3 * ε / 4) :=
              mul_le_mul_of_nonneg_left h_2_le h_pow_nn
      calc ((c.prune.psiCNF F α 0 hF_src).complexity : ℝ)
          ≤ ((F.card + 1 : ℕ) : ℝ) * (((2 : ℕ) ^ (2 ^ (d + 1)) : ℕ) : ℝ) := by
            exact_mod_cast h_psi_le
        _ ≤ ((M_F : ℝ) * ((N : ℝ) + 1)) * (2 : ℝ) ^ ((N : ℝ) ^ (ε / 4)) := by
            gcongr
        _ ≤ (2 : ℝ) ^ ((N : ℝ) ^ (ε / 4)) * (2 : ℝ) ^ ((N : ℝ) ^ (ε / 4)) := by
            gcongr
        _ = (2 : ℝ) ^ (2 * (N : ℝ) ^ (ε / 4)) := by
            rw [← Real.rpow_add (by norm_num)]; ring_nf
        _ ≤ (2 : ℝ) ^ ((N : ℝ) ^ ε) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h_2_eps4_le
    have h_sigma3 : Sigma3 ε (fun x => (c.prune.eval x) 0) ≤ 2 ^ F.card :=
      Sigma3_le_pow_card c.prune F hF_src h_clause
    rw [hf_eq'] at h_sigma3
    have h_F_card_bound : (F.card : ℝ) ≤ K * (N : ℝ) / Real.log (Real.log N) := by
      have hF_card_real : (F.card : ℝ) * (k_N : ℝ) ≤ 2 * r₀ * (c₂ + 1) * (N + 1) := by
        have h_nat : F.card * k_N ≤ r₀ * (2 * (c₂ * N + c₂)) := by
          rw [mul_comm]; exact hF_card_ineq.trans (Nat.mul_le_mul_left _ hS_le_N)
        have : ((F.card * k_N : ℕ) : ℝ) ≤ ((r₀ * (2 * (c₂ * N + c₂)) : ℕ) : ℝ) := by
          exact_mod_cast h_nat
        push_cast at this; nlinarith
      have h_M_pos_real : (1 : ℝ) ≤ (Nat.log2 N : ℝ) := by
        exact_mod_cast h_log2N_ge_1
      have h_log_lt_log2_succ : ∀ (m : ℕ), 0 < (m : ℝ) →
          Real.log (m : ℝ) < ((Nat.log2 m : ℝ) + 1) * Real.log 2 := fun m hm => by
        have h2 := Real.log_lt_log hm
          (by exact_mod_cast @Nat.lt_log2_self m : (m : ℝ) < (2 : ℝ) ^ (Nat.log2 m + 1))
        rw [Real.log_pow] at h2; push_cast at h2; linarith
      have h_kN_ge_real : ((Nat.log2 (Nat.log2 N) : ℝ) + 2) ≤ ((k_N : ℝ) + 1) := by
        have : (Nat.log2 (Nat.log2 N) : ℝ) + 1 ≤ (k_N : ℝ) := by exact_mod_cast le_max_right _ _
        linarith
      have h_loglogN_le_kN : Real.log (Real.log N) ≤ ((k_N : ℝ) + 1) * Real.log 2 := by
        have h_2M_log2 : Real.log N ≤ 2 * (Nat.log2 N : ℝ) * Real.log 2 := by
          linarith [h_log_lt_log2_succ N hN_pos_R,
            mul_le_mul_of_nonneg_right (add_one_le_two_mul h_M_pos_real) h_log2_pos.le]
        have h_log_log2_nonpos : Real.log (Real.log 2) ≤ 0 :=
          Real.log_nonpos h_log2_pos.le (by linarith [Real.log_two_lt_d9])
        calc Real.log (Real.log N)
            ≤ Real.log (2 * (Nat.log2 N : ℝ) * Real.log 2) :=
              Real.log_le_log h_logN_pos h_2M_log2
          _ = Real.log 2 + Real.log (Nat.log2 N : ℝ) + Real.log (Real.log 2) := by
              rw [Real.log_mul (by positivity) h_log2_pos.ne',
                  Real.log_mul (by norm_num) (by linarith)]
          _ ≤ ((Nat.log2 (Nat.log2 N) : ℝ) + 2) * Real.log 2 := by
              linarith [h_log_lt_log2_succ (Nat.log2 N) (by linarith)]
          _ ≤ ((k_N : ℝ) + 1) * Real.log 2 :=
              mul_le_mul_of_nonneg_right h_kN_ge_real h_log2_pos.le
      have hF_card_real_le : (F.card : ℝ) ≤ 2 * ((c₂ : ℝ) + 1) * ((N : ℝ) + 1) := by
        have h : ((F.card : ℕ) : ℝ) ≤ ((2 * (c₂ * N + c₂) : ℕ) : ℝ) := by
          exact_mod_cast (Finset.card_le_card hF_sub).trans hS_le_N
        push_cast at h
        linarith
      have h_F_card_nn : (0 : ℝ) ≤ F.card := by positivity
      have h_NP1_le : ((N : ℝ) + 1) ≤ 2 * (N : ℝ) := add_one_le_two_mul (by linarith)
      have h_K_factor : 4 * ((c₂ : ℝ) + 1) * Real.log 2 * ((r₀ : ℝ) + 1) ≤ K := by
        linarith
      have hF_loglog_le : (F.card : ℝ) * Real.log (Real.log N) ≤ K * (N : ℝ) :=
        calc (F.card : ℝ) * Real.log (Real.log N)
            ≤ (F.card : ℝ) * (((k_N : ℝ) + 1) * Real.log 2) :=
              mul_le_mul_of_nonneg_left h_loglogN_le_kN h_F_card_nn
          _ = ((F.card : ℝ) * (k_N : ℝ) + (F.card : ℝ)) * Real.log 2 := by ring
          _ ≤ (2 * (r₀ : ℝ) * ((c₂ : ℝ) + 1) * ((N : ℝ) + 1) +
                2 * ((c₂ : ℝ) + 1) * ((N : ℝ) + 1)) * Real.log 2 :=
              mul_le_mul_of_nonneg_right (add_le_add hF_card_real hF_card_real_le)
                h_log2_pos.le
          _ = 2 * ((c₂ : ℝ) + 1) * ((r₀ : ℝ) + 1) * ((N : ℝ) + 1) * Real.log 2 := by ring
          _ ≤ 2 * ((c₂ : ℝ) + 1) * ((r₀ : ℝ) + 1) * (2 * (N : ℝ)) * Real.log 2 := by
              gcongr
          _ = (4 * ((c₂ : ℝ) + 1) * Real.log 2 * ((r₀ : ℝ) + 1)) * (N : ℝ) := by ring
          _ ≤ K * (N : ℝ) :=
              mul_le_mul_of_nonneg_right h_K_factor (by linarith)
      rw [le_div_iff₀ h_loglogN_pos]
      linarith [hF_loglog_le]
    refine ⟨?_, ?_⟩
    · calc ((Sigma3 ε (f N) : ℕ) : ℝ)
          ≤ ((2 ^ F.card : ℕ) : ℝ) := by exact_mod_cast h_sigma3
        _ = (2 : ℝ) ^ (F.card : ℝ) := by norm_cast
        _ ≤ (2 : ℝ) ^ (K * (N : ℝ) / Real.log (Real.log N)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h_F_card_bound
    · rw [← hf_eq']
      exact ⟨Sigma3RepFromCutCircuit c.prune F hF_src h_clause⟩
  · -- ### Shallow regime: depth_p + 1 < 2^r₀.
    push_neg at h_deep
    let F : Finset (Fin (N + c.reachableGates.card + 1) ×
        Fin (N + c.reachableGates.card + 1)) := ∅
    have hF_src : ∀ e ∈ F, e.1.val < N + c.reachableGates.card := by
      intro e he; exact absurd he (Finset.notMem_empty _)
    -- Per-α bound for F = ∅: outputCNF ≤ 2^(2^(depth_p+1)) ≤ 2^(2^(2^r₀)) ≤ 2^(N^ε).
    have h_clause : ∀ α : ↥F → Bool,
        ((c.prune.psiCNF F α 0 hF_src).complexity : ℝ) ≤
          (2 : ℝ) ^ ((N : ℝ) ^ ε) := by
      intro α
      have h_psi_le_nat : (c.prune.psiCNF F α 0 hF_src).complexity ≤
          2 ^ (2 ^ (depth_p + 1)) := by
        have h1 := c.prune.psiCNF_complexity_le F α 0 hF_src
        rw [Valiant.deleteEdges_empty_depth, Finset.card_empty] at h1
        simpa using h1
      have h_le_const : (2 : ℕ) ^ (2 ^ (depth_p + 1)) ≤ 2 ^ (2 ^ (2 ^ r₀)) := by
        gcongr <;> omega
      have h_le_const_real :
          ((c.prune.psiCNF F α 0 hF_src).complexity : ℝ) ≤
            ((2 : ℕ) ^ (2 ^ (2 ^ r₀)) : ℝ) := by
        exact_mod_cast h_psi_le_nat.trans h_le_const
      have h_const_le_Npow :
          ((2 : ℕ) ^ (2 ^ (2 ^ r₀)) : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) ^ ε) := by
        push_cast
        rw [← Real.rpow_natCast (2 : ℝ) (2 ^ (2 ^ r₀))]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        push_cast
        rw [← Real.rpow_natCast (2 : ℝ) (2 ^ r₀)]
        have h_2B_le_N_real : (2 : ℝ) ^ ((2 ^ r₀ * (ε_inv + 1) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
          rw [Real.rpow_natCast]; exact_mod_cast hN_shallow
        have h_inv_eps : 1 ≤ (ε_inv : ℝ) * ε := (div_le_iff₀ hε).mp hε_inv
        have h_inner : ((2 ^ r₀ : ℕ) : ℝ) ≤
            ((2 ^ r₀ * (ε_inv + 1) + 1 : ℕ) : ℝ) * ε := by
          have h_pos : (0 : ℝ) ≤ ((2 ^ r₀ : ℕ) : ℝ) := by positivity
          have h_step : ((2 ^ r₀ : ℕ) : ℝ) ≤ ((2 ^ r₀ : ℕ) : ℝ) * ((ε_inv : ℝ) * ε) :=
            le_mul_of_one_le_right h_pos h_inv_eps
          have h_eps_pos : (0 : ℝ) ≤ ((2 ^ r₀ : ℕ) : ℝ) * ε := mul_nonneg h_pos hε.le
          push_cast at h_step h_eps_pos ⊢
          linarith [h_step, h_eps_pos, hε]
        calc (2 : ℝ) ^ ((2 ^ r₀ : ℕ) : ℝ)
            ≤ (2 : ℝ) ^ (((2 ^ r₀ * (ε_inv + 1) + 1 : ℕ) : ℝ) * ε) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h_inner
          _ = ((2 : ℝ) ^ ((2 ^ r₀ * (ε_inv + 1) + 1 : ℕ) : ℝ)) ^ ε := by
              rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          _ ≤ (N : ℝ) ^ ε :=
              Real.rpow_le_rpow (by positivity) h_2B_le_N_real hε.le
      exact h_le_const_real.trans h_const_le_Npow
    have h_sigma3 : Sigma3 ε (fun x => (c.prune.eval x) 0) ≤ 2 ^ F.card :=
      Sigma3_le_pow_card c.prune F hF_src h_clause
    rw [hf_eq', show F.card = 0 from Finset.card_empty, pow_zero] at h_sigma3
    have h_rhs_pos : 0 ≤ K * (N : ℝ) / Real.log (Real.log N) := by positivity
    refine ⟨?_, ?_⟩
    · calc ((Sigma3 ε (f N) : ℕ) : ℝ)
          ≤ 1 := by exact_mod_cast h_sigma3
        _ = (2 : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
        _ ≤ (2 : ℝ) ^ (K * (N : ℝ) / Real.log (Real.log N)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h_rhs_pos
    · rw [← hf_eq']
      exact ⟨Sigma3RepFromCutCircuit c.prune F hF_src h_clause⟩

/-- **Lemma 11.1** (Valiant, 1983). If `f ∈ NC¹_lin` then
`log Σ₃(f_n) = O(n / log log n)`.

Formally: for every `ε > 0`, `N ↦ log Σ₃_ε(f_N)` is `O(N / log log N)`
as `N → ∞`. The implied `O`-constant depends on `f` and `ε`.

The proof reduces (via `sigma3_le_pow_K_N_log_log_N`) to: for each `f`
and `ε`, there is `K > 0` with `Σ₃_ε(f_N) ≤ 2 ^ (K · N / log log N)`
eventually. Taking logs gives `log Σ₃ ≤ K · log 2 · N / log log N`,
hence `O(N / log log N)`.

The construction of `F_N` applies `Valiant.depth_reduction` to a log-depth,
linear-size circuit for `f_n`: removing `O(n / log log n)` wires splits the
circuit into subcircuits of depth at most `ε log n`, each computing a
function of at most `2 ^ (ε log n) = n ^ ε` inputs — small enough to
flatten into a CNF with at most `2 ^ (n ^ ε)` clauses. The number of
α-assignments is `2 ^ |F| = 2 ^ O(n / log log n)`. -/
theorem Valiant.log_sigma3_isBigO
    {f : BoolFunFamily} (hf : InNC1Lin f) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => Real.log ((Sigma3 ε (f N) : ℕ) : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / Real.log (Real.log N)) := by
  obtain ⟨K, hK_pos, hK⟩ := sigma3_le_pow_K_N_log_log_N hf hε
  rw [Asymptotics.isBigO_iff]
  refine ⟨K * Real.log 2, ?_⟩
  filter_upwards [hK, Filter.eventually_ge_atTop 3] with N ⟨hN_bound, _⟩ hN_ge_3
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN_ge_3
  have hlogN_gt_1 : 1 < Real.log N :=
    (Real.lt_log_iff_exp_lt hN_pos).mpr (by linarith [Real.exp_one_lt_three])
  have hloglogN_pos : 0 < Real.log (Real.log N) := Real.log_pos hlogN_gt_1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hN_pos.le hloglogN_pos.le),
      abs_of_nonneg (Real.log_natCast_nonneg _)]
  rcases (Sigma3 ε (f N)).eq_zero_or_pos with hSig_zero | hSig_pos
  · rw [hSig_zero, Nat.cast_zero, Real.log_zero]; positivity
  · calc Real.log ((Sigma3 ε (f N) : ℕ) : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (K * (N : ℝ) / Real.log (Real.log N))) :=
          Real.log_le_log (Nat.cast_pos.mpr hSig_pos) hN_bound
      _ = K * (N : ℝ) / Real.log (Real.log N) * Real.log 2 := Real.log_rpow (by norm_num) _
      _ = K * Real.log 2 * ((N : ℝ) / Real.log (Real.log N)) := by ring

/-- For `f ∈ NC¹_lin` and `ε > 0`, a Σ₃-representation of `f N` exists for
sufficiently large `N`. Witnessed by `Sigma3RepFromCutCircuit` applied to
the cut produced by `Valiant.depth_reduction`. -/
lemma sigma3Rep_exists_atTop {f : BoolFunFamily} (hf : InNC1Lin f) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, Nonempty (Sigma3Rep N ε (f N)) := by
  obtain ⟨_, _, hN⟩ := sigma3_le_pow_K_N_log_log_N hf hε
  filter_upwards [hN] with N ⟨_, h⟩
  exact h
