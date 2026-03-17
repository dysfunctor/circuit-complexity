import Circ.ACNF.Defs

/-! # Internal: Alternating Normal Form Correctness

Proofs that normalization preserves evaluation semantics, produces alternating
trees, and does not increase depth. Also proves CNF/DNF to ACNF conversion
preserves evaluation.

## Main results

* `ACNF.normalize_eval` — normalization preserves evaluation
* `ACNF.normalize_depth_le` — normalization does not increase depth
* `ACNF.normalize_isAlternating` — normalization produces alternating trees
* `CNF.toACNF_eval` — CNF to ACNF preserves evaluation
* `DNF.toACNF_eval` — DNF to ACNF preserves evaluation
* `Circuit.wireToACNF_eval` — circuit wire to ACNF preserves evaluation
* `Circuit.toACNF_eval` — circuit to ACNF preserves evaluation
* `Circuit.toACNF_depth_le` — ACNF depth bounded by circuit depth
* `Circuit.toACNF_normalize_isAlternating` — normalized ACNF is alternating
* `Circuit.toACNF_leafCount_le` — ACNF leaf count bounded by maxFanIn^depth
-/

namespace ACNF

variable {N : Nat}

/-! ## Relating evalAll/evalAny to List.all/List.any -/

theorem evalAll_eq_all (cs : List (ACNF N)) (x : BitString N) :
    eval.evalAll cs x = cs.all (fun c => c.eval x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [eval.evalAll, List.all_cons, ih]

theorem evalAny_eq_any (cs : List (ACNF N)) (x : BitString N) :
    eval.evalAny cs x = cs.any (fun c => c.eval x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [eval.evalAny, List.any_cons, ih]

/-! ## Eval append lemmas -/

theorem evalAll_append (l₁ l₂ : List (ACNF N)) (x : BitString N) :
    eval.evalAll (l₁ ++ l₂) x = (eval.evalAll l₁ x && eval.evalAll l₂ x) := by
  induction l₁ with
  | nil => simp [eval.evalAll]
  | cons c cs ih => simp only [List.cons_append, eval.evalAll, ih, Bool.and_assoc]

theorem evalAny_append (l₁ l₂ : List (ACNF N)) (x : BitString N) :
    eval.evalAny (l₁ ++ l₂) x = (eval.evalAny l₁ x || eval.evalAny l₂ x) := by
  induction l₁ with
  | nil => simp [eval.evalAny]
  | cons c cs ih => simp only [List.cons_append, eval.evalAny, ih, Bool.or_assoc]

/-! ## Depth list append -/

theorem depthList_append (l₁ l₂ : List (ACNF N)) :
    depth.depthList (l₁ ++ l₂) = max (depth.depthList l₁) (depth.depthList l₂) := by
  induction l₁ with
  | nil => simp [depth.depthList]
  | cons c cs ih => simp only [List.cons_append, depth.depthList, ih, Nat.max_assoc]

/-! ## IsAlternating list append -/

theorem isAlternatingAndList_append (l₁ l₂ : List (ACNF N)) :
    isAlternating.isAlternatingAndList (l₁ ++ l₂) =
    (isAlternating.isAlternatingAndList l₁ && isAlternating.isAlternatingAndList l₂) := by
  induction l₁ with
  | nil => simp [isAlternating.isAlternatingAndList]
  | cons c cs ih =>
    simp only [List.cons_append, isAlternating.isAlternatingAndList, ih, Bool.and_assoc]

theorem isAlternatingOrList_append (l₁ l₂ : List (ACNF N)) :
    isAlternating.isAlternatingOrList (l₁ ++ l₂) =
    (isAlternating.isAlternatingOrList l₁ && isAlternating.isAlternatingOrList l₂) := by
  induction l₁ with
  | nil => simp [isAlternating.isAlternatingOrList]
  | cons c cs ih =>
    simp only [List.cons_append, isAlternating.isAlternatingOrList, ih, Bool.and_assoc]

/-! ## SizeOf helpers for termination proofs -/

-- The auto-generated sizeOf for nested inductives requires manual unfolding.
private theorem sizeOf_lt_and {c : ACNF N} {children : List (ACNF N)}
    (hc : c ∈ children) : sizeOf c < sizeOf (ACNF.and children) := by
  induction hc with
  | head as =>
    show ACNF._sizeOf_1 _ < ACNF._sizeOf_1 _
    simp only [ACNF._sizeOf_1]
    omega
  | tail b _ ih =>
    apply Nat.lt_trans ih
    show ACNF._sizeOf_1 _ < ACNF._sizeOf_1 _
    simp only [ACNF._sizeOf_1]
    omega


/-! ## Normalize preserves eval -/

private theorem normalizeAndFlatten_evalAll (children : List (ACNF N)) (x : BitString N)
    (ih : ∀ c, c ∈ children → c.normalize.eval x = c.eval x) :
    eval.evalAll (normalize.normalizeAndFlatten children) x = eval.evalAll children x := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeAndFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [eval.evalAll, hrest, ← hc, hn]
    | and gcs =>
      rw [evalAll_append, hrest, eval.evalAll, ← hc, hn, eval]
    | or cs' =>
      simp only [eval.evalAll, hrest, ← hc, hn]

private theorem normalizeOrFlatten_evalAny (children : List (ACNF N)) (x : BitString N)
    (ih : ∀ c, c ∈ children → c.normalize.eval x = c.eval x) :
    eval.evalAny (normalize.normalizeOrFlatten children) x = eval.evalAny children x := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeOrFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [eval.evalAny, hrest, ← hc, hn]
    | and gcs =>
      simp only [eval.evalAny, hrest, ← hc, hn]
    | or cs' =>
      rw [evalAny_append, hrest, eval.evalAny, ← hc, hn, eval]

/-- Normalization preserves evaluation semantics. -/
theorem normalize_eval : (f : ACNF N) → (x : BitString N) →
    f.normalize.eval x = f.eval x
  | .lit _, _ => rfl
  | .and children, x => by
    simp only [normalize, eval]
    exact normalizeAndFlatten_evalAll children x (fun c hc => normalize_eval c x)
  | .or children, x => by
    simp only [normalize, eval]
    exact normalizeOrFlatten_evalAny children x (fun c hc => normalize_eval c x)
termination_by f => sizeOf f
decreasing_by
  all_goals exact sizeOf_lt_and hc

/-! ## Normalize does not increase depth -/

private theorem normalizeAndFlatten_depthList (children : List (ACNF N))
    (ih : ∀ c, c ∈ children → c.normalize.depth ≤ c.depth) :
    depth.depthList (normalize.normalizeAndFlatten children) ≤ depth.depthList children := by
  induction children with
  | nil => simp [normalize.normalizeAndFlatten]
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeAndFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [depth.depthList]
      exact max_le_max (by rw [← hn]; exact hc) hrest
    | and gcs =>
      rw [depthList_append]
      apply max_le_iff.mpr
      constructor
      · -- depthList gcs ≤ max c.depth (depthList cs)
        have hdep : depth (.and gcs) ≤ c.depth := hn ▸ hc
        simp only [depth] at hdep
        exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
      · exact Nat.le_trans hrest (Nat.le_max_right _ _)
    | or cs' =>
      simp only [depth.depthList]
      exact max_le_max (by rw [← hn]; exact hc) hrest

private theorem normalizeOrFlatten_depthList (children : List (ACNF N))
    (ih : ∀ c, c ∈ children → c.normalize.depth ≤ c.depth) :
    depth.depthList (normalize.normalizeOrFlatten children) ≤ depth.depthList children := by
  induction children with
  | nil => simp [normalize.normalizeOrFlatten]
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeOrFlatten]
    generalize hn : c.normalize = nc
    cases nc with
    | lit l =>
      simp only [depth.depthList]
      exact max_le_max (by rw [← hn]; exact hc) hrest
    | and gcs =>
      simp only [depth.depthList]
      exact max_le_max (by rw [← hn]; exact hc) hrest
    | or cs' =>
      rw [depthList_append]
      apply max_le_iff.mpr
      constructor
      · have hdep : depth (.or cs') ≤ c.depth := hn ▸ hc
        simp only [depth] at hdep
        exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
      · exact Nat.le_trans hrest (Nat.le_max_right _ _)

/-- Normalization does not increase depth. -/
theorem normalize_depth_le : (f : ACNF N) → f.normalize.depth ≤ f.depth
  | .lit _ => Nat.le.refl
  | .and children => by
    simp only [normalize, depth]
    exact Nat.add_le_add_left (normalizeAndFlatten_depthList children
      (fun c hc => normalize_depth_le c)) 1
  | .or children => by
    simp only [normalize, depth]
    exact Nat.add_le_add_left (normalizeOrFlatten_depthList children
      (fun c hc => normalize_depth_le c)) 1
termination_by f => sizeOf f
decreasing_by
  all_goals exact sizeOf_lt_and hc

/-! ## Normalize produces alternating trees -/

private theorem normalizeAndFlatten_isAlternatingAndList (children : List (ACNF N))
    (ih : ∀ c, c ∈ children → c.normalize.isAlternating = true) :
    isAlternating.isAlternatingAndList (normalize.normalizeAndFlatten children) = true := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeAndFlatten]
    generalize hn : c.normalize = nc
    rw [hn] at hc
    cases nc with
    | lit l =>
      simp [isAlternating.isAlternatingAndList, rootOp, isAlternating, hrest]
    | and gcs =>
      rw [isAlternatingAndList_append, hrest, Bool.and_true]
      simp only [isAlternating] at hc; exact hc
    | or cs' =>
      simp only [isAlternating.isAlternatingAndList, rootOp, hrest, Bool.and_true]
      rw [hc, Bool.and_true]; decide

private theorem normalizeOrFlatten_isAlternatingOrList (children : List (ACNF N))
    (ih : ∀ c, c ∈ children → c.normalize.isAlternating = true) :
    isAlternating.isAlternatingOrList (normalize.normalizeOrFlatten children) = true := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    have hc := ih c (.head cs)
    have hrest := ihcs (fun c' hc' => ih c' (.tail c hc'))
    simp only [normalize.normalizeOrFlatten]
    generalize hn : c.normalize = nc
    rw [hn] at hc
    cases nc with
    | lit l =>
      simp [isAlternating.isAlternatingOrList, rootOp, isAlternating, hrest]
    | and gcs =>
      simp only [isAlternating.isAlternatingOrList, rootOp, hrest, Bool.and_true]
      rw [hc, Bool.and_true]; decide
    | or cs' =>
      rw [isAlternatingOrList_append, hrest, Bool.and_true]
      simp only [isAlternating] at hc; exact hc

/-- Normalization produces alternating trees. -/
theorem normalize_isAlternating : (f : ACNF N) → f.normalize.isAlternating = true
  | .lit _ => rfl
  | .and children => by
    simp only [normalize, isAlternating]
    exact normalizeAndFlatten_isAlternatingAndList children
      (fun c hc => normalize_isAlternating c)
  | .or children => by
    simp only [normalize, isAlternating]
    exact normalizeOrFlatten_isAlternatingOrList children
      (fun c hc => normalize_isAlternating c)
termination_by f => sizeOf f
decreasing_by
  all_goals exact sizeOf_lt_and hc

end ACNF

/-! ## CNF/DNF to ACNF conversion correctness -/

/-- Converting a CNF to ACNF preserves evaluation. -/
theorem CNF.toACNF_eval (φ : CNF N) (x : BitString N) :
    φ.toACNF.eval x = φ.eval x := by
  simp only [CNF.toACNF, ACNF.eval, ACNF.evalAll_eq_all, CNF.eval,
    List.all_map, Function.comp_def, ACNF.evalAny_eq_any, List.any_map, ACNF.eval]

/-- Converting a DNF to ACNF preserves evaluation. -/
theorem DNF.toACNF_eval (φ : DNF N) (x : BitString N) :
    φ.toACNF.eval x = φ.eval x := by
  simp only [DNF.toACNF, ACNF.eval, ACNF.evalAny_eq_any, DNF.eval,
    List.any_map, Function.comp_def, ACNF.evalAll_eq_all, List.all_map, ACNF.eval]

/-! ## Bridging: List.ofFn ↔ Fin.foldl -/

namespace ACNF

private theorem foldl_and_init (n : Nat) (g : Fin n → Bool) (a : Bool) :
    Fin.foldl n (fun acc k => acc && g k) a =
    (a && Fin.foldl n (fun acc k => acc && g k) true) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.true_and]
    rw [ih (fun k => g k.succ) (a && g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Bool.and_assoc]

private theorem foldl_or_init (n : Nat) (g : Fin n → Bool) (a : Bool) :
    Fin.foldl n (fun acc k => acc || g k) a =
    (a || Fin.foldl n (fun acc k => acc || g k) false) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.false_or]
    rw [ih (fun k => g k.succ) (a || g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Bool.or_assoc]

theorem evalAll_ofFn (n : Nat) (f : Fin n → ACNF N) (x : BitString N) :
    eval.evalAll (List.ofFn f) x =
    (Fin.foldl n (fun acc k => acc && (f k).eval x) true) := by
  induction n with
  | zero => simp [List.ofFn_zero, eval.evalAll, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ, eval.evalAll, ih]
    conv_rhs => rw [Fin.foldl_succ]
    simp only [Bool.true_and]
    exact (foldl_and_init n (fun k => (f k.succ).eval x) ((f 0).eval x)).symm

theorem evalAny_ofFn (n : Nat) (f : Fin n → ACNF N) (x : BitString N) :
    eval.evalAny (List.ofFn f) x =
    (Fin.foldl n (fun acc k => acc || (f k).eval x) false) := by
  induction n with
  | zero => simp [List.ofFn_zero, eval.evalAny, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ, eval.evalAny, ih]
    conv_rhs => rw [Fin.foldl_succ]
    simp only [Bool.false_or]
    exact (foldl_or_init n (fun k => (f k.succ).eval x) ((f 0).eval x)).symm

private theorem foldl_max_init (n : Nat) (g : Fin n → Nat) (a : Nat) :
    Fin.foldl n (fun acc k => max acc (g k)) a =
    max a (Fin.foldl n (fun acc k => max acc (g k)) 0) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Nat.zero_max]
    rw [ih (fun k => g k.succ) (max a (g 0))]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Nat.max_assoc]

private theorem foldl_add_init (n : Nat) (g : Fin n → Nat) (a : Nat) :
    Fin.foldl n (fun acc k => acc + g k) a =
    a + Fin.foldl n (fun acc k => acc + g k) 0 := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Nat.zero_add]
    rw [ih (fun k => g k.succ) (a + g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    omega

theorem foldl_deMorgan_and (n : Nat) (f : Fin n → Bool) :
    Fin.foldl n (fun acc k => acc || !f k) false =
    !(Fin.foldl n (fun acc k => acc && f k) true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.true_and, Bool.false_or]
    rw [foldl_or_init n (fun k => !(f k.succ)) (!(f 0))]
    rw [ih (fun k => f k.succ)]
    rw [foldl_and_init n (fun k => f k.succ) (f 0)]
    simp [Bool.not_and]

theorem foldl_deMorgan_or (n : Nat) (f : Fin n → Bool) :
    Fin.foldl n (fun acc k => acc && !f k) true =
    !(Fin.foldl n (fun acc k => acc || f k) false) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.false_or, Bool.true_and]
    rw [foldl_and_init n (fun k => !(f k.succ)) (!(f 0))]
    rw [ih (fun k => f k.succ)]
    rw [foldl_or_init n (fun k => f k.succ) (f 0)]
    simp [Bool.not_or]

private theorem depthList_ofFn_le (n : Nat) (f : Fin n → ACNF N) (g : Fin n → Nat)
    (h : ∀ k, (f k).depth ≤ g k) :
    depth.depthList (List.ofFn f) ≤ Fin.foldl n (fun acc k => max acc (g k)) 0 := by
  induction n with
  | zero => simp [List.ofFn_zero, depth.depthList, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [depth.depthList]
    conv_rhs => rw [Fin.foldl_succ, Nat.zero_max]
    rw [foldl_max_init]
    exact max_le_max (h 0) (ih (fun k => f k.succ) (fun k => g k.succ) (fun k => h k.succ))

private theorem leafCountList_ofFn (n : Nat) (f : Fin n → ACNF N) :
    leafCount.leafCountList (List.ofFn f) =
    Fin.foldl n (fun acc k => acc + (f k).leafCount) 0 := by
  induction n with
  | zero => simp [List.ofFn_zero, leafCount.leafCountList, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [leafCount.leafCountList]
    conv_rhs => rw [Fin.foldl_succ, Nat.zero_add]
    rw [foldl_add_init, ih]

end ACNF

/-! ## Circuit to ACNF: evaluation correctness -/

namespace Circuit
variable {N G : Nat} [NeZero N]

private theorem xor_not_xor (a b : Bool) : (!a ^^ b) = !(a ^^ b) := by cases a <;> cases b <;> rfl

/-- Converting a wire to ACNF preserves evaluation (with polarity). -/
theorem wireToACNF_eval (c : Circuit Basis.unboundedAON N 1 G)
    (x : BitString N) (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNF w pol).eval x = (!pol ^^ c.wireValue x w) := by
  conv_lhs => unfold wireToACNF
  split
  · -- Primary input (w.val < N)
    rename_i h
    simp only [wireValue_lt c x w h, ACNF.eval, Literal.eval]
    cases pol <;> simp
  · -- Gate wire (w.val ≥ N)
    rename_i h
    have hG : w.val - N < G := by omega
    conv_rhs => rw [wireValue_ge c x w h]; simp only [Gate.eval, Basis.unboundedAON]
    -- IH for each child wire
    have ce : ∀ k : Fin (c.gates ⟨w.val - N, hG⟩).fanIn,
        (c.wireToACNF ((c.gates ⟨w.val - N, hG⟩).inputs k)
          (pol ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).eval x =
        (!(pol ^^ (c.gates ⟨w.val - N, hG⟩).negated k) ^^
          c.wireValue x ((c.gates ⟨w.val - N, hG⟩).inputs k)) :=
      fun k => wireToACNF_eval c x _ _
    -- Rewrite children using IH and simplify xor
    simp only [xor_not_xor] at ce
    -- Case split on (op, pol) to reduce the match
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      simp only [hop, ACNF.eval, AONOp.eval, Bool.true_xor, Bool.false_xor,
        Bool.not_true, Bool.not_false] at ce ⊢
    -- AND/false: De Morgan — evalAny vs !(foldl &&)
    · rw [ACNF.evalAny_ofFn]; simp_rw [ce]; exact ACNF.foldl_deMorgan_and _ _
    -- AND/true: same-op — evalAll vs foldl &&
    · rw [ACNF.evalAll_ofFn]; simp_rw [ce, xor_not_xor, Bool.not_not]; rfl
    -- OR/false: De Morgan — evalAll vs !(foldl ||)
    · rw [ACNF.evalAll_ofFn]; simp_rw [ce]; exact ACNF.foldl_deMorgan_or _ _
    -- OR/true: same-op — evalAny vs foldl ||
    · rw [ACNF.evalAny_ofFn]; simp_rw [ce, xor_not_xor, Bool.not_not]; rfl
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Converting a circuit to ACNF preserves evaluation. -/
theorem toACNF_eval (c : Circuit Basis.unboundedAON N 1 G) (x : BitString N) :
    c.toACNF.eval x = (c.eval x) 0 := by
  simp only [toACNF, eval, Gate.eval, Basis.unboundedAON]
  -- The output gate is c.outputs 0
  -- toACNF builds children with pol = true ^^ negated k = !negated k
  rcases hop : (c.outputs 0).op with _ | _
  · -- AND output gate
    simp only [AONOp.eval, ACNF.eval]
    rw [ACNF.evalAll_ofFn]; simp_rw [wireToACNF_eval, Bool.true_xor, Bool.not_not]; rfl
  · -- OR output gate
    simp only [AONOp.eval, ACNF.eval]
    rw [ACNF.evalAny_ofFn]; simp_rw [wireToACNF_eval, Bool.true_xor, Bool.not_not]; rfl

/-! ## Circuit to ACNF: depth bound -/

/-- The ACNF tree for a wire has depth at most the wire's depth. -/
theorem wireToACNF_depth_le (c : Circuit Basis.unboundedAON N 1 G)
    (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNF w pol).depth ≤ c.wireDepth w := by
  conv_lhs => unfold wireToACNF
  split
  · -- Primary input
    rename_i h; simp [wireDepth_lt c w h, ACNF.depth]
  · -- Gate wire
    rename_i h
    have hG : w.val - N < G := by omega
    conv_rhs => rw [wireDepth_ge c w h]
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      simp only [hop, ACNF.depth]
    all_goals (
      apply Nat.add_le_add_left
      exact ACNF.depthList_ofFn_le _ _ _ fun k =>
        wireToACNF_depth_le c ((c.gates ⟨w.val - N, hG⟩).inputs k) _)
termination_by w.val
decreasing_by
  all_goals (
    have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
    have : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
    omega)

/-- The ACNF tree for a circuit has depth at most the circuit's depth. -/
theorem toACNF_depth_le (c : Circuit Basis.unboundedAON N 1 G) :
    c.toACNF.depth ≤ c.depth := by
  simp only [toACNF, depth]
  rcases (c.outputs 0).op with _ | _ <;>
    simp only [ACNF.depth] <;>
    exact Nat.add_le_add_left
      (ACNF.depthList_ofFn_le _ _ _ fun k =>
        wireToACNF_depth_le c ((c.outputs 0).inputs k) _) 1

/-! ## Normalization composition -/

/-- The normalized ACNF tree preserves evaluation. -/
theorem toACNF_normalize_eval (c : Circuit Basis.unboundedAON N 1 G)
    (x : BitString N) :
    c.toACNF.normalize.eval x = (c.eval x) 0 := by
  rw [ACNF.normalize_eval, toACNF_eval]

/-- The normalized ACNF tree has depth at most the circuit's depth. -/
theorem toACNF_normalize_depth_le (c : Circuit Basis.unboundedAON N 1 G) :
    c.toACNF.normalize.depth ≤ c.depth :=
  Nat.le_trans (ACNF.normalize_depth_le c.toACNF) (toACNF_depth_le c)

/-- The normalized ACNF tree is alternating. -/
theorem toACNF_normalize_isAlternating (c : Circuit Basis.unboundedAON N 1 G) :
    c.toACNF.normalize.isAlternating = true :=
  ACNF.normalize_isAlternating c.toACNF

/-! ## Leaf count bounds -/

private theorem foldl_max_le_elem (n : Nat) (f : Fin n → Nat) (i : Fin n) :
    f i ≤ Fin.foldl n (fun acc k => max acc (f k)) 0 := by
  induction n with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    by_cases hi : (i : Nat) < n
    · exact Nat.le_trans (ih (fun j => f j.castSucc) ⟨i, hi⟩) (Nat.le_max_left _ _)
    · have : i = Fin.last n := by ext; simp [Fin.val_last]; omega
      rw [this]; exact Nat.le_max_right _ _

/-- The fan-in of internal gate `i` is at most `maxFanIn`. -/
private theorem gate_fanIn_le_maxFanIn {B : Basis} (c : Circuit B N 1 G) (i : Fin G) :
    (c.gates i).fanIn ≤ c.maxFanIn := by
  simp only [maxFanIn]
  exact Nat.le_trans (foldl_max_le_elem G (fun i => (c.gates i).fanIn) i) (Nat.le_max_left _ _)

/-- The fan-in of the output gate is at most `maxFanIn`. -/
private theorem output_fanIn_le_maxFanIn {B : Basis} (c : Circuit B N 1 G) :
    (c.outputs 0).fanIn ≤ c.maxFanIn := by
  simp only [maxFanIn]
  exact Nat.le_max_right _ _

private theorem foldl_sum_le (n : Nat) (f : Fin n → Nat) (bound : Nat)
    (h : ∀ k, f k ≤ bound) :
    Fin.foldl n (fun acc k => acc + f k) 0 ≤ n * bound := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Nat.zero_add, ACNF.foldl_add_init]
    calc f 0 + Fin.foldl n (fun acc k => acc + f k.succ) 0
        ≤ bound + n * bound :=
          Nat.add_le_add (h 0) (ih (fun k => f k.succ) (fun k => h k.succ))
      _ = (n + 1) * bound := by rw [Nat.succ_mul]; omega

private theorem pow_le_pow_of_le_of_pos {M a b : Nat} (hM : 0 < M) (hab : a ≤ b) :
    M ^ a ≤ M ^ b :=
  Nat.pow_le_pow_right hM hab

/-- The ACNF tree for a wire has at most `maxFanIn ^ wireDepth` leaves. -/
theorem wireToACNF_leafCount_le (c : Circuit Basis.unboundedAON N 1 G)
    (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNF w pol).leafCount ≤ c.maxFanIn ^ c.wireDepth w := by
  conv_lhs => unfold wireToACNF
  split
  · -- Primary input: leafCount = 1 = maxFanIn ^ 0
    rename_i h; simp [wireDepth_lt c w h, ACNF.leafCount]
  · -- Gate wire
    rename_i h
    have hG : w.val - N < G := by omega
    conv_rhs => rw [wireDepth_ge c w h]
    -- IH for each child
    have lc_ih : ∀ k : Fin (c.gates ⟨w.val - N, hG⟩).fanIn,
        (c.wireToACNF ((c.gates ⟨w.val - N, hG⟩).inputs k)
          (pol ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).leafCount ≤
        c.maxFanIn ^ c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k) :=
      fun k => wireToACNF_leafCount_le c _ _
    -- Reduce the match on (op, pol) — all branches give same leafCount structure
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      (simp only [hop]; simp only [ACNF.leafCount]; rw [ACNF.leafCountList_ofFn])
    -- All goals: foldl sum ≤ maxFanIn ^ (1 + foldl max)
    all_goals (
      set D := Fin.foldl (c.gates ⟨w.val - N, hG⟩).fanIn
            (fun acc k => max acc (c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k))) 0
      have hD : ∀ k, c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k) ≤ D :=
        fun k => foldl_max_le_elem _
          (fun j => c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs j)) k
      by_cases hM : c.maxFanIn = 0
      · -- maxFanIn = 0 implies all fanIns = 0, so Fin fanIn is empty
        have : (c.gates ⟨w.val - N, hG⟩).fanIn = 0 := by
          have := gate_fanIn_le_maxFanIn c ⟨w.val - N, hG⟩; omega
        simp [this, Fin.foldl_zero]
      · have hM_pos : 0 < c.maxFanIn := Nat.pos_of_ne_zero hM
        have hbound : ∀ k : Fin (c.gates ⟨w.val - N, hG⟩).fanIn,
            (c.wireToACNF ((c.gates ⟨w.val - N, hG⟩).inputs k)
              (_ ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).leafCount ≤
            c.maxFanIn ^ D :=
          fun k => Nat.le_trans (lc_ih k) (pow_le_pow_of_le_of_pos hM_pos (hD k))
        calc Fin.foldl _ (fun acc k => acc +
                (c.wireToACNF ((c.gates ⟨w.val - N, hG⟩).inputs k)
                  (_ ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).leafCount) 0
            ≤ _ * c.maxFanIn ^ D := foldl_sum_le _ _ _ hbound
          _ ≤ c.maxFanIn * c.maxFanIn ^ D :=
              Nat.mul_le_mul_right _ (gate_fanIn_le_maxFanIn c ⟨w.val - N, hG⟩)
          _ = c.maxFanIn ^ (D + 1) := (pow_succ' c.maxFanIn D).symm
          _ = c.maxFanIn ^ (1 + D) := by congr 1; omega)
termination_by w.val
decreasing_by
  all_goals (
    have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
    have : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
    omega)

/-- The ACNF tree for a circuit has at most `maxFanIn ^ depth` leaves. -/
theorem toACNF_leafCount_le (c : Circuit Basis.unboundedAON N 1 G) :
    c.toACNF.leafCount ≤ c.maxFanIn ^ c.depth := by
  simp only [toACNF, depth]
  rcases hop : (c.outputs 0).op with _ | _ <;>
    (simp only []; simp only [ACNF.leafCount]; rw [ACNF.leafCountList_ofFn])
  all_goals (
    set D := Fin.foldl (c.outputs 0).fanIn
          (fun acc k => max acc (c.wireDepth ((c.outputs 0).inputs k))) 0
    have hD : ∀ k, c.wireDepth ((c.outputs 0).inputs k) ≤ D :=
      fun k => foldl_max_le_elem _
        (fun j => c.wireDepth ((c.outputs 0).inputs j)) k
    by_cases hM : c.maxFanIn = 0
    · have : (c.outputs 0).fanIn = 0 := by
        have := output_fanIn_le_maxFanIn c; omega
      simp [this, Fin.foldl_zero]
    · have hM_pos : 0 < c.maxFanIn := Nat.pos_of_ne_zero hM
      have hbound : ∀ k : Fin (c.outputs 0).fanIn,
          (c.wireToACNF ((c.outputs 0).inputs k)
            (true ^^ (c.outputs 0).negated k)).leafCount ≤
          c.maxFanIn ^ D :=
        fun k => Nat.le_trans (wireToACNF_leafCount_le c _ _)
          (pow_le_pow_of_le_of_pos hM_pos (hD k))
      calc Fin.foldl _ (fun acc k => acc +
              (c.wireToACNF ((c.outputs 0).inputs k)
                (true ^^ (c.outputs 0).negated k)).leafCount) 0
          ≤ _ * c.maxFanIn ^ D := foldl_sum_le _ _ _ hbound
        _ ≤ c.maxFanIn * c.maxFanIn ^ D :=
            Nat.mul_le_mul_right _ (output_fanIn_le_maxFanIn c)
        _ = c.maxFanIn ^ (D + 1) := (pow_succ' c.maxFanIn D).symm
        _ = c.maxFanIn ^ (1 + D) := by congr 1; omega)

end Circuit
