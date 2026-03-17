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
