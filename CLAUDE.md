# Circuit Complexity — Agent Guide

Lean 4 formalization of circuit complexity theory, built on Mathlib.

## Build

```bash
lake build
```

Verify the build passes with no errors or warnings before considering a change complete.

## Proof Development Workflow

### Stay grounded in the proof state

Use Lean MCP tools constantly — never write tactic blocks blind.

- **`lean_goal`** at a `sorry` or tactic to see exact hypotheses and goal.
- **`lean_diagnostic_messages`** for fast per-file error checking (prefer over `lake build`).
- **`lean_multi_attempt`** to trial candidate closers (`simp`, `omega`, `exact?`, `aesop`) without editing the file.

### Sorry-sketch first

For non-trivial proofs, stub out the full `have`-step structure with `sorry`
in each gap, check it compiles, then fill each `sorry` one at a time —
checking diagnostics after each.

### One tactic at a time

Replace a `sorry` with one tactic plus new `sorry`s for remaining subgoals.
Check the proof state after each step. After `induction`/`cases`, inspect
each branch individually.

### Never guess Mathlib names

Use search tools to find lemmas:

1. **Known locally?** → `lean_local_search`
2. **Natural language** → `lean_leansearch`
3. **Type pattern** → `lean_loogle`
4. **Conceptual/semantic** → `lean_leanfinder`
5. **What closes this goal?** → `lean_state_search`
6. **What to feed `simp`?** → `lean_hammer_premise`

After finding a name, use `lean_hover_info` to confirm its signature.

### When stuck

- If cycling on the same step, stop and decompose: extract a helper lemma,
  try a different strategy, or reconsider the definitions.
- Use `lean_code_actions` to capture `exact?`/`apply?`/`rw?` suggestions.

## Tactic Tips

- When `omega` fails on `match`/`if`/`max`:
  - **`match`**: use `cases` or `split` to eliminate the discriminant.
  - **`if`**: use `split_ifs`, or `simp only [ite_true, ite_false]`.
  - **`max`**: use `le_max_left`/`le_max_right` directly, or `max_le`.
- Use `dsimp only` to reduce projections (`.1`, `.2`), constructor matches,
  and `let` bindings left behind by `simp only`.
- Use `first | tac1 | tac2` when different case-split branches need
  different strategies.

## Proof Standards

- No `sorry` in finished proofs.
- No custom axioms beyond Lean's core (`Classical.choice`, `propext`,
  `Quot.sound`, `funext`).
- Follow Mathlib naming conventions and tactic style.
