# Task: derive two radius bounds from a collision theorem (Lean 4)

Prove `Lane4.TB.Collision → Lane4.TB.ParityBound` and `Lane4.TB.Collision → Lane4.TB.SortBound`.
All are defined in `Spec.lean` (the `Lane4.TB` part); read there `Collision`, `ParityBound`,
`IsRank`, `SortOnBall`, `SortBound`, and in the `Lane4.Coll` part `Task`, `Task.Valid`,
`Task.Correct`, `Task.OnBall`, `netRel`. You do NOT need the network evaluator.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll Lane4.TB`):

- `theorem parity_of_collision : Collision → ParityBound`
- `theorem sort_of_collision : Collision → SortBound`

**The intended argument (you may do it differently).** Both by contradiction: assume
`1 ≤ τ * (2a+1)` and apply `Collision` with `b = a` to get `N₁`, `N₂` in the ball with
equal outputs at every position `i ≤ 2a+1` on `w₁ = replicate a s ++ replicate (a+1) o`
and `w₂ = replicate (a+1) s ++ replicate a o`. Both inputs are valid, non-empty, of
length `2a+1` (`a + a + 1 = 2*a + 1`: `omega`).
- Parity: at `i = w.length = 2a+1`. The counts `countP K.inS` are `a` and `a+1`
  (`List.countP_append`, `List.countP_replicate`, with `K.inS s = true`, `K.inS o = false`).
  `OnBall` gives `0 < out ↔ a % 2 = par` and `0 < out ↔ (a+1) % 2 = par` for the same
  `out`; with `K.par < 2` this is contradictory (`omega` after extracting the two iffs).
- Sort: tokens `s = 1`, `o = 2` (`2 ≤ ntok`), position `i = a + 1`. `SortOnBall` gives
  `t₁`, `t₂ : ℕ` with `N₁.out w₁ (a+1) = t₁`, `IsRank w₁ (a+1) t₁` and likewise for `w₂`;
  equal outputs give `t₁ = t₂` (`Nat.cast_injective`). In `w₁ = 1^a 2^(a+1)`:
  `countP (· < t)` and `countP (· ≤ t)` are computed by `List.countP_append`,
  `List.countP_replicate` and a case split on `t` (`t = 0`, `t = 1`, `t = 2`, `t ≥ 3`);
  `IsRank w₁ (a+1) t` forces `t = 2`, and `IsRank w₂ (a+1) t` forces `t = 1`. Contradiction.
  A convenient helper: `(List.replicate m v).countP p = if p v then m else 0`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r6c/cBounds"

  It prints PASS or FAIL with Lean's output. You have **12 submissions**; stop at the
  first PASS. A check can take up to 10 minutes and may also wait in a queue. Wait for
  it. Never resubmit while one is pending. You may submit a partial file (helper lemmas
  only) to see Lean's errors for your part; it will FAIL at `Final.lean`.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. Short Python for arithmetic is fine.
- Banned in `Solution.lean` (rejected without running Lean, still costs a submission):
  `sorry`, `admit`, `axiom`, `native_decide`, `macro`, `syntax`, `notation`, `elab`,
  `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`, anything in the `Lean.`
  namespace.
- Standard axioms only. Each check is limited to 600 s and 4.5 GB.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.
- **If the statement is false as written, say so in your reply with the counterexample
  instead of spending submissions.** That would be a useful result.

## When you finish

Reply with PASS or FAIL, the number of submissions used, and three or four sentences on
how you proved it and what went wrong. If you give up, say why and what is left.
