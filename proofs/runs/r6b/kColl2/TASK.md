# Task: prove a short lower-bound theorem about weight perturbations (Lean 4)

Prove the two statements `Lane4.Coll.CollisionBound` and `Lane4.Coll.CollisionBound'`
defined in `Spec.lean`. Read `Spec.lean` (all definitions), `Final.lean`, and in
`Seq.lean` only the definitions of `TNet` and `TNet.out` (you do not need to unfold the
network evaluator: the class `CountChannel` gives you the outputs).

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll`):

- `theorem collision_bound' : CollisionBound'`
- `theorem collision_bound : CollisionBound`

The checker builds one file from `import Lane4.Seq` (which imports Mathlib), then
`Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**The intended argument (you may do it differently).** Take the decoder `D` from
`CountChannel`. Let `w₁ = replicate (L-1) s ++ [o]` (count `L-1`) and
`w₂ = replicate L s` (count `L`), both valid, of length `L`. Let `d₂ = -τ` and
`d₁ = (1 - τ*L)/(L-1)`. Then `|d₁| ≤ τ` (this is where `1 ≤ τ*(2L-1)` and `τ ≤ 1` are
used), `|d₂| = τ ≤ 1`, and `(1 + d₁)*(L-1) = (1 + d₂)*L`. The class gives networks `N₁`,
`N₂` with `netRel |dᵢ| N Nᵢ` and outputs `D (L+1) ((1+dᵢ)*kᵢ/(L+1))`, which are equal.
The counts `L-1` and `L` have different parities, so `Correct` cannot hold for both.
You need a monotonicity lemma: `netRel a N N' → a ≤ b → netRel b N N'` (through
`List.Forall₂.imp` at each level; `qRel a x y → a ≤ b → qRel b x y` since `|x| ≥ 0`).
The hypothesis `T.par < 2` is what makes the two parities contradict (`omega` after
`List.countP` rewrites). `scratch/PREVIOUS.lean` is a previous attempt at the statement WITHOUT that
hypothesis: everything in it compiled except the last parity step; you may reuse it.
`CollisionBound` follows from `CollisionBound'` by contradiction (`OnBall` says every
network in the ball is correct). Useful: `List.countP_replicate`, `List.countP_append`,
`List.length_replicate`, `List.mem_replicate`, `Nat.even_add_one`, `omega`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r6b/kColl2"

  It prints PASS or FAIL with Lean's output. You have **12 submissions**; stop at the
  first PASS. A check can take up to 10 minutes and may also wait in a queue. Wait for
  it. Never resubmit while one is pending. You may submit a partial file to see Lean's
  errors for your part; it will FAIL at `Final.lean`.
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
