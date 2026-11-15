# Task: prove that a written transformer has a "count channel" (Lean 4)

`Spec.lean` defines a small hard-attention transformer `net` (two blocks) and the
statement `Membership : Prop := task.CountChannel net`. Prove it.

`net` is the network of `EXAMPLE.lean`, which is a COMPLETE, kernel-checked proof that
this same network computes the parity of the number of counted tokens (file given for
reference: its lemmas about the initial state, the first block and the second block's
scores are what you need to adapt; it is not imported, copy what you use).

**What the statement says.** There is one function `D : ℕ → ℚ → ℚ` such that for every
rational `d` with `|d| ≤ 1` there is a network `N'` inside the relative ball of radius
`|d|` around `net` (every weight `a` replaced by `b` with `|b - a| ≤ |d| * |a|`, so zeros
stay zero) whose output at the last position, on every valid input `w`, equals
`D (w.length + 1) ((1 + d) * k / (w.length + 1))` with `k = w.countP task.inS`.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll`): `theorem membership : Membership`, plus helpers.
The checker builds one file from `import Lane4.Seq`, then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`.

**The intended argument (you may do it differently).**
- `N'` := `net` with the single nonzero entry of the first block's value matrix (the `1`
  in `hd1.V`, row 1, column 0) replaced by `1 + d`. Define it as a function of `d`.
  `netRel |d| net N'`: every other entry is unchanged (`|a - a| = 0 ≤ |d| * |a|`), and
  for the changed entry `|(1 + d) - 1| = |d| ≤ |d| * |1|`. Unfold the lists; `simp` with
  the definitions and `List.Forall₂` constructors, or `decide`-free explicit terms.
- Block 1 has a zero score matrix, so every position is selected (`sel_all`) and slot 1
  becomes `z = (1 + d) * k / n` at every position (the example proves this with `d = 0`).
- Block 2's score from the last position to position `j` is `a * z * j - b * j^2 / n`
  for the constants `a`, `b` of this network; it does not read the token slots. Its
  value reads `(-1)^j`. So the output is `c * avg S (fun j => (-1)^j)` where `S` is the
  set of maximisers of that score over `j < n`.
- You do NOT need to find the maximiser. Define `D n z` as exactly that expression:
  `c * avg ((List.range n).filter (fun j => decide (∀ k ∈ List.range n, f n z k ≤ f n z j))) (fun j => (-1)^j)`
  with `f n z j := a * z * j - b * j^2 / n`, and show `Head.sel` of the second head is
  that filtered list (`List.filter_congr` after rewriting each score). This is the main
  difference from the example, which proves the maximiser is `j = k`.
- The state lists are long; follow the example's way of stating the state after block 1
  as `[flag, z, 0] ++ pos j n` and computing `qdot`/`matVec` on it by `simp`/`norm_num`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r6b/m10"

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
