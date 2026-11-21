# Task: the abstract states of the certificate checker mean what they should

This is framework work, not a test. Prove the four statements in `Spec.lean`. They are
about lists and natural numbers only: no real numbers, no rounding.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)` and
`open Lane4.AGate Lane4.Cert`):

- `theorem abs_closed : AbsClosed`
- `theorem abs_len : AbsLen`
- `theorem abs_target : AbsTarget`
- `theorem abs_pick : AbsPick`

and whatever helper lemmas you need. The checker builds one file from
`import Lane4.R7Defs` (which imports R7Cert, AGateAll, ..., Mathlib), then `Spec.lean`,
then your `Solution.lean`, then `Final.lean`.

**Background.** Read `R7Defs.lean` and `R7Cert.lean` (copied here; in `R7Cert.lean` you
need only `Task`, `Task.target`, `pickAt`, `pickNext`). `Seq.lean` (copied) has
`cand` and `tokAt`:

    def cand (m : Mask) (n i : ℕ) : List ℕ :=
      match m with
      | Mask.all => List.range n | Mask.causal => List.range (i + 1) | Mask.strict => List.range i
    def tokAt (w : List ℕ) (i : ℕ) : ℕ := (0 :: w).getD i 0

An input is a list `w` of tokens; position 0 holds the BOS token 0 and position `i ≥ 1`
holds `w[i-1]`. A task is an automaton (`Task`: `init`, `step`, `out`). Each attention
head has a set of candidate tokens `cd : List Bool` (indexed by token, BOS is index 0).
The abstract state after reading a prefix (`absState`) is the task state together with,
per head, the most recent candidate token seen so far, BOS included (`none` if there has
been none). `pickAt` then gives the token a head attends to at the query position: for a
causal mask the token of the query itself if it is a candidate, otherwise the stored pick.

- `AbsClosed`: induction along the prefix (prove it for `foldl` from an arbitrary state in
  the set, or use `List.reverseRecOn` with `List.foldl_append`).
- `AbsLen`: `zipWith` keeps the length when both lists have the same length; the initial
  pick list is a `map` over `cands`.
- `AbsTarget`: unfold `Task.target`; the first component of `absState` is
  `foldl T.step T.init` of the prefix (a small induction, generalising the start state),
  and for `1 ≤ i` the token `tokAt w i` is `w.getD (i - 1) 0`.
- `AbsPick` is the real work. A good invariant, by induction on `k` for the prefix
  `w.take k` with `k ≤ w.length`: with
  `p = (absState T cands (w.take k)).2.getD a none` and `cd = cands.getD a []`,
  `p = none → ∀ j ≤ k, cd.getD (tokAt w j) false = false`, and
  `p = some t → ∃ j ≤ k, tokAt w j = t ∧ cd.getD t false = true ∧
     ∀ j2 ≤ k, cd.getD (tokAt w j2) false = true → j2 ≤ j`.
  (`tokAt w 0 = 0`; `tokAt w (k + 1) = w.getD k 0`; `w.take (k + 1) = w.take k ++ [w.getD k 0]`
  when `k < w.length`.) Then take `k = i - 1` and split on the mask: for `Mask.strict` the
  allowed positions are `j < i`, that is `j ≤ i - 1`; for `Mask.causal` they are `j ≤ i`,
  and `pickAt` adds the token of the query when it is a candidate. `List.mem_range` turns
  membership in `cand` into inequalities. The entry `a` of a `zipWith` is the function of
  the two entries (`List.getD` through `zipWith`, both lists of length `cands.length`).

**If a statement is false as written, say so in your reply with the counterexample instead
of spending submissions.** You may submit a partial file (some theorems missing) to see
whether what you have compiles; it will FAIL at `Final.lean` but shows the errors Lean
finds in your part.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r7-kit/k4"

  It prints PASS or FAIL with Lean's output. You have **30 submissions**; stop at the
  first PASS. A check can take up to 10 minutes and may also wait in a queue. Wait for
  it. Never resubmit while one is pending.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. Short Python for arithmetic is fine.
- Banned in `Solution.lean` (rejected without running Lean, still costs a submission):
  `sorry`, `admit`, `axiom`, `native_decide`, `macro`, `syntax`, `notation`, `elab`,
  `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`, anything in the `Lean.`
  namespace.
- Standard axioms only. Each check is limited to 600 s and 4.5 GB.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.
  Long linter warnings can push errors out of the shown output; put
  `set_option linter.unusedVariables false` and similar at the top of your file.

## When you finish

Reply with: PASS or FAIL, the number of submissions used, and three or four sentences on
how you built it and what went wrong along the way. If you give up, say why.
