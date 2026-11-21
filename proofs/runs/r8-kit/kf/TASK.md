# Task: the abstract states of the rung-8 checker (windows) mean what they should

This is framework work, not a test. Prove the four statements in `Spec.lean`. They are
about lists and natural numbers only: no real numbers, no rounding.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)` and
`open Lane4.AGate Lane4.Cert Lane4.Cert8`):

- `theorem abs_closed8 : AbsClosed8`
- `theorem abs_len8 : AbsLen8`
- `theorem abs_target8 : AbsTarget8`
- `theorem abs_keys8 : AbsKeys8`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R8Defs`
(which imports R8Cert, the rung-7 modules, ..., Mathlib), then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`.

**Background.** Read `R8Defs.lean` (copied here: `absInit8`, `absStep8`, `absState8`,
`WinPos`, `fullLen`) and in `R8Cert.lean` only `HCert` (fields `cands`, `L`), `keysAt` and
`winNext`; in `R7Cert.lean` only `Task` and `Task.target`. `Seq.lean` has

    def cand (m : Mask) (n i : ℕ) : List ℕ :=
      match m with
      | Mask.all => List.range n | Mask.causal => List.range (i + 1) | Mask.strict => List.range i
    def tokAt (w : List ℕ) (i : ℕ) : ℕ := (0 :: w).getD i 0

An input is a list `w` of tokens; position 0 holds the BOS token 0 and position `i ≥ 1`
holds `w[i-1]`. Each attention head has a certificate `hc` with a set of candidate tokens
`hc.cands : List Bool` (indexed by token, BOS is index 0) and a window length `hc.L`. The
abstract state after reading a prefix is the task state together with, per head, the
WINDOW: the tokens at the last `hc.L` candidate positions seen so far (BOS included),
newest first, fewer if there have not been that many:

    winNext hc t win = if hc.cands.getD t false = true then (t :: win).take hc.L else win
    keysAt h hc t win = if h.mask = Mask.causal ∧ hc.cands.getD t false = true then t :: win else win

**The rung-7 versions of these four statements are proved in `R7K4.lean` (copied here),**
where the state held one pick (`Option ℕ`) per head instead of a window. `AbsClosed8`,
`AbsLen8` and `AbsTarget8` are the same proofs with the new names; start from those.

**`AbsKeys8` is the real work.** A good invariant, by induction on `k` for the prefix
`w.take k` with `k ≤ w.length`: with `win = (absState8 T heads (w.take k)).2.getD a []`,
`cd = hc.cands` and `Q` the list of ALL candidate positions `j ≤ k` in decreasing order
(for example `((List.range (k + 1)).filter (fun j => cd.getD (tokAt w j) false)).reverse`):

    win = (Q.take hc.L).map (tokAt w)

(`tokAt w 0 = 0`; `tokAt w (k + 1) = w.getD k 0`; `w.take (k + 1) = w.take k ++ [w.getD k 0]`
when `k < w.length`; `List.range_succ`, `List.filter_append`, `List.reverse_append`;
`(t :: l).take L` against `(q :: Q).take L`, and `(Q.take L).take L = Q.take L`. The entry
`a` of a `zipWith` over `heads` is the function of the two entries; `heads.getD a hc = hc`
with `a < heads.length` says entry `a` of `heads` is `hc`.) Then take `k = i - 1` and split
on the mask:

- `Mask.strict`: allowed positions are `j < i`, that is `j ≤ i - 1`. Take `P = Q.take hc.L`.
  `keysAt` returns `win`, `fullLen = hc.L`.
- `Mask.causal`: allowed positions are `j ≤ i`. If the token at `i` is a candidate,
  `P = i :: Q.take hc.L`, `keysAt` returns `tokAt w i :: win`, `fullLen = hc.L + 1`;
  otherwise as in the strict case.
- `Mask.all` is excluded by hypothesis.

`WinPos` for such a `P`: a prefix of a strictly decreasing list is strictly decreasing
(`List.Pairwise` of `>` on the reversed filtered range: `List.pairwise_lt_range`,
`List.Pairwise.filter`, `List.pairwise_reverse`, `List.Pairwise.sublist` with
`List.take_sublist`); its members are candidate positions `≤ i - 1` (or `i`); a candidate
position NOT in the prefix `Q.take L` of `Q` lies in `Q.drop L`, and in a strictly
decreasing list every element of `Q.drop L` is below every element of `Q.take L`
(`List.take_append_drop`, `List.pairwise_append`). The length facts: `(Q.take L).length ≤ L`,
and if it is `< L` then `Q.take L = Q`, so every candidate position is in `P`.

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

      C:/Python314/python.exe tools/submit.py "runs/r8-kit/kf"

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
