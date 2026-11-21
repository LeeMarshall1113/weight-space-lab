# Task: shared attention over a window (pure real analysis)

This is framework work, not a test. Prove the statement in `Spec.lean`. There is no
rounding and no floating point in it: only real exponentials, finite sums over lists, and
inequalities between fractions.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq Lane4.RSoft`):

- `theorem mix_bound : MixBound`

and whatever helper lemmas you need. The checker builds one file from
`import Lane4.R8Soft` (RSoftKit, RSoft, RSeq, Seq, Basic, Mathlib), then `Spec.lean`,
then your `Solution.lean`, then `Final.lean`. `R8Soft.lean` (copied here) defines

    eavg c s f = (c.map (fun k => Real.exp (s k) * f k)).sum / (c.map (fun k => Real.exp (s k))).sum

**The mathematics.** Put `r k = exp (s k - s jr)` for `k ∈ c` (so `r jr = 1`), and
`Z = Σ_{k ∈ c} r k`. Dividing numerator and denominator of `eavg` by `exp (s jr)`:
`eavg c s f = (Σ_{k ∈ c} r k * f k) / Z`. The candidates split into three disjoint parts:
`jr` itself, the window `W` (duplicate-free, members of `c`, different from `jr`), and the
rest, whose ratios sum to `T ≤ tl`. So `Z = 1 + R + T` with `R = Σ_{i < W.length} r (W[i])`.

Take `a i = r (W.getD i 0) / Z` for `i < W.length` and `a i = 0` otherwise. Then:

- *Interval.* With `lo i ≤ r_i ≤ hi i` for all window keys: `Z ≤ 1 + r_i + (hi.sum - hi i) + tl`
  and `Z ≥ 1 + r_i + (lo.sum - lo i)` (the other ratios are at least their lower bounds, the
  tail is non-negative). The map `x ↦ x / (x + K)` is increasing for `K > 0`, `x ≥ 0`, so
  `lo i / (1 + lo i + (hi.sum - hi i) + tl) ≤ r_i / (1 + r_i + (hi.sum - hi i) + tl) ≤ a i`
  and `a i ≤ r_i / (1 + r_i + (lo.sum - lo i)) ≤ hi i / (1 + hi i + (lo.sum - lo i))`.
  (`lo.sum - lo i` is the sum of the other lower bounds and is `≥ 0`; similarly for `hi`.)
- *Sign and total.* `a i ≥ 0`; `Σ_{i < W.length} a i = R / Z ≤ 1`.
- *The value.* `eavg - (f jr + Σ_i a i * (f (W[i]) - f jr))
  = Σ_{k in the rest} (r k / Z) * (f k - f jr)`, because the weights `1/Z`, `r_i/Z` and
  `r k / Z` sum to 1. Its size is at most `(T / Z) * 2 * B ≤ 2 * tl * B` (`Z ≥ 1`,
  `|f k - f jr| ≤ 2 * B`).

**Suggestions for the formal side (you may ignore them).**
- Work with `Finset` sums: `c.Nodup` gives `(c.map g).sum = ∑ k ∈ c.toFinset, g k`
  (`List.sum_toFinset`), likewise for `W` and for the filtered rest. Then
  `c.toFinset = {jr} ∪ W.toFinset ∪ rest` as a disjoint union, and
  `Finset.sum_union`/`Finset.sum_insert` split every sum.
- The window sum over indices: for a duplicate-free `W`,
  `((List.range W.length).map (fun i => g (W.getD i 0))).sum = (W.map g).sum`
  (induction on `W`, or `List.map_getD_range`-style lemmas; an explicit induction with
  `List.range_succ_eq_map` is short).
- `lo.sum - lo.getD i 0 = Σ_{i' ≠ i} lo i'`: prove once, for a list and an index below its
  length, that `l.sum = l.getD i 0 + (sum of the others)` with the others listed by index.
- `Real.exp_sub`, `Real.exp_pos`; keep `field_simp` for the very end.
- If `W` is empty all of this degenerates gracefully; do not special-case it unless you
  must.

**If the statement is false as written, say so in your reply with the counterexample
instead of spending submissions.** You may submit partial files to see whether they
compile; they will FAIL at `Final.lean` but show Lean's errors for your part.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r8-kit/kd"

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
