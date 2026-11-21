# Task: the softmax lemma at a score gap of 12 per position

This is framework work, not a test. Prove the statement in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq Lane4.RSoft`):

- `theorem savg_near12 : SavgNear12`

and whatever helper lemmas you need. The checker builds one file from
`import Lane4.RSoftKit` (RSoft, RSeq, Seq, Basic, Mathlib), then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`.

**Background.** `RSoftKit.lean` (copied here, read it first; `RSoft.lean` and `RSeq.lean`
are here too for the definitions) already proves `SavgNear`: softmax attention with a
clear winner returns the winner's value up to `B / 100 + 1 / 2^90`, when the winner beats
every other candidate by a score gap of at least **16** per unit of distance. `SavgNear12`
is the same statement, word for word, with the gap **12** in place of 16 and the same
error bound. Everything in `RSoftKit.lean` is imported and may be used: `rsum_err`,
`geom_dist`, `div_step`, `sum_split`, `abs_sum_le_aff`, and the rest.

**Hints (you may ignore them). If the statement is false as written, say so in your reply
with the counterexample instead of spending submissions.**

- The existing proof `savg_near` (in `RSoftKit.lean`, from the line
  `theorem savg_near : RsumErr → GeomDist → SavgNear`) is the model. It uses the gap 16
  through `exp_neg15_le : Real.exp (-15) ≤ 1 / 10 ^ 6` (one unit of the gap is spent on
  rounding of the scores). With gap 12 the corresponding fact is about `Real.exp (-11)`,
  which is about `1.67e-5`: for example `Real.exp (-11) ≤ 1 / 10 ^ 4` (since
  `(1 + 11/100)^100 > 10^4`), proved the same way as `exp_neg15_le`. The geometric sum
  then gives at most `4 * q` with `q` of that size, still far below the `4 / 1000` that
  `div_step` needs, so the same final bound should go through; check each numeric step
  of the old proof where `10 ^ 6` or 15 or 16 appears and redo it with the new numbers.
- Copying the old proof into your file and editing it is allowed and expected. Its
  private helper lemmas are already available by name; do not restate them under the
  same names.
- You may submit partial files to see whether they compile; they will FAIL at
  `Final.lean` but show Lean's errors for your part.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r7-kit/k1"

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
