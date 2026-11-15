# Task: write a SOFTMAX transformer's weights and prove it correct for every length, every nearby weight setting and floating-point arithmetic

Write the weights of a small softmax-attention transformer, in the fixed architecture of
`RSoft.lean`, that solves the task below, and a Lean 4 proof of `Statement` in `Spec.lean`.

**Task.** Tokens are 1..5. Marked tokens carry a bit a: 1 ↦ 0, 2 ↦ 0, 3 ↦ 1, 4 ↦ 1; the other tokens are unmarked. Every token also has a bit c: 1 ↦ 0, 2 ↦ 1, 3 ↦ 1, 4 ↦ 1, 5 ↦ 0. Let A_i be the bit a of the FIRST marked token among positions 1..i (position i included), and 0 if there is none. The target at position i (1 ≤ i ≤ length) is (A_i + c(token i)) mod 2. (In `Spec.lean`, `code` is 0 for an unmarked token, 1 for a marked token with a = 0, 2 for a marked token with a = 1.)

**What the statement says.** For every rounding function `fl` satisfying `Rnd u η M fl`
(relative error `u ≤ 2^-24` plus an underflow term `η ≤ 2^-149`, guaranteed ONLY for
arguments of absolute value at most `M`), every float exponential `ex` satisfying
`ExpM u η ex`, every relative perturbation of every weight by at most 1/200 (weight `w`
becomes `fl (w * (1 + d))`, `|d| ≤ 1/200`), and every input `w` whose number of positions
`n = length + 1` satisfies `u * n ≤ 1/256`, `η * n ≤ 1/2^100` and `2^40 * n^2 ≤ M`: at
every position `i` in 1..length the output is within 1/4 of the target. `Final.lean`
then derives two corollaries from your theorem (you do not prove them): exact arithmetic
at EVERY length, and IEEE binary32 arithmetic up to 65,535 tokens. One proof must cover
both, so it has to work from the `Rnd` and `ExpM` axioms.

**Architecture (fixed; read the header of `RSoft.lean`, and `RSeq.lean` for the parts it
reuses).** Written weights are rationals. A BOS token (token 0) is put at position 0, so
your input occupies positions 1..length. Each position starts with its token's stored
embedding row followed by three position features `[1, fl i, fl n]`. Attention is
SOFTMAX over the candidate positions (masks: all, causal `j ≤ i`, strict `j < i`), computed
as `ex (fl (score - max score))`, summed and divided, every step rounded. Each block is
heads plus a one-hidden-layer ReLU MLP, both residual. Limits: at most 4 blocks, 4 heads
per block, state width (embedding width + 3) at most 24, MLP hidden width at most 32.

**The two softmax lemmas** (end of `RSoftKit.lean`):

- `soft_near`: if one candidate `j` beats every other candidate `k` by a score gap of at
  least `16 * |j - k|` (`ndist j k`), the head's output is within `B / 100 + 1/2^90` of
  `j`'s value, where `B` bounds the values. So a selecting score needs a slope of at
  least 16 per position, after perturbation and rounding.
- `soft_zeros`: if every candidate's value is exactly 0, the output is exactly 0.

**Advice.** A weight written as 0 stays exactly 0, and sums and products of exact zeros
are exactly 0; nothing else is exact. Two stored weights written with the same value are
in general NOT equal. A score that must separate positions has to do so with a margin
that the perturbation (relative size 1/200, and it multiplies large position features)
cannot close. `Rnd` gives nothing outside `[-M, M]`: every kit lemma that touches `fl x`
asks for `|x| ≤ B` and `B ≤ M`, and `fl (fl x) = fl x` (`Rnd.idem`) needs `|x| ≤ M`; get
these from `range_const`, `range_lin`, `range_quad`. Small target values and few layers
keep the error bounds easy. Read `EXAMPLE.lean` closely: it shows the whole pattern on a
one-head network.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case` (with
`open Lane4.RSeq Lane4.RSoft` and `open Lane4.Seq (Mask cand tokAt)`):

- `def net : TNet` with 5 real tokens, so `6` embedding rows (row 0 is BOS).
- `theorem net_ok : Statement net`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep every helper file you create (scripts, notes) inside the `scratch/`
  sub-folder of this folder, and nowhere else. Do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.RSoftAll` (RSoftKit, RSoft, RSeq, Seq, Basic, and the binary32 file
  used only by `Final.lean`), then `Spec.lean`, then
  your `Solution.lean`, then `Final.lean`.
  Read `RSoft.lean`, the end of `RSoftKit.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean`
  first; `RSeq.lean` and `Seq.lean` hold the definitions and the mask, candidate-list and
  token lemmas that `RSoft.lean` reuses. Long linter warnings can push errors out of the
  shown output; `set_option linter.unusedVariables false` and similar at the top help.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/rung5-test/net/f28"

  It prints PASS or FAIL with Lean's output. You have **12 submissions**; the episode
  ends at the first PASS. A check can take up to 10 minutes and may also wait in a queue.
  Wait for it. Never resubmit while one is pending, and do not report until your last
  submission has returned.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. You may run short Python (standard library or numpy) to test
  ideas before you submit.
- Banned in `Solution.lean` (the checker rejects the file without running Lean, and it
  still costs a submission): `sorry`, `admit`, `axiom`, `native_decide`, `macro`,
  `syntax`, `notation`, `elab`, `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`,
  anything in the `Lean.` namespace.
- The proof must be accepted by Lean's kernel using only the standard axioms, and it must
  hold for input lists of EVERY length. Testing finitely many lengths proves nothing here.
- Each check is limited to 600 s and 4.5 GB of memory.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.

## When you finish

Reply with: PASS or FAIL, the number of submissions used, and three or four sentences on
how you built it and what went wrong along the way. If you give up, say why.
