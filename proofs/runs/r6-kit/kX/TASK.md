# Task: write the worked example for a new framework (a gated softmax transformer under ADDITIVE weight perturbation)

This is framework work, not a test: your solution becomes the worked example that later
agents are given. Write the weights of a small network in the architecture of
`AGate.lean` that outputs the PREVIOUS token (tokens are 1 and 2; the token before
position 1 is BOS = 0), and a Lean 4 proof of `Statement` in `Spec.lean`. Make the proof
clean and well commented, organised as reusable steps, because others will learn the
method from it.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec)`, `open Lane4.RSoft Lane4.AGate`
and `open Lane4.Seq (Mask cand tokAt)`):

- `def net : ANet` with 2 real tokens (3 embedding rows; row 0 is BOS);
- `theorem net_ok : Statement net`.

The checker builds one file from `import Lane4.AGateAll` (AGateKit, AGate, RSoftKit, RSoft,
RSeq, Seq, Basic, the binary32 file, Mathlib), then `Spec.lean`, then your `Solution.lean`,
then `Final.lean` (which derives two corollaries from your theorem and checks the shape).

**The architecture and the statement (read the header of `AGate.lean`).** The state at a
position is ONLY the stored embedding row of its token; there are no position features.
Positions enter through a score bias `fl (m' * (j - i))` with a slope `m` per head. Each
head has a gate neuron on the keys: key `j` is a candidate iff the mask allows it and
`relu (fl (g' · x_j + gb')) = 0` exactly. Attention is softmax over the candidates (the
rung-5 `savg`). Every weight `w` is used as `asw fl w d = fl (w + d)` with `|d| ≤ 1/1000`,
one `d` per weight, INCLUDING weights written as 0, gate weights, the gate bias and the
slope. So nothing is exactly zero and closed forms by `simp` are not available. The
method is: an IDEAL value plus an error bound.

**A design that should work (check it yourself).** Embedding rows `[val, res, one]`:
BOS `[0, 0, 1]`, token 1 `[1, 0, 1]`, token 2 `[2, 0, 1]`. One head, mask `strict`, slope
`m = 24`, score matrix `A` all zeros (3 by 3), value matrix `V` with row 1 = `[1, 0, 0]`
(copy `val` into `res`), gate weights `g = [0, 0, 0]` and gate bias `gb = -1` (so every
key has pre-activation about -1 and gate exactly 0: all keys are candidates). No MLP
(`W1 = []`, `b1 = []`, `W2 = [[], [], []]`, `b2 = [0, 0, 0]`). Read-out `outW = [0, 1, 0]`,
`outB = 0`. The previous position `i - 1` wins by about 24 per position minus the content
noise (the perturbed zero score matrix contributes at most about 9 entries times 1/1000
times products of state entries, each at most about 2), which leaves well over the
`16 * |j - k|` gap that `soft_near` needs.

**Lemmas to use.**
- `AGate.lean`: `asw_near`, `asw_bound`, `fl_asw`, `relu_fl_zero`, `AHead.mem_cands`,
  `AHead.cands_nodup`.
- `AGateKit.lean` (statements at the top, as `def ... : Prop`; theorems `ardot_near`,
  `pdot_near`, `bias_gap` prove them): approximate dot products with an ideal value
  (`dotQ`, `dotR`, `Close`) and the position-bias gap. Each gives an error bound and a
  magnitude bound.
- `RSoftKit.lean` (end of file): `soft_near` (a winner with score gap at least
  `16 * ndist j k` over every other candidate gets its value returned within
  `B/100 + 1/2^90`, and the result is unchanged by rounding again) and `soft_zeros`.
- `RSoft.lean`: `Rnd.abs`, `Rnd.near`, `Rnd.bound`, `Rnd.gap`, `mul_near`, `range_const`,
  `range_lin`, `range_quad`, `eta_tiny`, `ndist_cast`.
- `scratch/rung5_example_for_reference.lean` is the worked example of the PREVIOUS
  framework (relative perturbation, position features in the state). Its overall shape
  (range facts, score gap, `soft_near`, error chain) carries over; its closed forms by
  `simp` do not, because here zeros are perturbed.

**Suggested organisation.**
1. Ideal states: the starting state at position `j` is `Close` to the ideal row
   `[tok, 0, 1]` with error `e0 = 1/1000 + tiny` (from `asw_near` on each entry).
2. The gate: every key's pre-activation is at most `-1/2`, so the gate is exactly 0 and
   the candidates are exactly the mask's positions (`AHead.mem_cands`, `relu_fl_zero`).
3. Scores: `score = fl (bias + content)`, with `|content| ≤` a small constant (by
   `ardot_near` for each row of `A` then `pdot_near`), so the gap between key `i-1` and
   any earlier key `k` is at least `(24 - 1/1000) * (i-1-k) - small ≥ 16 * (i-1-k)`
   (`bias_gap`, `Rnd.gap`).
4. Values: `V_r · x_j` within a small error of the ideal (`ardot_near`); row 1's ideal is
   the token at `j`; rows 0 and 2 have ideal 0.
5. `soft_near` for each of the three rows (each row's values are bounded and the winner
   is `i-1`), giving the head output within a small error of `[0, tok(i-1), 0]`.
6. Residual add, the empty MLP (`araffine` with `W1 = []` gives `[]`; `W2` rows are empty
   so each output is `fl (0 + asw 0 d)`, a number of size at most about 1/1000), the
   read-out by `ardot_near` again, and the final error budget, well under 1/4.

State sizes are tiny here (width 3), so unfolding `aattnRows`, `aheadsApply`,
`ABlock.apply`, `arunFrom` by `simp only` with the concrete lists is fine; just keep the
perturbed quantities abstract (do not try to simplify `asw fl 0 d` to 0: it is not 0).

You may submit partial files (a prefix of the proof with a final dummy that fails) to see
Lean's errors. Long linter warnings can push errors out of the shown output: put
`set_option linter.unusedVariables false`, `set_option linter.unusedSimpArgs false` and
`set_option linter.deprecated false` at the top.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r6-kit/kX"

  It prints PASS or FAIL with Lean's output. You have **30 submissions**; stop at the
  first PASS. A check can take up to 10 minutes and may also wait in a queue. Wait for
  it. Never resubmit while one is pending. You may submit a file that proves only part
  (leave the other theorem out) to see Lean's errors; it will FAIL at `Final.lean` but
  show whether your part compiles.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. Short Python for arithmetic is fine.
- Banned in `Solution.lean` (rejected without running Lean, still costs a submission):
  `sorry`, `admit`, `axiom`, `native_decide`, `macro`, `syntax`, `notation`, `elab`,
  `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`, anything in the `Lean.`
  namespace.
- Standard axioms only. Each check is limited to 600 s and 4.5 GB.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.
  Long linter warnings can push errors out of the shown output; if that happens put
  `set_option linter.unusedVariables false` and similar at the top of your file.

## When you finish

Reply with PASS or FAIL, the number of submissions used, and three or four sentences on
how you proved it and what went wrong. If you give up, say why and what is left.
