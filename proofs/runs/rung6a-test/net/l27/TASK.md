# Task: write a GATED softmax transformer's weights and prove it correct for every length under ADDITIVE perturbation of every weight

Write the weights of a small transformer in the fixed architecture of `AGate.lean` that
solves the task below, and a Lean 4 proof of `Statement` in `Spec.lean`.

**Task.** Tokens are 1..5. Marked tokens carry a value: 1 ↦ 3, 2 ↦ 1, 3 ↦ 3; the other tokens are unmarked. The target at position i (1 ≤ i ≤ length) is the value of the LAST marked token among positions 1..i (position i included), and 0 if there is none.

**What the statement says.** For every rounding function `fl` with `Rnd u η M fl`, every
float exponential `ex` with `ExpM u η ex`, every ADDITIVE perturbation of every weight by
at most 1/1000 (a written weight `w` is used as `asw fl w d = fl (w + d)`, `|d| ≤ 1/1000`,
one `d` per weight, INCLUDING weights written as 0, gate weights, gate biases and slopes),
and every input whose number of positions `n = length + 1` satisfies `u * n ≤ 1/256`,
`η * n ≤ 1/2^100` and `2^40 * n^2 ≤ M`: at every position `i` in 1..length the output is
within 1/4 of the target. `Final.lean` then derives two corollaries (you do not prove
them): exact arithmetic at EVERY length, and IEEE binary32 up to 65,535 tokens.

**Architecture (fixed; read the header of `AGate.lean`).** Written weights are rationals.
A BOS token (token 0) is put at position 0. The state at a position is ONLY the stored
embedding row of its token: there are NO position features. Positions enter through a
score bias `fl (m' * (j - i))` with one slope `m` per head. Each head has a gate neuron
on the keys: key `j` is a candidate for query `i` iff the mask allows it (all, causal
`j ≤ i`, strict `j < i`) and `relu (fl (g' · x_j + gb')) = 0` exactly. Attention is softmax
over the candidates. Each block is heads plus a one-hidden-layer ReLU MLP, both residual.
With no candidate a head's output is 0. Limits: at most 4 blocks, 4 heads per block,
state width at most 24, MLP hidden width at most 32, slopes between 1 and 1024.

**Method: an ideal value plus an error bound.** Nothing is exactly zero here, so closed
forms by `simp` are not available. Reason about each quantity as an IDEAL value (written
weights, no perturbation, no rounding) plus an error:
- `AGateKit.lean`: `ardot_near_abs` and `ardot_near` (a stored-weight dot product is close
  to the ideal dot product `dotQ`; `Close x xh e X` says a vector is within `e` of its
  ideal), `pdot_near` (the same for two real vectors), `bias_gap` (an earlier key is
  behind a later one by at least `(m - δ)` per position, up to a small slack).
- `AGateKitW.lean` (end of file): `ardot_near_w`, the per-coordinate form: each
  coordinate has its own entry error and bound (`CloseL`, `wErr`). Use it when the
  state is wide: the uniform lemmas charge `len * δ * (X + e)` with the largest `X`
  and `e` and can exceed the 1/4 budget on their own.
- `AGate.lean`: `asw_near`, `asw_bound`, `fl_asw`, `relu_fl_zero` (a gate with a
  non-positive pre-activation is exactly 0), `AHead.mem_cands`, `AHead.cands_nodup`.
- `RSoftKit.lean` (end of file): `soft_near` (a candidate that beats every other
  candidate by a score gap of at least `16 * |j - k|` gets its value returned within
  `B/100 + 1/2^90`), `soft_zeros`.
- `RSoft.lean`: `Rnd.abs`, `Rnd.near`, `Rnd.bound`, `Rnd.gap`, `mul_near`, `range_const`,
  `range_lin`, `range_quad`, `eta_tiny`, `ndist_cast`.

**What your proof must cover.**
1. The gate: after perturbing the embedding and ALL gate parameters, every key you want
   as a candidate has a non-positive pre-activation (gate exactly 0), and every key you
   want removed has a positive gate.
2. BOS and the empty case: say whether the candidate list can be empty for a position
   `i ≥ 1`, and prove the output in that case.
3. The content part of the score (score matrix times states) is bounded by a small
   constant, uniformly in length.
4. The winner beats every other candidate by at least `16 * |j - k|` after the slope
   perturbation, the content noise and the rounding.
5. Every argument of `fl` is within the range `M` (each kit lemma asks for it).
6. The final error is at most 1/4.

**Advice.** A gate that is exactly 0 on the wanted keys survives additive noise only if
its pre-activation has a margin (for example a bias of -1/2 against a flag of 0 or 1).
A state entry produced by an earlier layer is only approximately its ideal value; if a
later gate must be exactly 0 on it, give that gate a margin too. Keep written weights
and state values small: every bound scales with them. Read `EXAMPLE.lean` closely.
The checker is your only compiler: submit early and in parts (helper lemmas first; a
partial file FAILS at `Final.lean` but shows Lean's errors for your part). Stopping
with unused submissions counts as a FAIL, the same as using all of them.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case` (with
`open Lane4.RSeq (Vec)`, `open Lane4.RSoft Lane4.AGate` and
`open Lane4.Seq (Mask cand tokAt)`):

- `def net : ANet` with 5 real tokens, so `6` embedding rows (row 0 is BOS).
- `theorem net_ok : Statement net`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep every helper file you create (scripts, notes) inside the `scratch/`
  sub-folder of this folder, and nowhere else. Do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.AGateAll` (AGateKitW, AGateKit, AGate, RSoftKit, RSoft, RSeq, Seq, Basic, and the
  binary32 file used only by `Final.lean`), then `Spec.lean`, then
  your `Solution.lean`, then `Final.lean`.
  Read `AGate.lean`, `AGateKit.lean`, the end of `AGateKitW.lean`, the end of `RSoftKit.lean`, `Spec.lean`, `Final.lean`
  and `EXAMPLE.lean` first. Long linter warnings can push errors out of the shown
  output; put `set_option linter.unusedVariables false`, `linter.unusedSimpArgs false`
  and `linter.deprecated false` at the top of your file.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/rung6a-test/net/l27"

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
