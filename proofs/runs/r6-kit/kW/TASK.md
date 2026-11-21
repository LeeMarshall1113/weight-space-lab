# Task: prove a per-coordinate dot-product lemma for a Lean 4 lemma kit

This is framework work, not a test. Prove the two statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec pdot)` and
`open Lane4.RSoft Lane4.AGate`):

- `theorem ardot_near_w : ArdotNearW`
- `theorem closeL_of_close : CloseLOfClose`

and whatever helper lemmas you need. The checker builds one file from
`import Lane4.AGateAll` (AGateKit, AGate, RSoftKit, RSoft, RSeq, Seq, Basic, Mathlib),
then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**Background.** `AGateKit.lean` (copied here, read it first) already proves the uniform
form `ardot_near_abs` / `ardot_core`: one entry error `e` and one bound `X` for every
coordinate. Its proof is `ar_step` (one term), `ardot_aux` (induction over the lists with
a running partial sum, error and magnitude bound) and `ardot_core` (constants). The new
statement lets every coordinate have its own entry error `es[k] ≤ e` and bound
`Xs[k] ≤ X`; the main error term becomes `wErr δ r es Xs`, the sum over coordinates of
`|a_k| * es[k] + δ * (Xs[k] + es[k])`. The uniform `W`, `X`, `e` still bound everything and
are used for the rounding term `len * (W+1) * (X+e+1) / 2^16` and for the magnitude bound.

**Hints (you may ignore them). If a statement is false as written, say so in your reply
with the counterexample instead of spending submissions.**

- `ar_step` as stated uses the same `e`, `X` in the main error and in `T`. You need a
  version with a per-term `e'`, `X'` (`|v - vh| ≤ e'`, `|vh| ≤ X'`, `e' ≤ e`, `X' ≤ X`) whose
  error is `E + (|a| * e' + δ * (X' + e') + T / 65536 + η * 2097152)` with the same
  `T = (W + 1) * (X + e + 1)`. Copy the proof of `ar_step` and change the few lines where
  the main error is bounded; the magnitude and rounding parts are unchanged because
  `|v - vh| ≤ e` and `|vh| ≤ X` still hold.
- Then copy `ardot_aux` with `CloseL` in place of `Close` (you need the analogue of
  `close_cons` for `CloseL`: the heads satisfy the bounds and the tails are `CloseL`;
  `getD` over a `cons` shifts by one) and `wErr δ r es Xs` in place of
  `absSum r * e + len * δ * (X + e)`; then copy `ardot_core`.
- `0 ≤ es[k]` and `0 ≤ Xs[k]` follow from `CloseL` (they bound absolute values).
- `closeL_of_close`: `List.getD_replicate` or a direct argument with `List.getD` and
  `List.getElem_replicate`.
- You may submit partial files to see whether they compile; they will FAIL at
  `Final.lean` but show Lean's errors for your part.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r6-kit/kW"

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
