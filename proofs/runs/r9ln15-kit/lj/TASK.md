# Task: the trained LayerNorm network as a point of the ball

This is framework work, not a test. Prove the two statements `Lane4.LNT.OutShiftL` and
`Lane4.LNT.DiffWithinL` (file `LNT.lean`).

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec)`,
`open Lane4.RSoft Lane4.AGate Lane4.LN Lane4.R7KT Lane4.LNT` and
`open Lane4.Seq (Mask cand tokAt)`):

- `theorem out_shift_l : OutShiftL`
- `theorem diff_within_l : DiffWithinL`

The checker builds one file from `import Lane4.LNT` (which imports LNCert, LNNet, R8All and
with it `Lane4.R7KT`, Mathlib), then `Spec.lean` (empty), then your `Solution.lean`, then
`Final.lean`.

**Background.** `R7KT.lean` (copied here) is the PROVED version of both statements for
networks without LayerNorm (`out_shift : OutShift`, `diff_within : DiffWithin`), with general
helper lemmas that are imported and usable as `Lane4.R7KT.<name>`: `kt_sameShape_parts`,
`kt_asw_congr`, `kt_aswRow_gen`, `kt_ardot_gen`, `kt_araffine_gen`, `kt_aheadsApply_gen`,
`kt_attn_diff`, `kt_init_diff`, `kt_mr_diff`, `kt_dq_hyp`, `kt_block_eq`, `kt_nearL_abs`, ...
Read how `out_shift` and `diff_within` use them. `LNNet.lean` has the network:
`LNNet.out` matches on `N.net.blocks = [B]` and is
`N.read (N.post B (N.mid B ...))` with `lnorm`, `lnScale`, `lnCentre`, `lnSigma`.
`LNT.lean`: `diffPL`, `zeroPL`, `sameShapeL`, `nearNetL`.

**The mathematics.** `asw fl w d = fl (w + d)`, and with `d = t - w` (the entry of `diffPL`)
this is `fl t = asw fl t 0`. So every stored weight of `W` under `diffPL W T` equals the
stored weight of `T` under `zeroPL`, and the two evaluations are the same expression.
- `lnScale fl s c g b dg db k`: by induction over the three lists, equal for `(g, b, dq g g', dq b b')`
  and `(g', b', 0, 0)` when `g.length = g'.length`, `b.length = b'.length` (index `k` general;
  `dq a b c = ((b.getD c 0 - a.getD c 0 : ℚ) : ℝ)`; mind the index shift as in `kt_aswRow_gen`).
  `lnCentre` and `lnSigma` do not involve weights.
- The pieces of `LNNet.out`: `N.net.init` (`kt_init_diff`), the heads
  (`kt_aheadsApply_gen` / the argument inside `kt_block_eq`, applied to the state function
  `N.hid ...`, which is the same function for both networks once `lnorm` agrees),
  `araffine` for W1 and W2 (`kt_araffine_gen`), `ardot` and `asw` for the read-out. Both
  networks have exactly one block or both have another number (same shape), so the `match`
  in `LNNet.out` takes the same branch.
- `DiffWithinL`: the `a` field is `diff_within`; each LayerNorm field is `kt_nearL_abs` (or
  its argument) for one list.

**Hints.** Submit after `diff_within_l` (the short one), then build `out_shift_l` piece by
piece. **If a statement is false as written, say so with the exact place instead of spending
submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/lj"

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
