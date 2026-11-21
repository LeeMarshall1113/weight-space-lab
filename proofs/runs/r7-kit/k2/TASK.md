# Task: the interval evaluator is sound, piece by piece

This is framework work, not a test. Prove the eight statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and `open Lane4.RSoft Lane4.AGate Lane4.Cert`):

- `theorem emb_sound : EmbSound`
- `theorem dot_sound : DotSound`
- `theorem mat_sound : MatSound`
- `theorem aff_sound : AffSound`
- `theorem add_sound : AddSound`
- `theorem relu_sound : ReluSound`
- `theorem gate_sound : GateSound`
- `theorem score_sound : ScoreSound`

and whatever helper lemmas you need. The checker builds one file from
`import Lane4.R7Cert` (which imports AGateAll: AGateKitW, AGateKit, AGate, RSoftKit, RSoft,
RSeq, Seq, Basic, Mathlib), then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**Background.** `R7Cert.lean` (copied here, read it first) defines a computable evaluator
over rationals: an interval is `IV = ℚ × ℚ` (centre, radius), and `embIV`, `dotIV`,
`matIV`, `affIV`, `addIV`, `reluIV`, `gateDec`, `scoreIV` push intervals through the
operations of the network of `AGate.lean` (copied here: `asw`, `aswRow`, `ardot`, `armat`,
`araffine`, `AHead.gate`; `pdot` and `radd` are in `RSeq.lean`). `Spec.lean` defines what
it means for reals to lie in intervals (`InIV`, `InIVs`), a size bound (`Bdd`), the
hypothesis bundle `Ctx`, and one soundness statement per operation: the real, rounded,
perturbed operation applied to reals inside the input intervals lands inside the output
interval. `δ` is a rational perturbation radius with `0 ≤ δ ≤ 1/2`; every perturbation
function is bounded by `δ` everywhere.

The error terms of the evaluator were chosen to be exactly the bounds of these kit
lemmas, which are imported and are the intended tools:

- `asw_near` (AGate.lean): a stored weight is within `δ + (u * (|w| + δ) + η)` of the
  written weight. With `|w| ≤ 15`, `δ ≤ 1/2`, `u ≤ 2^-24`, `η ≤ 2^-149` that is at most
  `δ + 2^-20 = e0 δ`.
- `ardot_near_w` (AGateKitW.lean, statement `ArdotNearW`): a stored-weight dot product
  against a vector known entry by entry (`CloseL x xh es Xs`): error
  `wErr δ r es Xs + len * (W + 1) * (X + e + 1) / 2^16 + 1/2^100`. `dotIV` is this bound
  with `xh` the centres, `es` the radii, `Xs` the absolute centres, `W = maxAbs r`,
  `X = maxAbs` of the centres, `e = maxAbs` of the radii. Its range hypothesis
  `(W + 1) * (X + e + 1) ≤ 2^20` follows from `smallQ r` (so `W ≤ 15`) and `Bdd 16 xv`.
- `pdot_near` (AGateKit.lean, statement `PdotNear`): the same for `pdot` with uniform
  `Close`; `scoreIV` is its bound, and `scoreOK` contains its range hypothesis.
- `Rnd.near`, `Rnd.abs`, `Rnd.bound`, `Rnd.nonpos`, `Rnd.nonneg` (RSoft.lean) for single
  roundings: a quantity of absolute value at most 15 is moved by at most
  `u * 15 + η ≤ 2^-20 = rnd`. The guard `small v` (|centre| + radius ≤ 15) is what gives
  the size bound; the radius of every rounded output already includes `rnd`.

**Hints (you may ignore them). If a statement is false as written, say so in your reply
with the counterexample instead of spending submissions.**

- Start with small bridge lemmas between the rational side and the real side:
  `qabs a` cast to ℝ is `|(a : ℝ)|`; `maxAbs l` bounds `qabs` of every member and is
  non-negative (induction on the list, generalising the fold's accumulator); the cast of
  `dotC r xv` is `dotQ r (centres)`; the cast of `wErrQ δ r xv` is `wErr δ r radii
  abscentres`; `InIVs x xv` with these lists is `CloseL`. `push_cast` and `Rat.cast_le`
  move inequalities between ℚ and ℝ; `decide_eq_true_eq` and `Bool.and_eq_true` open the
  Boolean guards; `List.all_eq_true` opens `.all`.
- `dot_sound` first; `mat_sound` and `aff_sound` are inductions on the rows with the row
  index generalised (the definitions recurse with `i + 1`, so prove the statement for an
  arbitrary start index and specialise to 0); `gate_sound` is `dot_sound` plus one
  rounding and a sign argument (`Lane4.relu x = max x 0`, defined in `Basic.lean`, copied
  here: it is 0 exactly when its argument is ≤ 0).
- For `affIV` and `addIV` the evaluator uses `List.zipWith`, and the real operations
  recurse on both lists and stop at the shorter one, the same way.
- In `score_sound`, `x.length = y.length` for `pdot_near` comes from
  `(armat fl A xt dA 0).length = A.length` (prove by induction) and `h.A.length = xq.length`.
- The eight statements are independent of each other except that later ones use
  `dot_sound` and `mat_sound`. You may submit a partial file (some theorems missing) to
  see whether what you have compiles; it will FAIL at `Final.lean` but shows Lean's errors
  for your part. Build the file up in that order rather than writing everything first.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r7-kit/k2"

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
