# Task: prove that a rational mirror computes the same output as a real-valued network definition

This is framework work, not a test. Prove the statement `QBridge` in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq` and `open Lane4.Seq (Mask cand tokAt)`):

- `theorem q_bridge : QBridge`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.RSeq`
(which imports Lane4.Seq, Lane4.Basic, Mathlib), then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`.

**Background.** `RSeq.lean` defines a small transformer over the reals with a rounding
function `fl : ℝ → ℝ` and a perturbation `p : Pert`: `sw`, `swRow`, `rdot`, `pdot`, `rmat`,
`raffine`, `radd`, `pos`, `Head.score`, `selOf`, `Head.sel`, `rsum`, `ravg`, `attnRows`,
`Head.attn`, `headsApply`, `Block.apply`, `TNet.init`, `runFrom`, `TNet.run`, `TNet.out`.
`Spec.lean` defines a mirror over ℚ (`qrdot`, `qrmat`, `qraffine`, `qradd`, `qpos`,
`qscore`, `qsel`, `qrsum`, `qavg`, `qattn`, `qheads`, `qblock`, `qinit`, `qrunFrom`,
`qout`) with `fl` removed and every perturbation 0. You must show the two agree when
`fl = fun x => x` and the perturbation is `pert0` (all zeros).

**Hints (you may ignore them).**

- State one lemma per definition, each saying "the real definition applied to casts is
  the cast of the rational definition", by induction on the lists with the accumulator
  and the index arguments generalised. For a vector use `x.map (fun q : ℚ => (q : ℝ))`.
  For example: `rdot (fun x => x) r (x.map Rat.cast) (fun _ => 0) j (acc : ℝ)
  = ((qrdot r x acc : ℚ) : ℝ)` (after `sw (fun x => x) a 0 = a` since `a * (1 + 0) = a`).
- `pdot` and `rdot` differ only in where the weights come from; `qscore` uses `qrdot` for
  both, so you need `pdot id (x.map cast) (y.map cast) acc = cast (qrdot x y acc)` too.
- States are functions `ℕ → Vec`; carry the invariant
  `∀ j, xR j = (xQ j).map Rat.cast` through the blocks.
- Selection: `selOf c s = qsel c s'` when `∀ k, s k = (s' k : ℝ)`, because the cast
  preserves `≤` (`Rat.cast_le`); `List.filter_congr` plus `decide_eq_decide`.
- `relu x = max x 0` (`Lane4.relu`), and `Rat.cast_max`.
- Casts: `push_cast`, `Rat.cast_add`, `Rat.cast_mul`, `Rat.cast_div`, `Rat.cast_natCast`.
- Position features: `pos (fun x => x) i n = (qpos i n).map Rat.cast` by `simp`.
- You may submit partial files (lemmas only) to see whether they compile; they will FAIL
  at `Final.lean` but show Lean's errors for your part.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r5-kit/kQ"

  It prints PASS or FAIL with Lean's output. You have **25 submissions**; stop at the
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
