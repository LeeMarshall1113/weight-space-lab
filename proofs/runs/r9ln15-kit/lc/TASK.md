# Task: repair a ported proof (the head lemma)

This is framework work, not a test. Prove the one statement `Lane4.LNC.HeadSoundLN`
(`LNDefs.lean`, section "lb, lc").

**What to write.** `Solution.lean` in this folder ALREADY EXISTS: it is a draft made by text
substitution from the proved rung-8 file `R8KG.lean` (copied here). Edit it until it compiles.
It must contain, inside `namespace Lane4.Case`:

- `theorem head_sound_ln : HeadSoundLN`

The checker builds one file from `import Lane4.LNB2` (the proved modules `LNKA.lean` and
`LNKB.lean`, and through them LNDefs, LNCert, LNNet, R8All, Mathlib), then `Spec.lean`
(empty), then your `Solution.lean`, then `Final.lean`.

**What changed against rung 8.** `HeadSoundLN` is `Lane4.R8KG.HeadSound8` with `headOKLN` in
place of `headOK8`. `headOKLN` (`LNCert.lean`) is `headOK8` (`R8Cert.lean`) conjunct for
conjunct, in the same order, with four functions replaced:

    scoreIV → scoreRel      matIV → matRel      valBound → valBoundR      scoreOK → scoreOKR

`matRel δ M x = M.map (fun r => dotRel δ r x)` and `valBoundR δ E h cd = h.V.map (bfRel δ E cd)`,
where `bfRel` is rung 7's `Lane4.R7K3.hs_Bf` with `dotRel` in place of `dotIV`. The lemmas
that changed name: a value entry lies in its table entry by
`Lane4.LNKA.dot_rel_sound : DotRelSound` (same hypotheses and conclusion as rung 7's
`dot_sound`, with `dotRel`); scores by `Lane4.LNKB.score_win_ln : ScoreWinLN` (same as
`Lane4.R8KA.score_win` with `headOKLN`). The draft already has these substitutions and two
ported helper lemmas at its top (`bfRel_nonneg`, `bfRel_ge`). Nothing else in the argument
changes: the proof never looks inside `dotIV` or `scoreIV`.

**How to work.** Submit the draft as it is first; fix only what Lean reports. Do not
restructure the proof. Lemmas of the imported rung-8 modules are still available under
their namespaces (`Lane4.R8KA.k_getD_map`, `Lane4.R7K3.hs_...`, ...).

**If the statement is false as written, say so in your reply with the exact place instead of
spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/lc"

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
