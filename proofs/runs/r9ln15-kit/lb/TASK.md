# Task: repair a ported proof (scores of candidate keys against the certificate's table)

This is framework work, not a test. Prove the one statement `Lane4.LNC.ScoreWinLN`
(`LNDefs.lean`, section "lb, lc").

**What to write.** `Solution.lean` in this folder ALREADY EXISTS: it is a draft made by text
substitution from the proved rung-8 file `R8KA.lean` (copied here). Edit it until it compiles.
It must contain, inside `namespace Lane4.Case`:

- `theorem score_win_ln : ScoreWinLN`

The checker builds one file from `import Lane4.LNKA` (the proved module `LNKA.lean`, which
imports LNDefs, LNCert, LNNet, R8All, Mathlib), then `Spec.lean` (empty), then your
`Solution.lean`, then `Final.lean`.

**What changed against rung 8.** `ScoreWinLN` is `Lane4.R8KA.ScoreWin` with `headOKLN` in
place of `headOK8`. `headOKLN` (`LNCert.lean`) is `headOK8` (`R8Cert.lean`) conjunct for
conjunct, in the same order, with four functions replaced:

    scoreIV → scoreRel      matIV → matRel      valBound → valBoundR      scoreOK → scoreOKR

and the lemma that the content score lies in its table entry is now
`Lane4.LNKA.score_rel_sound : ScoreRelSound` (statement in `LNDefs.lean`, section "la"),
which has the same hypotheses and conclusion as rung 7's `Lane4.R7K2.score_sound` with
`scoreOKR`, `scoreRel` in place of `scoreOK`, `scoreIV`. The draft already has these
substitutions. Nothing else in the argument changes: the proof never looks inside `scoreIV`.

**How to work.** Submit the draft as it is first; fix only what Lean reports (most likely:
a `simp`/`obtain` pattern in `k_open` that depended on the old names, or a name clash with
the lemmas of the imported `Lane4.R8KA`, which are still imported under that namespace and
can simply be reused, e.g. `Lane4.R8KA.k_getD_map`). Do not restructure the proof.

**If the statement is false as written, say so in your reply with the exact place instead of
spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/lb"

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
