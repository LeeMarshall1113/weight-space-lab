# Task: write a branching program and prove it correct

Write a Lean 4 function that computes this function exactly using only `if … then … else`,
comparisons (`≤`, `<`) and arithmetic, and a Lean 4 proof that it equals the spec at every
real point of the box.

**Function** (1 input):

    spec(x0) = max (|(-1) * x0 + (-1)|) (max (min ((-2) * x0) ((-2) * x0 + (-3/2))) (min (max ((-2) * x0) ((-2) * x0 + (-3/2))) ((-1/2) * x0 + (-1))))

(`max a b`, `min a b` and `|a|` have their usual meaning.)

**Box:** -8 ≤ x0 ≤ 2

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `noncomputable def prog (x0 : ℝ) : ℝ`. The program part of the file (everything
  above a line that reads exactly `-- PROOF`) must not use `max`, `min`, `abs`, `|…|`,
  `relu`, `⊔`, `⊓` or `spec`. Helper `def`s are allowed above the marker.
- Then the line `-- PROOF`, and below it only lemmas and
  `theorem prog_correct : StatementProg prog`, where `StatementProg` is in `Spec.lean`.

## Rules

- Write exactly one file in this folder: `Solution.lean`. Do not edit any other file here
  and do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.Basic`, then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
  Read `Basic.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.
- Helper files (Python scripts, notes) go only in the `scratch/` sub-folder of this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8 (it contains characters such as
  `ℝ` and `≤`); do not patch it with shell one-liners.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/rung3-test/prog/p119"

  It prints PASS or FAIL with Lean's output. You have **12 submissions**; the
  episode ends at the first PASS. A submission can take a few minutes (it may
  also sit in a queue; just wait, never resubmit while one is pending).
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start
  other agents, or kill processes. You may run short Python (standard library or
  numpy) to test numbers before you submit.
- Banned in `Solution.lean` (the checker rejects the file without running Lean, and it
  still costs a submission): `sorry`, `admit`, `axiom`, `native_decide`, `macro`,
  `syntax`, `notation`, `elab`, `instance`, `opaque`, `unsafe`, `import`, `#eval`,
  anything in the `Lean.` namespace.
- The proof must be accepted by Lean's kernel using only the standard axioms.
- Each check is limited to 600 s and 4.5 GB of memory. Very long generated proofs
  (thousands of lines) run out of memory; keep the proof compact.
- Lean 4 with Mathlib (the real numbers and `Mathlib.Tactic` are imported; see `Basic.lean`).
  `set_option maxHeartbeats N in` before a theorem is allowed.

## When you finish

Reply with: PASS or FAIL, the number of submissions used, and three or four sentences on
how you built it and what went wrong along the way. If you give up, say why.
