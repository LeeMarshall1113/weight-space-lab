# Task: write a one-pass program and prove it correct for every input length

Write a plain Lean 4 function that solves the task below in a single left-to-right pass,
and a Lean 4 proof that it is correct for input lists of every length.

**Task.** Tokens are 1..4. The input is ACCEPTED exactly when the number of tokens that lie in {2, 3} is odd.

The exact statement to prove is `StatementProg` in `Spec.lean`.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `def prog : List ℕ → Bool`. The program part of the file (everything above a line that reads
  exactly `-- PROOF`) must do its work with `List.foldl` and an explicit step function
  (one pass). It must not use library counting, summing, slicing, filtering or sorting
  (`countP`, `count`, `sum`, `take`, `drop`, `filter`, `mergeSort`, `sort`, ...) and must
  not mention the spec's own definitions. Helper `def`s are allowed above the marker.
- Then the line `-- PROOF`, and below it only lemmas and
  `theorem prog_correct : StatementProg prog`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep every helper file you create (scripts, notes) inside the `scratch/`
  sub-folder of this folder, and nowhere else. Do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.Seq`, then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
  Read `Seq.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/rung2-test/prog/p29"

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
