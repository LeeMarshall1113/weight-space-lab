# Task: write a ReLU network and prove it correct

Write the weights of a small ReLU multi-layer perceptron that computes this function
exactly, and a Lean 4 proof that it does so at every real point of the box.

**Function** (2 inputs):

    spec(x0, x1) = |max (3 * x0 + 3 * x1 + 1) ((1/2) * x0 + (-1/2))|

(`max a b`, `min a b` and `|a|` have their usual meaning.)

**Box:** -2 ≤ x0 ≤ 4, -8 ≤ x1 ≤ 4

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `def net : Lane4.Net`: rational weights. Hidden layers apply ReLU, the output layer
  is affine. At most 6 hidden layers, each at most 32 units wide, 2 inputs, 1 output.
- `theorem net_correct : Statement net`, where `Statement` is in `Spec.lean`.

## Rules

- Write exactly one file in this folder: `Solution.lean`. Do not edit any other file here
  and do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.Basic`, then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
  Read `Basic.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.
- Write `Solution.lean` with your file-writing tool, as UTF-8 (it contains characters such as
  `ℝ` and `≤`); do not patch it with shell one-liners.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/rung1-test/net/p063"

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
