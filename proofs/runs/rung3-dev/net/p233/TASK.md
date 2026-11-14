# Task: write a ReLU network and prove it stays correct when its weights move

Write the weights of a small ReLU multi-layer perceptron for the function below, and a
Lean 4 proof that **every** network whose weights and biases are each within 1/1000 of
yours stays within 6/25 of the function at every real point of the box.

**Function** (2 inputs):

    spec(x0, x1) = max (min (max (x0 + (-1) * x1 + (1/2)) (2 * x1 + (-3))) (3 * x1 + 2)) ((-1/2) * x1 + 1)

(`max a b`, `min a b` and `|a|` have their usual meaning.)

**Box:** -1 ≤ x0 ≤ 4, -8 ≤ x1 ≤ 2

**Weight tolerance:** 1/1000 per weight and per bias. This includes the weights you write
as 0: every unit sees every unit of the layer below with a weight of size up to 1/1000.

**Output tolerance:** 6/25.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `def net : Lane4.Net`: rational weights. Hidden layers apply ReLU, the output layer
  is affine. At most 6 hidden layers, each at most 32 units wide, 2 inputs, 1 output.
- `theorem net_robust : StatementRobust net`, where `StatementRobust` is in `Spec.lean`
  and the perturbed forward pass `Net.evalP` is in `Robust.lean`.

Advice: the error grows with every layer and with large weights, so a shallow network
with small weights is easier to prove. Your network does not have to equal the function
exactly; it has to stay within the output tolerance under every allowed perturbation.

## Rules

- Write exactly one file in this folder: `Solution.lean`. Do not edit any other file here
  and do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.Robust` (which imports Lane4.Basic), then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
  Read `Basic.lean`, `Robust.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.
- Helper files (Python scripts, notes) go only in the `scratch/` sub-folder of this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8 (it contains characters such as
  `ℝ` and `≤`); do not patch it with shell one-liners.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/rung3-dev/net/p233"

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
