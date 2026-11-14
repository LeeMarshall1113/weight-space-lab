# Task: prove that a given ReLU network stays close to a target when its weights move

`Spec.lean` contains a ReLU multi-layer perceptron `twin` with fixed rational weights (it
was trained, not designed) and a target function `spec`. Prove in Lean 4 that **every**
network whose weights and biases are each within 1/1000 of `twin`'s stays within 11/20 of
the target at every real point of the box.

**Target** (3 inputs):

    spec(x0, x1, x2) = (-1) * (max (x1 + x2 + 3) ((1/2) * x0 + 1)) + (1/2) * (max ((-2) * x0 + (-1/2) * x2 + 1) 0)

**Box:** -2 ≤ x0 ≤ 4, -2 ≤ x1 ≤ 4, -2 ≤ x2 ≤ 1

**Weight tolerance:** 1/1000 per weight and per bias (including weights that are 0).

**Output tolerance:** 11/20.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `theorem twin_robust : StatementRobustTwin`, where `StatementRobustTwin` is in
  `Spec.lean` and the perturbed forward pass `Net.evalP` is in `Robust.lean`. You do not
  write any weights; the network is given and must not be changed.

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

      python <repo>/tools/submit.py "<repo>/runs/rung3-test/twin/p142"

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
