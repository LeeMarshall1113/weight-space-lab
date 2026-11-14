# Task: write a transformer's weights and prove it correct for every input length

Write the weights of a small hard-attention transformer, in the fixed architecture of
`Seq.lean`, that solves the task below, and a Lean 4 proof that it is correct for input
sequences of every length.

**Task.** Tokens are 1..4 with weights 1 ↦ +0, 2 ↦ +1, 3 ↦ -1, 4 ↦ +1. The input is ACCEPTED exactly when every prefix has weight sum ≥ 0 and the whole input has weight sum 0 (a bracket-balance check).

The exact statement to prove is `Statement` in `Spec.lean`.

**Architecture (fixed; read `Seq.lean` for the definitions).** Weights are exact
rationals. A BOS token (token 0) is put at position 0, so your input occupies positions
1..length. Each position starts with its token's embedding row followed by eight position
features `[1, i, i², 1/(i+1), (-1)^i, n, 1/n, i/n]` (n = number of positions, BOS
included). Attention is average-hard: the positions with the highest score share the
weight equally. Masks: all, causal (j ≤ i), strict (j < i). Each block is heads plus a
one-hidden-layer ReLU MLP, both residual. Limits: at most 4 blocks, 4 heads per block,
state width (embedding width + 8) at most 24, MLP hidden width at most 32.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case` (with
`open Lane4.Seq`):

- `def net : TNet` with 4 real tokens, so `5` embedding rows (row 0 is BOS).
- `theorem net_correct : Statement net`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep every helper file you create (scripts, notes) inside the `scratch/`
  sub-folder of this folder, and nowhere else. Do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.Seq`, then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
  Read `Seq.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/rung2-test/net/d15"

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
