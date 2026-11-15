# Task: prove two lemmas for a Lean 4 lemma kit

This is framework work, not a test. Prove the two statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq Lane4.RSoft`):

- `theorem rsum_err : RsumErr`
- `theorem geom_dist : GeomDist`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.RSoft`
(which imports Lane4.RSeq, Lane4.Seq, Mathlib), then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`. Read `Spec.lean`, `Final.lean`, and in `RSoft.lean` the
structure `Rnd` and its lemmas (`Rnd.err`, `Rnd.abs`, ...); `rsum` is defined in `RSeq.lean`:

    rsum fl (a :: l) acc = rsum fl l (fl (acc + a)),   rsum fl [] acc = acc

**Hints (you may ignore them).**

- `rsum_err`: induction on the list with `acc` generalised. It is easiest to prove a
  version with a free bound `m` in place of `l.length` (`l.length ≤ m`, `u * m ≤ 1/256`)
  first. One step: `|fl (acc + a) - (acc + a)| ≤ u * |acc + a| + η` and
  `|fl (acc + a)| ≤ (1 + u) * (|acc| + |a|) + η`. The factor 101/100 works because
  `u * m ≤ 1/256 < 1/100`.
- `geom_dist`: split the keys into those below `j` and those above `j`. On each side the
  distances are distinct positive naturals, so the sum is at most `Σ_{d ≥ 1} q^d ≤ 2q`
  (for `q ≤ 1/2`). Going through `Finset` (`List.toFinset`, `Finset.sum_image`,
  `geom_sum`-type lemmas, or a direct induction on an upper bound for the largest
  distance) is fine.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r5-kit/kA2"

  It prints PASS or FAIL with Lean's output. You have **20 submissions**; stop at the
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
