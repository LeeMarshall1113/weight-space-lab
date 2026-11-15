# Task: prove that one transformer block preserves an invariant (Lean 4)

Prove `Lane4.Inv.BlockStep`, defined at the end of `Spec.lean`. `Spec.lean` also contains,
already proved, `Lane4.HeadProof.head_step : Lane4.Inv.HeadStep` (and its helper lemmas,
which you may use; read their statements). Read `Agree`, `HeadStep`, `BlockStep`,
`blockBlind`, `headBlind`, `zeroOn` in `Spec.lean`, and in `Seq.lean`: `qdot`, `vadd`,
`affine`, `Head.attn`, `Block.apply`, `rowsOK`, `Head.shapeOK`, `Block.shapeOK`.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv`): `theorem block_step : BlockStep`.
The checker builds one file from `import Lane4.Seq`, then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`.

**The intended argument (you may do it differently).** Fix `i < n`. Recall

    B.apply n x i = vadd y' (affine B.W2 B.b2 ((affine B.W1 B.b1 y').map (fun v => max v 0)))
    where y' = B.heads.foldl (fun acc h => vadd acc (h.attn n x i)) (x i)

1. By `head_step`, `h.attn n x i = h.attn n y i` for every `h ∈ B.heads` (each head is
   blind by `blockBlind`, has shape `d` by `B.shapeOK d`). Each `h.attn n x i` has length
   `d` (`h.V` has `d` rows). So the two folds add the SAME list of vectors, each of length
   `d`, to `x i` and to `y i`. Prove by induction on the list of heads (generalising the
   start vectors) that the results have length `d`, agree off `T`, and that for every
   coordinate `c < d` the increment `result.getD c 0 - start.getD c 0` is the same on
   both sides. Key fact: for `a`, `b` of length `d` and `c < d`,
   `(vadd a b).getD c 0 = a.getD c 0 + b.getD c 0`, and `(vadd a b).length = d`.
2. `affine B.W1 B.b1` gives the same list on both sides: each row of `B.W1` is zero on
   `T` (`blockBlind`), the two folded vectors have the same length and agree off `T`, so
   each `qdot row _` is equal (a congruence lemma of this kind should be among the helper
   lemmas of the head proof; check its exact name and hypotheses, or prove your own). So
   the MLP output `affine B.W2 B.b2 (...)` is literally the same list on both sides, of
   length `d` (`B.W2` has `d` rows and `B.b2` has length `d`; `affine` is a `zipWith`).
3. Conclude the three parts of `Agree` for the new states: lengths `d`; off `T` equal
   (old values equal, same increments); for `c ∈ T` (so `c < d`) the new coordinate is
   the old coordinate plus an increment that is the same on both sides, so the two sums
   over `j < n` change by the same amount (`List.sum_map_add`, or an induction on `n`).
`Bool` conditions unpack with `Bool.and_eq_true`, `List.all_eq_true`, `beq_iff_eq`,
`decide_eq_true_eq`; `rowsOK M r c = true` gives `M.length = r` and every row of length `c`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r6c/iBlock"

  It prints PASS or FAIL with Lean's output. You have **12 submissions**; stop at the
  first PASS. A check can take up to 10 minutes and may also wait in a queue. Wait for
  it. Never resubmit while one is pending. You may submit a partial file (helper lemmas
  only) to see Lean's errors for your part; it will FAIL at `Final.lean`.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. Short Python for arithmetic is fine.
- Banned in `Solution.lean` (rejected without running Lean, still costs a submission):
  `sorry`, `admit`, `axiom`, `native_decide`, `macro`, `syntax`, `notation`, `elab`,
  `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`, anything in the `Lean.`
  namespace.
- Standard axioms only. Each check is limited to 600 s and 4.5 GB.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.
- **If the statement is false as written, say so in your reply with the counterexample
  instead of spending submissions.** That would be a useful result.

## When you finish

Reply with PASS or FAIL, the number of submissions used, and three or four sentences on
how you proved it and what went wrong. If you give up, say why and what is left.
