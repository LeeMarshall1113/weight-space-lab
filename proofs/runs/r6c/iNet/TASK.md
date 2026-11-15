# Task: prove an invariance theorem for token-blind transformers (Lean 4)

Prove `Lane4.TB.Invariance`, defined in `Spec.lean` (in the `Lane4.TB` part). `Spec.lean`
also contains, already proved: `Lane4.HeadProof.head_step : Lane4.Inv.HeadStep` and
`Lane4.BlockProof.block_step : Lane4.Inv.BlockStep`, with their helper lemmas (you may
use any of them; read their statements). Read `tokenBlind`, `SameOffT`, `colSum`,
`Invariance`, `Agree`, `BlockStep` in `Spec.lean`, and in `Seq.lean`: `pos`, `tokAt`,
`TNet.init`, `TNet.run`, `TNet.out`, `TNet.shapeOK`, `Block.shapeOK`, `rowsOK`, and the
lemmas `tokAt_zero`, `tokAt_succ`, `tokAt_zero_or_mem`.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv`): `theorem invariance : Invariance`.

**The intended argument (you may do it differently).** Let `de = (N.embed.getD 0 []).length`,
`d = de + 8`, `n = w₁.length + 1` (equal to `w₂.length + 1`).
1. Unpack `tokenBlind N ntok T = true`: `N.shapeOK ntok = true` (so `N.embed` is
   `e :: _` with `ntok + 1` rows, every row of length `de = e.length`, every block has
   `Block.shapeOK d`, `N.outW.length = d`); every `c ∈ T` has `c < de`; for `c < de`,
   `c ∉ T`, all rows `1..ntok` have the same entry at `c`; every block is `blockBlind T`;
   `zeroOn T N.outW`.
2. Initial states `x j = N₁.init w₁ j`, `y j = N₂.init w₂ j` satisfy `Agree T d n x y`:
   - lengths: `tokAt w j` is `0` or a member of `w` (so between 1 and `ntok`), hence a
     valid row index; rows of `N₁`, `N₂` have the lengths of the rows of `N` (`SameOffT`),
     which is `de`; `pos` has length 8.
   - off `T`: for `c < de`, `c ∉ T`: both entries equal the entry of `N` (`SameOffT`); at
     `j = 0` both tokens are BOS (`tokAt_zero`); at `1 ≤ j < n` both tokens are real, and
     real tokens agree at `c` in `N`. For `c ≥ de` the entry is a position feature
     `(pos j n).getD (c - de) 0`, the same on both sides (same `j`, same `n`).
   - sums on `c ∈ T` (`c < de`): `(x j).getD c 0 = (N₁.embed.getD (tokAt w₁ j) []).getD c 0`,
     so the sum is `colSum N₁ w₁ c`, and the hypothesis gives equality.
3. `TNet.run` is a `List.foldl` of `Block.apply n` over `N₁.blocks = N.blocks = N₂.blocks`.
   By induction on the list of blocks (generalising `x`, `y`), `block_step` gives
   `Agree T d n (N₁.run w₁) (N₂.run w₂)`. Mind that `n` is `w₁.length + 1` on one side
   and `w₂.length + 1` on the other: rewrite with the length hypothesis first.
4. `N₁.out w₁ i = qdot N₁.outW (N₁.run w₁ i) + N₁.outB`; `outW`, `outB` are those of `N`;
   `N.outW` is zero on `T` and the two final states at `i < n` have the same length and
   agree off `T`, so the two `qdot`s are equal.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r6c/iNet"

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
