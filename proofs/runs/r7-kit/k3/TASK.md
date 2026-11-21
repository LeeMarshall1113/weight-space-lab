# Task: the head lemma of the certificate checker

This is framework work, not a test. Prove the one statement in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and `open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2`):

- `theorem head_sound : HeadSound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R7B3`
(which imports R7K2, R7K1, R7Defs, R7Cert, AGateAll, ..., Mathlib), then `Spec.lean`, then
your `Solution.lean`, then `Final.lean`.

**Background. Read these copies first:** `AGate.lean` (the head: `AHead.gate`,
`AHead.cands`, `AHead.bias`, `AHead.score`, `aattnRows`, `AHead.attn`), `R7Cert.lean` (the
checker: `gateDec`, `scoreIV`, `scoreOK`, `slopeRoom`, `gap`, `valBound`, `headOK`,
`headOut`), `R7Defs.lean` (`Latest`), and the STATEMENTS at the top of `R7K2.lean`
(`Ctx`, `InIV`, `InIVs`, `Bdd`, and the eight proved interval lemmas, available as
`Lane4.R7K2.dot_sound`, `mat_sound`, `gate_sound`, `score_sound`, ...) and of `R7K1.lean`
(`Lane4.R7K1.savg_near12 : Lane4.R7K1.SavgNear12`, the softmax lemma with a score gap of
12 per unit of distance). From the older kit: `bias_gap : BiasGap` (AGateKit.lean),
`soft_zeros` (RSoftKit.lean), `Rnd.near`, `Rnd.abs`, `Rnd.bound` (RSoft.lean).

**The argument.** Fix the query position `i` (token `tok i ≥ 1`) and write `E[t]` for row
`t` of the interval table.

1. *Candidates.* `headOK` says `cd.length = E.length` and `gateDec δ h E[t] = some cd[t]`
   for every row `t`. With `gate_sound` (state `x k` lies in `E[tok k]`, `h.g.length = dd`
   from `h.shapeOK dd`): position `k` passes the gate filter iff `cd[tok k] = true`. So
   `h.cands fl dg dgb n x i` is exactly the positions `k ∈ cand h.mask n i` whose token is
   a candidate token; it is duplicate-free (a filter of `List.range`).
2. *No candidate.* If no allowed position holds a candidate token the list is empty, each
   row of `aattnRows` is `savg` over the empty list, which is 0 (`soft_zeros`, or unfold),
   and `headOut ... none` is the zero intervals of the same length (`h.V.length`).
3. *Winner.* Otherwise let `j` be the latest candidate position (`Latest`). For another
   candidate `k` (so `k < j`): with `s k = fl (bias k + content k)`,
   - `bias_gap`: `bias k + (m - δ) * (j - k) - (m + 2) / 32 ≤ bias j`, and
     `|bias| ≤ (m + 2) * (n + 1)`; its hypotheses `1 ≤ m ≤ 1024` are in `headOK`, its `n`
     is the `n` here (positions are `< n`), and `2^12 * (n + 1) ≤ M` follows from
     `2^40 * n^2 ≤ M` and `1 ≤ n`.
   - `score_sound` (query row `E[tok i]`, key rows `E[tok j]`, `E[tok k]`; `scoreOK` for
     candidate keys and query rows `E.drop 1` is in `headOK`): each content score is in
     its interval and at most 1024 in size; the pair condition in `headOK` gives
     `content k - content j ≤ slopeRoom δ h = m - δ - 12 - 3 * (m + 2) / 64`.
   - rounding the sum: `|bias + content| ≤ (m + 2) * (n + 1) + 1024`, so `fl` moves it by
     at most `u * ((m + 2) * (n + 1) + 1024) + η`, and `u * n ≤ 1/256`, `u ≤ 2^-24` make
     this at most `(m + 2) / 256 + 2^-12` (the exact small constant is yours to choose).
   - together: `s j - s k ≥ (m - δ) * (j - k) - (m + 2)/32 - 2 * ((m + 2)/256 + 2^-12)
     - slopeRoom ≥ 12 * (j - k)`, using `j - k ≥ 1`, `m - δ - 12 ≥ 0` and
     `(m + 2) / 128 ≥ 3 / 128 > 2^-11`. (`ndist j k` cast to ℝ is `|j - k|`:
     `ndist_cast`.)
   - `savg_near12` with `f k = ardot fl r (x k) (dV row) 0 0` for a row `r` of `V`:
     `dot_sound` puts `f k` in `dotIV δ r E[tok k]`, so `|f k| ≤ B` with `B` the entry of
     `valBound` for that row (a `foldl max` over the candidate rows: show it bounds
     `|centre| + radius` of every candidate row), and `B ≤ 2^20` from `headOK` gives
     `4 * B + 4 ≤ M`. Score bound `Sb = (m + 2) * (n + 1) + 1025` or similar, `2 * Sb ≤ M`.
     Result: `|savg - f j| ≤ B / 100 + 2^-90`, hence `savg` lies in the interval
     `(centre of dotIV δ r E[tok j], its radius + B / 100 + 2^-90)`, which is the entry of
     `headOut ... (some (tok j))`.
4. *Rows.* `aattnRows` recurses over the rows of `V` with the row index going up from 0;
   `headOut` is a `zipWith` over `matIV δ h.V E[t]` and `valBound`. Prove the row statement
   for an arbitrary start index and a suffix of the rows.
5. *Radii.* The last conjunct (`0 ≤` every radius of `headOut`) is arithmetic:
   `dot_sound`/`mat_sound` give non-negative radii, `valBound` entries are `≥ 0` (the fold
   starts at 0).

**Hints.**
- Split the work into lemmas in that order and submit after each (a partial file FAILS at
  `Final.lean` but shows the errors Lean finds in your part). Do not write the whole proof
  before the first submission.
- `headOK` is a conjunction of Booleans: open it once into named `Prop` facts
  (`Bool.and_eq_true`, `decide_eq_true_eq`, `List.all_eq_true`, `beq_iff_eq`), with the
  `zipWith`/`zip` parts turned into statements about indices `t < E.length`.
- Keep rational-to-real casts in small lemmas (`Rat.cast_le`, `push_cast`); the cast of
  `slopeRoom δ h` is the real expression above.
- If the statement is false as written, or a constant in the checker is too small for the
  argument, say so in your reply with the exact place instead of spending submissions.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r7-kit/k3"

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
