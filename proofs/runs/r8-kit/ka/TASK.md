# Task: scores of candidate keys against the certificate's table

This is framework work, not a test. Prove the one statement in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2`):

- `theorem score_win : ScoreWin`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R8Defs`
(which imports R8Cert, R7All and with it every rung-7 module: R7K5, R7K3, R7K4, R7K2, R7K1,
R7Defs, R7Cert, AGateAll, ..., Mathlib), then `Spec.lean`, then your `Solution.lean`, then
`Final.lean`.

**Background. Read these copies first:** `AGate.lean` (the head: `AHead.bias`,
`AHead.score`), `R8Cert.lean` (the rung-8 checker: `HCert`, `sAt`, `sigFar`, `headOK8`),
`R7Cert.lean` (`scoreIV`, `scoreOK`, `gateDec`, `IV`), the STATEMENTS at the top of
`R7K2.lean` (`Ctx`, `InIV`, `InIVs`, `Bdd`, and the proved `Lane4.R7K2.score_sound :
ScoreSound`), and `R7K3.lean`, the rung-7 head lemma, whose proof does almost the same job
for the old checker: see there `hs_score_pack`, `hs_score_abs`, `hs_bias_abs`,
`hs_round_sum`, `hs_Sb` and `hs_gap`. Those lemmas are imported (namespace `Lane4.R7K3`)
but are stated over the rung-7 environment `HEnv`, which needs `headOK`, not `headOK8`; you
will mostly have to restate what you need over the facts of `headOK8`. From the older kit
(`AGateKit.lean`): `bias_gap : BiasGap`, and `Rnd.near`, `Rnd.abs`, `Rnd.bound` in
`RSoft.lean`.

    AHead.bias h fl dm i j  = fl (asw fl h.m dm * (((j : ℤ) - (i : ℤ) : ℤ) : ℝ))
    AHead.score h fl dA dm x i j = fl (h.bias fl dm i j + pdot fl (x i) (armat fl h.A (x j) dA 0) 0)
    asw fl w d = fl ((w : ℝ) + d)

**What `headOK8` gives (open it once into named facts).** `1 ≤ h.m ≤ 1024`;
`hc.cands.length = E.length`; the table equation
`hc.S = E.map (fun xq => E.map (fun xt => scoreIV δ h xq xt))`, so for `q, t < E.length`,
`sAt hc q t = scoreIV δ h (E.getD q []) (E.getD t [])`; and for every query row among
`E.drop 1` and every candidate row `t`, `scoreOK δ h xq (E row t) = true`. With
`score_sound` (states lie in rows of `E`; rows are `Bdd 16` of length `dd`; `h.shapeOK dd`
gives the shape of `h.A`): the content score `pdot ...` of query `i` against key `j` lies in
the interval `sAt hc (tok i) (tok j)`, its radius is non-negative, and its size is at most
1024.

**The three conclusions.**

1. *Size.* `|bias| ≤ (m + 2) * (n + 1)` as in rung 7 (`bias_gap` gives it, or `hs_bias_abs`),
   content at most 1024, one rounding of the sum: at most 1 more with room.
2. *FAR.* Exactly the rung-7 argument of `hs_gap`, kept as an inequality instead of being
   compared with a gap: `bias_gap` gives `bias k + (m - δ) * (j - k) - (m + 2) / 32 ≤ bias j`
   for `k < j`; the two roundings of `bias + content` cost at most
   `2 * ((m + 2) / 256 + 2^-12) = (m + 2) / 128 + 2^-11` (from `u * n ≤ 1/256`,
   `u ≤ 2^-24`, sizes at most `(m + 2) * (n + 1) + 1024`); the contents differ by at most the
   difference of the centres plus both radii. The three slack terms add up to
   `sigFar h = (m + 2) / 32 + (m + 2) / 128 + 2^-11`.
3. *NEAR (the new part).* Both keys are within 4 positions of the query, so
   `|j - i| ≤ 4`, `|k - i| ≤ 4`. Write `m' = asw fl h.m dm`; `|m' - (m + dm)| ≤ u * 1025 + η`
   and `|m'| ≤ 1025` (`asw_near`, `asw_bound`; `|m + dm| ≤ 1024.5`). Each bias is `fl` of a
   number of size at most `4 * 1025`, so it is within `u * 4100 + η` of `m' * (j - i)`.
   Each score is `fl` of a number of size at most `4101 + 1024`, so within `u * 5125 + η`
   of `bias + content`. Hence the score difference is within
   `|k - j| * (u * 1025 + η) + 2 * (u * 4100 + η) + 2 * (u * 5125 + η)` plus both radii of
   `(m + dm) * (k - j) + (centre k - centre j)`; and `|dm * (k - j)| ≤ δ * |k - j|`. With
   `u ≤ 2^-24`, `η ≤ 2^-149` and `|k - j| ≤ 4` the rounding part is at most
   `22600 * 2^-24 < 1.4 * 10^-3 < 1 / 2^8`. (The integer cast in `bias` is of `j - i` as
   integers; `push_cast` turns it into `(j : ℝ) - (i : ℝ)`.)

**Hints.**
- `headOK8` is a conjunction of Booleans: `Bool.and_eq_true`, `decide_eq_true_eq`,
  `List.all_eq_true`, `beq_iff_eq`; the `zipWith`/`zip`/`drop` parts are easiest as
  statements about indices (`R7K3.lean` has `hs_mem_drop`, `hs_mem_zip`, `hs_zipWith_all`
  for exactly this, usable as `Lane4.R7K3.hs_mem_drop` and so on).
- Keep rational-to-real casts in small lemmas (`Rat.cast_le`, `push_cast`).
- Split the work into lemmas in the order above and submit after each (a partial file FAILS
  at `Final.lean` but shows the errors Lean finds in your part).
- **If the statement is false as written, or a constant is too small for the argument, say
  so in your reply with the exact place instead of spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r8-kit/ka"

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
