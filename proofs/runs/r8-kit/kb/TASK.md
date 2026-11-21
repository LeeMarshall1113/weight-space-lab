# Task: the arithmetic of softmax attention when only the last few keys matter

This is framework work, not a test. Prove the statement in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq Lane4.RSoft`):

- `theorem savg_arith : SavgArith`

and whatever helper lemmas you need. The checker builds one file from
`import Lane4.R8Soft` (which imports RSoftKit, RSoft, RSeq, Seq, Basic, Mathlib), then
`Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**Background.** Read `RSoft.lean` first (the rounding model `Rnd u η M fl`, the exponential
model `ExpM u η ex`, `smax`, `swt`, `savg`), `RSeq.lean` for `rsum` (left-to-right rounded
sum), and `R8Soft.lean` for `eavg` (the exact softmax average with real exponentials).
`RSoftKit.lean` proves the older lemma `savg_near` (a single winner by a gap of 16 per
position) and `R7K1.lean` its variant at gap 12; both are models for handling `savg`, and
everything in `RSoftKit.lean` is imported and may be used (`rsum_err`, `geom_dist`,
`div_step`, `sum_split`, `abs_sum_le_aff`, ...). `R7K1.lean` is NOT imported; it is here
only to read.

    savg fl ex c s f = fl (rsum fl (c.map (fun j => fl (swt fl ex c s j * f j))) 0
                           / rsum fl (c.map (swt fl ex c s)) 0)
    swt fl ex c s j  = ex (fl (s j - smax s c))
    eavg c s f       = (Σ_{k ∈ c} exp (s k) * f k) / (Σ_{k ∈ c} exp (s k))

**What is new against `savg_near`.** There the list could be summed in any order and the
bound was `B / 100`. Here the bound is `B / 2^13`, about 80 times smaller, and it holds for
lists of any length (up to `u * n ≤ 1/256`, so tens of thousands of keys at `u = 2^-24`).
The crude estimate "rounding error of a sum ≤ u · n · total" (`rsum_err`) is therefore NOT
enough: it gives `u * n ≤ 1/256`. What makes the statement true is the ORDER: `c` is
increasing, so the sum runs from the oldest key to the newest, the weights grow
geometrically toward the end (hypothesis: a key `D ≥ 3` positions before `p` has weight at
most `exp (-16 - (D - 3) / 2)` times that of `p`), and the rounding error of each addition
is proportional to the partial sum so far, which is tiny until the last three keys.

**A route (you may ignore it).**

1. *Weights.* Let `w k = swt fl ex c s k` and `W k = exp (s k - smax s c)` (exact). The list
   is non-empty (`p ∈ c`), `smax s c` is the score of some member and is at least every
   member's score (prove both by induction on the list), so all `W k ∈ (0, 1]` and the
   best key has `W = 1`; its `w` is `ex (fl 0) = ex 0 = 1` (`Rnd.nat` at 0, `ExpM.zero`).
   For the others: `fl (s k - smax)` is within `u * t + η` of `-t`, where `t = smax - s k ≥ 0`
   and `t ≤ 2 * Sb ≤ M`; then `ExpM.err` (argument `≤ 0`: use `Rnd.mono` against `fl 0 = 0`).
   Useful bound: `|w k - W k| ≤ c0 * u * max(W k, small) + small`, obtained from
   `t * exp (-t) ≤ 1` (so that `exp (-t + u t) - exp (-t)` is at most about `2 u exp(-t/2)`
   for `u ≤ 2^-24`). You do not need sharp constants: there is a factor of about 40 between
   what a careful count gives (about `50 * u * B`) and `B / 2^13 ≈ 2048 * u * B`.
2. *Decay.* From the hypothesis, for a key `k` with `k + 3 ≤ p`:
   `W k ≤ W p * exp (-16 - (p - k - 3)/2) ≤ exp (-16) * exp (-(p - k - 3)/2)`. Keys with
   `p - k ∈ {0, 1, 2}` are at most three (the list is increasing: `Pairwise (<)`, hence
   `Nodup`), each with `W ≤ 1`.
3. *Ordered summation.* Prove a refined summation lemma by induction along the list in the
   order `rsum` adds: for non-negative terms, the error of `rsum fl l 0` against the exact
   sum is at most `u'` times the SUM OF THE PARTIAL SUMS plus the `η` terms, and bound the
   sum of partial sums by `Σ_k (term k) * (number of later elements)`. With the decay, a
   key `D` positions before `p` has at most `D` later elements, so that sum is at most
   `3 * 3 + exp (-16) * Σ_D (D + 1) * exp (-(D - 3)/2)`, a constant below 10. An easier
   alternative with the same effect: split `c` into the old part (keys with `k + 3 ≤ p`)
   and the last at most three keys (`c` increasing means the old part is a prefix); use the
   existing `rsum_err` on the prefix, whose total is at most `exp (-16) * 3` so that even
   `u * n ≤ 1/256` times it is below `10^-8`; then at most three more additions, each with
   relative error `u`.
4. *Quotient.* Numerator terms are `fl (w k * f k)` with `|f k| ≤ B`; the same summation
   bound applies with a factor `B`. The denominator is at least about 1 (it contains the
   best key's weight 1; rounding is monotone) and at most about 3.01. `div_step` in
   `RSoftKit.lean` shows how the old proof divided; the final `fl` adds `u * B + η`.
   `eavg` with `exp (s k)` equals the same quotient with `W k` (cancel `exp (smax)`).
5. *Idempotence* (`fl (savg ...) = savg ...`): `savg` is `fl` of something of size at most
   about `2 * B ≤ M`; use `Rnd.idem` as the old proof does.

The `2^-90` in the bound is there to absorb every `η` term (`η * n ≤ 2^-100`,
`η ≤ 2^-149`).

**If the statement is false as written, or a constant is too small for the argument, say so in
your reply with the exact place, instead of spending submissions.** You may submit partial
files to see whether they compile; they will FAIL at `Final.lean` but show Lean's errors
for your part. Split the work into lemmas and submit after each.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r8-kit/kb"

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
