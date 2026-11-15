# Task: prove the main softmax lemma of a Lean 4 lemma kit

This is framework work, not a test. Prove the statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq Lane4.RSoft`):

- `theorem savg_near : RsumErr → GeomDist → SavgNear`
- `theorem savg_zeros : SavgZeros`

and whatever helper lemmas you need. `RsumErr` and `GeomDist` (stated in `Spec.lean`) are
proved elsewhere; here they are hypotheses you may use. The checker builds one file from
`import Lane4.RSoft` (which imports Lane4.RSeq, Lane4.Seq, Mathlib), then `Spec.lean`,
then your `Solution.lean`, then `Final.lean`. Read `Spec.lean`, `Final.lean`, and in
`RSoft.lean`: `Rnd`, `ExpM`, `smax`, `swt`, `savg`, and the lemmas `smax_eq`,
`swt_winner`, `Rnd.err`, `Rnd.abs`, `Rnd.near`, `Rnd.zero`. `rsum` is in `RSeq.lean`.

    savg fl ex c s f = fl ( rsum fl (c.map (fun j => fl (swt fl ex c s j * f j))) 0
                            / rsum fl (c.map (swt fl ex c s)) 0 )
    swt fl ex c s k  = ex (fl (s k - smax s c))

**Range conditions (added).** The rounding model is `Rnd u η M fl`: its guarantees hold
only for arguments with `|x| ≤ M`, and every kit lemma that uses `fl x` asks for
`|x| ≤ B` and `B ≤ M`. `SavgNear` gives you `2 * Sb ≤ M` (for `fl (s k - s j)`) and
`4 * B + 4 ≤ M` (products `w * f` are at most `2 B`, the sums at most `4 B + 4`, the
quotient at most `2 B`). `RsumErr` has its own range hypothesis; discharge it from these.


**The argument on paper** (check the constants yourself; they have about 20% slack).
Write `w k = swt fl ex c s k`, `L = Σ_{k ∈ c, k ≠ j} w k`.

1. `j` has the largest score (gaps are ≥ 0), so `smax s c = s j` and `w j = 1`
   (`swt_winner`).
2. For `k ≠ j` with distance `d = ndist j k ≥ 1`: `s k - s j ≤ -16 d`, so by `Rnd.err`
   `fl (s k - s j) ≤ -16 d (1 - u) + η ≤ -15 d`, hence by `ExpM.err` and monotonicity of
   `Real.exp`: `0 ≤ w k ≤ (1 + 4u) (e^-15)^d + η`. With `q = e^-15 ≤ 1/10^6`
   (`Real.exp_one_gt_d9` gives `e > 2.7`, and `2.7^15 > 10^6`) and `GeomDist`:
   `L ≤ (1 + 4u) * 4 q + n η ≤ 1/10^5`.
3. Denominator: exact sum `Z = 1 + L`; by `RsumErr`, `|Z~ - Z| ≤ 101/100 * u n * Z + 2 n η`,
   so `|Z~ - 1| ≤ 0.00396` and `Z~ ≥ 0.996`.
4. Numerator terms `t k = fl (w k * f k)`: `|t j - f j| ≤ u B + η`, and for `k ≠ j`
   `|t k| ≤ (1 + u) w k B + η`. So `|Σ t - f j| ≤ u B + (1 + u) L B + n η` and
   `Σ |t| ≤ (1 + u)(1 + L) B + n η`. By `RsumErr`, `|N~ - Σ t| ≤ 101/100 * u n * Σ|t| + 2 n η`.
   Together `|N~ - f j| ≤ 0.00396 B + small`.
5. `N~ / Z~ - f j = (N~ - f j * Z~) / Z~`, and `|N~ - f j Z~| ≤ |N~ - f j| + B |Z~ - 1|`,
   so `|N~ / Z~ - f j| ≤ 0.00795 B + small`; the final `fl` adds at most `u * 1.01 B + η`.
   Total below `B / 100 + 1/2^90`. (`B ≥ 0` follows from `|f j| ≤ B`.)

Splitting a sum over `c` into the `j` term and the rest: `c` has no duplicates and
`j ∈ c`; e.g. `List.sum_map_filter`-style lemmas, or prove
`(c.map g).sum = g j + ((c.filter (· ≠ j)).map g).sum` by induction on `c`.
All `η`-terms are at most a few times `η * n + η ≤ 2/2^100`; keep them symbolic until
the end and bound them once.

`savg_zeros` is short: every numerator term is `fl (w * 0) = 0`, a rounded sum of zeros
from 0 is 0 (`Rnd.zero`), `0 / Z = 0`, `fl 0 = 0`.

You may submit with only one theorem, or with a helper lemma chain that stops early, to
see whether it compiles (it will FAIL at `Final.lean`). Build the proof in stages.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r5-kit/kB"

  It prints PASS or FAIL with Lean's output. You have **25 submissions**; stop at the
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
