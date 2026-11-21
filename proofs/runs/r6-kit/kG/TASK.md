# Task: prove three error-bound lemmas for a Lean 4 lemma kit

This is framework work, not a test. Prove the three statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec pdot)` and
`open Lane4.RSoft Lane4.AGate`):

- `theorem ardot_near : ArdotNear`
- `theorem pdot_near : PdotNear`
- `theorem bias_gap : BiasGap`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.AGate`
(which imports RSoftKit, RSoft, RSeq, Seq, Basic, Mathlib), then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`. Read `Spec.lean`, `Final.lean`, the definitions `asw`,
`ardot`, `AHead.bias` and the lemmas `asw_near`, `asw_bound` in `AGate.lean`, the model
`Rnd` and its lemmas (`Rnd.abs`, `Rnd.near`, `Rnd.bound`, `Rnd.gap`, `Rnd.upper`,
`Rnd.lower`) in `RSoft.lean`, and `pdot` in `RSeq.lean`:

    ardot fl (a :: w) (v :: x) d j acc = ardot fl w x d (j+1) (fl (acc + fl (asw fl a (d j) * v)))
    pdot fl (a :: x) (b :: y) acc     = pdot fl x y (fl (acc + fl (a * b)))
    asw fl w d = fl ((w : ℝ) + d)
    AHead.bias h fl dm i j = fl (asw fl h.m dm * (((j : ℤ) - (i : ℤ) : ℤ) : ℝ))

Every guarantee of `Rnd u η M fl` holds only for arguments of absolute value at most `M`,
so each use needs a bound on the argument; the statements give `2^30 ≤ M` (or a multiple
of `n`) and bounds on all magnitudes for that purpose.

**Hints (you may ignore them). If a statement is false as written, say so in your reply
with the counterexample instead of spending submissions; the constants were chosen by
hand and have slack, but were not machine-checked.**

- `ardot_near`, `pdot_near`: generalise to an arbitrary start `acc`, start index `j` and
  an ideal partial sum `s` with `|acc - s| ≤ E`, and prove by induction on the lists
  that the error grows per term by at most
  `W*e + δ*(X+e) + (rounding of the stored weight, of the product and of the addition)`.
  One term: `|asw - a| ≤ δ + u*(W+δ) + η`; `|asw * v - a * vh| ≤ ...` (`mul_near` in
  RSoft.lean); rounding the product costs `u*|product| + η`; rounding the sum costs
  `u*|partial sum| + η`, and partial sums are at most `32*(W+1)*(X+e+1)*2`. With
  `u ≤ 2^-24`, at most 32 terms and `(W+1)*(X+e+1) ≤ 2^20`, all rounding terms together
  are below `len*(W+1)*(X+e+1)/2^16`, and all `η` terms below `1/2^100`. Track a
  running magnitude bound alongside the error (the second conjunct) so every `fl`
  argument is shown to be within `M`. Indexing with `getD` over a `cons` shifts by one:
  state the induction hypothesis on the tails.
- `bias_gap`: let `S = asw fl h.m dm`; `|S - m| ≤ δ + u*(m+δ) + η`, so `S ≥ m - δ - (m+2)*u`
  and `|S| ≤ m + 2`. The integer cast is `(j : ℝ) - (i : ℝ)` (`push_cast`), of absolute
  value at most `n`. Then `Rnd.gap` (or `upper`/`lower`) on the two products, whose
  difference is `S * ((j:ℝ) - k) ≥ (m - δ)*(j - k) - (m+2)*u*n`. All slack terms are at
  most a few times `(m+2)*u*n ≤ (m+2)/256`, plus `η` terms below `1/2^99`.
- You may submit partial files (one theorem, or helper lemmas only) to see whether they
  compile; they will FAIL at `Final.lean` but show Lean's errors for your part.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r6-kit/kG"

  It prints PASS or FAIL with Lean's output. You have **30 submissions**; stop at the
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
