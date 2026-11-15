# Task: prove that round-to-nearest on the binary32 grid satisfies a rounding model

This is framework work, not a test. Prove the three statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSoft`):

- `theorem rn_rnd : RnRnd`
- `theorem rn_range : RnRange`
- `theorem rn_exists : RnExists`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.RSoft`
(Mathlib is available), then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
Read `Spec.lean`, `Final.lean`, and the structure `Rnd` at the top of `RSoft.lean`:

    structure Rnd (u η : ℝ) (fl : ℝ → ℝ) : Prop where
      err : ∀ x, |fl x - x| ≤ u * |x| + η
      mono : ∀ x y, x ≤ y → fl x ≤ fl y
      idem : ∀ x, fl (fl x) = fl x
      nat : ∀ k : ℕ, k ≤ 16777216 → fl (k : ℝ) = (k : ℝ)

**Hints (you may ignore them).**

- `idem` and `nat`: a grid point is its own unique nearest point (distance 0). A natural
  `k ≤ 2^24` is on the grid (`k = 2^24` is `2^23 * 2^1`).
- `mono`: if `x ≤ y` and `fl y < fl x`, both are grid points; `fl x` is at least as close
  to `x` as `fl y` is, and `fl y` at least as close to `y` as `fl x` is; with
  `fl y < fl x` this forces `x ≥ (fl x + fl y)/2 ≥ y`, so `x = y`, contradiction.
- `err`: it is enough to exhibit, for each `x`, ONE grid point `g` with
  `|g - x| ≤ |x| / 2^24 + 1 / 2^150`. For `x ≠ 0` take the integer `e` with
  `2^(e+23) ≤ |x| < 2^(e+24)` (for instance from `Int.log 2 |x|`, lemmas
  `Int.zpow_log_le_self`, `Int.lt_zpow_succ_log_self`). If `e ≥ -149` use
  `g = round (x / 2^e) * 2^e` (`|round t - t| ≤ 1/2`); when the rounded significand is
  `± 2^24` rewrite it as `± 2^23 * 2^(e+1)`. If `e < -149` use
  `g = round (x / 2^(-149)) * 2^(-149)`, with error at most `2^(-150)`.
- `rn_range`: `maxF` and `-maxF` are grid points; use monotonicity and idempotence.
- `rn_exists`: for each `x` a nearest grid point exists. One route: the two candidates
  `⌊x / 2^e⌋ * 2^e` and `(⌊x / 2^e⌋ + 1) * 2^e` for a suitable `e`, and every grid point
  is at most as close as the better of them. Another route: the set of distances
  `|g - x|` over grid points within distance `|x| + 1` of `x` is finite or the grid is a
  closed discrete set, so the infimum is attained; then use `Classical.choose`.
  Any correct route is fine; this is the least important of the three, do it last.
- You may submit with only some of the three theorems to see whether they compile (it
  will FAIL at `Final.lean`).

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r5-kit/kC2"

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
