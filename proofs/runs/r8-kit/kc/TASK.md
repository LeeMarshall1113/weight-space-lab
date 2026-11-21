# Task: the checker's rational enclosures of the exponential are enclosures

This is framework work, not a test. Prove the two statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Cert Lane4.Cert8`):

- `theorem round_sound : RoundSound`
- `theorem exp_encl : ExpEncl`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R8Cert`
(which imports the rung-7 modules and Mathlib), then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`.

**The definitions** (top of `R8Cert.lean`, copied here; `qabs` is in `R7Cert.lean`:
`qabs a = if a < 0 then -a else a`):

    def dnB (b : ℕ) (x : ℚ) : ℚ := (((x.num * 2 ^ b) / (x.den : ℤ) : ℤ) : ℚ) / 2 ^ b
    def upB (b : ℕ) (x : ℚ) : ℚ := -dnB b (-x)
    def expSeries (y : ℚ) : ℚ × ℚ :=
      (List.range 14).foldl (fun p k => (p.1 + p.2, p.2 * y / ((k : ℚ) + 1))) (0, 1)
    def sqN (f : ℚ → ℚ) : ℕ → ℚ → ℚ
      | 0, a => a
      | n + 1, a => sqN f n (f (a * a))
    def expLo (x : ℚ) : ℚ :=
      if x < -60 then 0
      else max (sqN (dnB 70) 6 (dnB 70 ((expSeries (x / 64)).1 - 3 * qabs (expSeries (x / 64)).2))) 0
    def expHi (x : ℚ) : ℚ :=
      if x < -60 then 1 / 2 ^ 80
      else sqN (upB 70) 6 (upB 70 ((expSeries (x / 64)).1 + 3 * qabs (expSeries (x / 64)).2))

**The argument.**

1. *Rounding.* `/` on `ℤ` is floor division for a positive divisor (`Int.ediv`):
   `(n / d) * d ≤ n` (`Int.ediv_mul_le`) with `d = x.den > 0`, and `x = x.num / x.den`
   (`Rat.num_div_den`). So `dnB b x ≤ x`; `upB` follows by negation.
2. *The series.* By induction on the number of steps, the fold over `List.range n` from
   `(0, 1)` is `(Σ_{k < n} y^k / k!, y^n / n!)` (use `List.range_succ` and
   `List.foldl_append`; state the invariant for general `n`, then take `n = 14`).
3. *Taylor remainder.* Mathlib: `Real.exp_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
   |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / m.factorial| ≤ |x| ^ n * (n.succ / (n.factorial * n))`.
   With `n = 14`: the remainder is at most `|y|^14 / 14! * (15 / 14) ≤ 3 * |y^14 / 14!|`.
   For `-60 ≤ x ≤ 6`, `y = x / 64` has `|y| ≤ 1`. So with `(S, t) = expSeries y`:
   `S - 3 * |t| ≤ exp y ≤ S + 3 * |t|` (after casting the rational sum to ℝ).
4. *Squaring.* `exp x = (exp y)^(2^6) = (((exp y)^2)^2 ...)^2`, six squarings
   (`Real.exp_nat_mul` or `← Real.exp_add` six times; `64 * y = x`). Upper bound: if
   `0 ≤ exp z ≤ a` then `exp (2 z) = (exp z)^2 ≤ a * a ≤ upB 70 (a * a)`; induct along `sqN`.
   Lower bound: if `0 ≤ a ≤ exp z` then `dnB 70 (a * a) ≤ a * a ≤ exp (2 z)`, but this
   needs `0 ≤ a` at every stage. `dnB b` of a non-negative rational is non-negative
   (floor of a non-negative integer quotient). The starting value: `dnB 70 (S - 3 |t|)`,
   where `S - 3 |t| ≥ exp y - 6 |t|`, `exp y ≥ exp (-1) ≥ 1/3` (since `y ≥ -60/64`) and
   `|t| = |y|^14 / 14! ≤ 1 / 14! < 10^-10`. So it is positive. (If that is awkward, an
   alternative that avoids the positivity argument: if the starting value were negative
   the final `max ... 0` would still be a valid lower bound only if you track it, so the
   positivity route is the simple one.)
   The final `max _ 0` keeps the lower bound valid since `exp x > 0`.
5. *Far left.* For `x < -60`: `expLo x = 0 ≤ exp x`, and `exp x ≤ exp (-60) ≤ 2^-80`:
   `exp 1 ≥ 2` gives `exp (-60) ≤ 2^-60`, which is NOT enough; use
   `exp 3 ≥ 16 = 2^4` (from `exp 1 ≥ 2.7`, Mathlib `Real.exp_one_gt_d9`), so
   `exp (-60) = (exp 3)^(-20) ≤ 2^-80`.

Casts: state the invariants for rationals and cast once (`Rat.cast_le`, `push_cast`), or
cast first and work in ℝ; `Rat.cast_max`, `Rat.cast_abs` exist. `qabs` against `|·|`:
`Lane4.R7K2.zqabs_cast : ((qabs a : ℚ) : ℝ) = |(a : ℝ)|` is imported.

**If a statement is false as written, say so in your reply with the counterexample instead
of spending submissions.** You may submit partial files (for example `round_sound` alone)
to see whether they compile; they will FAIL at `Final.lean` but show Lean's errors for your
part.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r8-kit/kc"

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
