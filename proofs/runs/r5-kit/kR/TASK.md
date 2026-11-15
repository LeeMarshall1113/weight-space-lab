# Task: prove that a round-to-nearest on a 24-bit grid satisfies a rounding model, and that one exists

This is framework work, not a test. Prove the two statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq`):

- `theorem rnx_rounding : RnxRounding`
- `theorem rnx_exists : RnxExists`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.RSeq`
(Mathlib is available), then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
Read `Spec.lean`, `Final.lean`, and the structure `Rounding` at the top of `RSeq.lean`:

    structure Rounding (u : ℝ) (fl : ℝ → ℝ) : Prop where
      rel : ∀ x, |fl x - x| ≤ u * |x|
      mono : ∀ x y, x ≤ y → fl x ≤ fl y
      idem : ∀ x, fl (fl x) = fl x
      neg : ∀ x, fl (-x) = -fl x
      nat : ∀ k : ℕ, k ≤ 16777216 → fl (k : ℝ) = (k : ℝ)

**Hints (you may ignore them).** In `scratch/` there are two reference files from a
closely related task that was solved (`kC2_spec_for_reference.lean`,
`kC2_solution_for_reference.lean`): the same statements for a grid whose exponents are
bounded below (`e ≥ -149`), where the error bound has an extra absolute term. Here the
exponent is unbounded below, so the bound is purely relative and there is no special
case for small `x`; you can reuse the structure (`near`: for each `x` ONE grid point within
`|x| / 2^24`; monotonicity from nearest-ness; a grid point is its own nearest point;
naturals up to `2^24` are on the grid). Differences to watch:

- `rel`: for `x ≠ 0` take the integer `L` with `2^L ≤ |x| < 2^(L+1)` (the reference file
  uses `exists_mem_Ico_zpow`), `e = L - 23`, `g = round (x / 2^e) * 2^e`; for `x = 0`,
  `fl 0 = 0` because 0 is a grid point.
- `rnx_exists`: the grid accumulates at 0, so a nearest point of `x ≠ 0` must be found
  among grid points with exponent bounded below (points within `|x| / 2` of `x`), e.g. as
  in the reference file after restricting to the lattice `2^(L-24) * ℤ` near `x`, or
  directly: the better of `⌊x / 2^e⌋ * 2^e` and `(⌊x / 2^e⌋ + 1) * 2^e` with `e = L - 23`
  is a nearest grid point (every grid point in `[2^L, 2^(L+1)]` is a multiple of `2^e`).
  Make the function odd by defining it on `x > 0` and setting `fl (-x) = -fl x`,
  `fl 0 = 0`. Finally `2^24 + 1 = 16777217` is not on the grid (its nearest grid points are
  `2^24` and `2^24 + 2`), so `fl 16777217 ≠ 16777217`.
- Do `rnx_rounding` first; `rnx_exists` is the harder half. You may submit with only one
  theorem to see whether it compiles (it will FAIL at `Final.lean`).

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r5-kit/kR"

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
