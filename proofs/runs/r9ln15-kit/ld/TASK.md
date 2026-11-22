# Task: small lemmas on integer affine forms

This is framework work, not a test. Prove the seven statements of section "ld" of
`LNDefs.lean` (namespace `Lane4.LNC`): `FrameFF`, `ZeroFacts`, `BoxSound`, `AddFSound`,
`ReluFSound`, `ResFSound`, `HoFSound`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec pdot radd rsum)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2`):

- `theorem frame_ff : FrameFF`
- `theorem zero_facts : ZeroFacts`
- `theorem box_sound : BoxSound`
- `theorem add_f_sound : AddFSound`
- `theorem relu_f_sound : ReluFSound`
- `theorem res_f_sound : ResFSound`
- `theorem ho_f_sound : HoFSound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.LNDefs`
(which imports LNCert, LNNet, R8All, Mathlib), then `Spec.lean` (empty), then your
`Solution.lean`, then `Final.lean`.

**Background. Read these copies first.**
- `LNCert.lean`: `SC = 2^56 : ℤ`, `SCq = 2^56 : ℚ`, `cdiv a b = -((-a) / b)` (ceiling
  division for `b > 0`; `/` on `ℤ` rounds down for a positive divisor), `chg m = m / 2^22 + 1`,
  `iabs`, `floorQ q = q.num * SC / q.den`, `ceilQ`, `gridOK`, `gridL`, the forms `FF`
  (centre `c`, coefficients `t`, radius `r`, all integers in units of `2^-56`), `linI`,
  `FF.dev`, `FF.mag`, `FF.add`, `FF.wide`, `zeroF`, `FF.small`, `addAt`, `zeroFrom`,
  `zeroRange`, `reluF`, `intL`, `unitL`, `resF`, `boxOf`, `padTo`, `hoF`, `addOne`.
- `LNDefs.lean`: `linValI`, `InFF`, `InFFs`, `Shaped`, `AgreeBelow`.
  `InFF e v a` means `|v * 2^56 - (a.c + Σ_k a.t[k] * e k)| ≤ a.r`.
- `R8Defs.lean`: `linVal`, `InAF` (the rational forms `AF` of rung 8), `Sym e` (every
  `|e k| ≤ 1`). `R8Cert.lean`: `AF`. `R8KE.lean`: the PROVED rung-8 lemmas for rational
  forms (`af_range`, `relu_af`, ...), usable as `Lane4.R8KE.<name>`; the ReLU argument there
  (`relu_mid`, `relu_small`, `relu_one`) is the one needed here, in integers.
- `R7K2.lean`: `Ctx`, `InIV`. `AGate.lean`: `asw`, `aswRow`. `RSoft.lean`: `Rnd.err`,
  `Rnd.abs`, `Rnd.near`.

**First, three facts used everywhere** (prove by induction with the start index general):
- `|linValI t e k| ≤ linI t` when `Sym e` (`linI` is a `foldl`; you may first prove
  `linI t = (t.map iabs).sum` or restate it as a recursion);
- `linValI` of a `zipWith (+)` of two lists of EQUAL length is the sum of the two;
- `linValI` reads only coefficients: if `∀ k, e' k ≠ e k → t.getD (k - start) 0 = 0`
  (indices shifted by the start index), the two values agree. That is `FrameFF`.

**The statements.**

1. `FrameFF`, `ZeroFacts`: list lemmas (`List.getD`, `List.drop`, `List.take`, `List.all`).
2. `BoxSound`: unfold; `|v * 2^56 - a.c| ≤ linI a.t + a.r = a.dev`; divide by `2^56`
   (`SCq` cast to `ℝ` is `2^56`). `0 ≤ a.dev` because `0 ≤ |...| ≤ a.r` and `0 ≤ linI`.
3. `AddFSound`: `addOne a (true, b)` has second component
   `(a.add b).wide (chg (a.add b).mag)`. The exact sum is represented by `a.add b` (equal
   lengths); `fl (x + y)` is within `u * |x + y| + η` of it (`|x + y| ≤ 32 ≤ M`), and
   `|x + y| * 2^56 ≤ (a.add b).mag = m`. To show: `(u * |x + y| + η) * 2^56 ≤ chg m`, i.e.
   `m / 2^24 + 2^-93 ≤ m / 2^22 + 1` with integer floor division on the right:
   `(m / 2^22 : ℤ) + 1 > m / 2^22` as reals.
4. `ReluFSound`: `lo = p.c - p.dev ≤ v * 2^56 ≤ hi = p.c + p.dev`. Three cases as in
   `reluF`. In the middle case `lam = hi * 2^20 / (hi - lo)` is an integer in `[0, 2^20]`,
   `λ = lam / 2^20` (real) and for every `w ∈ [lo, hi]`:
   `0 ≤ relu w - λ * w ≤ max (-(λ * lo)) ((1 - λ) * hi)` (`Lane4.R8KE.relu_mid` states this
   for reals; `Lane4.relu x = max x 0`). With `mu = cdiv (max (-(lam * lo)) ((2^20 - lam) * hi)) (2^21)`
   at least half of that maximum: `relu` is within `mu` of `λ * w + mu`. The new form has
   centre `lam * p.c / 2^20 + mu` (floor: one unit), coefficients `lam * x / 2^20` (floors:
   at most `p.t.length` units in all, `|e k| ≤ 1`), radius `cdiv (lam * p.r) (2^20)` plus
   `p.t.length + 1` plus `mu`. Length: `List.length_map`, `List.length_replicate`.
5. `ResFSound`: entry `k` of `resF (floorQ δ) ns (intL row) 0` is
   `⟨floorQ row_k, unitL ns k (floorQ δ), chg (iabs (floorQ row_k) + floorQ δ)⟩`; on the
   grid `floorQ q` cast to `ℝ` equals `q * 2^56` exactly (`gridOK q`: the denominator divides
   `2^56`; prove this once as a lemma). The stored entry is `fl (row_k + d k)`, within
   `u * (|row_k| + δ) + η` of `row_k + d k`. Take `e0 k = d k / δ` (and `0` if `δ = 0`); then
   `(floorQ δ : ℝ) * e0 k = d k * 2^56`. `linValI (unitL ns k c) e 0 = c * e k` for `k < ns`.
   Magnitude: `15 * 2^56 + 2^55 + small ≤ 16 * 2^56`.
6. `HoFSound`: `InAF e v a` says `|v - (a.c + linVal a.t e 0)| ≤ a.r` (rationals cast to
   reals). The integer form has centre `floorQ a.c`, coefficients `floorQ` of each entry of
   `a.t` padded with zeros to `ns` slots, and the coefficient `C = ceilQ a.r + 1 + n8` at
   `slot` (the guard says the padded list has length `ns` and is zero from `hB` on, and
   `hB ≤ slot < ns`, so `addAt` puts exactly `C` there), radius `0`. Take
   `s = (v * 2^56 - floorQ a.c - Σ_k (floorQ t_k) * e k) / C`. Then `|s| ≤ 1` because the
   numerator is at most `a.r * 2^56 + 1 + (number of entries of rest) ≤ C` in absolute value:
   each floor loses less than one unit, the `pre` leading zeros lose nothing, and
   `|e k| ≤ 1`. For an assignment `e'` that agrees with `e` below `hB` and has `e' slot = s`,
   the form's value is `floorQ a.c + Σ_{k < hB} (floorQ t_k) * e k + C * s` (coefficients
   from `hB` on are zero except at `slot`), which is exactly `v * 2^56`. `C ≥ 1` since
   `a.r ≥ 0` (from `InAF`).

**Hints.**
- Submit after each statement (a partial file FAILS at `Final.lean` but shows the errors
  Lean finds in your part). Do not write everything before the first submission.
- Integer floor division as real inequalities: for `b > 0`,
  `((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b` and `(a : ℝ) / b < ((a / b : ℤ) : ℝ) + 1`
  (from `Int.ediv_mul_le`, `Int.lt_ediv_add_one_mul_self`, or `Int.emod` facts, then
  `exact_mod_cast` / `push_cast` and `div_le_iff`); state them once.
- **If a statement is false as written, or a constant is too small for the argument, say so
  in your reply with the exact place instead of spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/ld"

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
