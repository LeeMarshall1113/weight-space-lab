# Task: LayerNorm on integer affine forms, assembled

This is framework work, not a test. Prove the one statement `Lane4.LNC.LnFSound`
(`LNDefs.lean`, section "lf, lg, lh").

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec pdot radd rsum)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2`):

- `theorem ln_f_sound : LnFSound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.LNB3`
(the proved modules LNKA, LNKD, LNKF, LNKG, and through them LNDefs, LNCert, LNNet, R8All,
Mathlib), then `Spec.lean` (empty), then your `Solution.lean`, then `Final.lean`.

**Background. Read these copies first.**
- `LNNet.lean`: `lnCentre`, `lnSigma`, `lnScale`, `lnorm`:

      lnorm fl sq g b dg db x = lnScale fl (lnSigma fl sq (lnCentre fl x)) (lnCentre fl x) g b dg db 0
      lnSigma fl sq c = sq (fl (fl (rsum fl (c.map (fun v => fl (v * v))) 0 / c.length) + fl (1/100000)))
      lnScale: entry k is  fl (fl (fl (c_k / s) * asw fl g_k (dg k)) + asw fl b_k (db k))

- `LNCert.lean`: `lnF`, `meanF`, `centF`, `varW`, `rinvF`, `lnOuts`, `lnOne`, `splitOK`,
  `freeOpt`, `zeroFrom`, `FF.bump`, `addAt`, `FF.small`, `chg`, `cdiv`, `SC`.
- `LNDefs.lean`: `InFF`, `InFFs`, `Shaped`, `AgreeBelow`, and the statement.
- **Proved and imported** (statements in `LNDefs.lean`):
  - `Lane4.LNKF.cent_sound : CentSound`: the centred vector `lnCentre fl x` is represented
    by `centF (meanF ns X) X`, whose forms have `ns` slots and `mag ≤ 64 * SC`;
  - `Lane4.LNKF.var_sound : VarSound`: for a vector `c` represented by forms `C` (`ns` slots,
    `mag ≤ 64 * SC`), the argument of `sq` in `lnSigma fl sq c` is represented by `varW ns C`;
  - `Lane4.LNKG.rinv_sound : RinvSound`: with the guards of `lnF`, `0 < sq vh` and
    `1 / sq vh` is represented by the form `rinv` returned by `rinvF`;
  - `Lane4.LNKD`: `box_sound` (`|v| * 2^56 ≤ a.mag`), `frame_ff`, `zero_facts`, and helper
    lemmas (`linValI_abs_le`, `linValI_zipWith_add`, `floor_facts`, `cdiv_facts`,
    `chg_facts`, `round_chg`, `floorQ_grid`, `wide_round`, `map_floor_err`, ...); read
    `LNKD.lean` and reuse them;
  - `Lane4.LNKA` (rounded chains), if needed.

**Unfolding `lnF`.** `lnF dI ns gI bI slot0 X = some Y` gives: with `cs = centF (meanF ns X) X`,
`v = varW ns cs`, `a = isqrtI (v.c * SC)`, `b = isqrtI ((v.c - v.dev) * SC)`: the guard
`0 < v.c - v.dev ∧ sqrtOK (v.c * SC) a = true ∧ sqrtOK ((v.c - v.dev) * SC) b = true ∧ 1 ≤ b`,
`rinvF ns v a b = some rinv`, and `splitOK (lnOuts dI rinv rinv.dev ns slot0 cs gI bI 0) = some Y`,
i.e. every Boolean of `lnOuts` is true and `Y` is the list of second components. From
`rinvF ... = some rinv` also `0 ≤ rinv.c` (it is `g0`, and the guard `8 * eg ≤ g0` with
`eg ≥ 1`).

**One coordinate (`lnOne`).** Let `c` be a centred entry represented by `C` under `e`, and
`ri = 1 / s` (`s = lnSigma ... > 0`) represented by `rinv` under `e`; `dr = rinv.dev`;
`S = 2^56`; `g`, `b` on the grid, `gI = g * S`, `bI = b * S`, `dI = δ * S` exactly.

1. `o0`: the exact product `c * ri`. With `c * S = C.c + Lc + ρc`, `ri * S = R.c + Lr + ρr`:
   `c * ri * S = C.c * R.c / S + (R.c * Lc + C.c * Lr) / S + (R.c * ρc + C.c * ρr + (Lc + ρc) * (Lr + ρr)) / S`,
   and `|(Lc + ρc) * (Lr + ρr)| ≤ C.dev * dr`. Floors: centre one unit, coefficients at most
   `ns` units (both lists have `ns` entries). So `o0` represents `c * ri = c / s`.
2. `o = o0.wide (chg o0.mag)` represents `fl (c / s)` (`wide_round` or the same argument).
   The first Boolean, `o.small`, gives `|fl (c / s)| ≤ 15`.
3. Gain. `asw fl g (dg k) = g + dg k + ρg`, `|ρg| ≤ u * (|g| + δ) + η`. With `o' = fl (c / s)`,
   `o' * S = O.c + L + ρ`:
   `o' * (g + dg k) * S = g * (O.c + L + ρ) + dg k * O.c + dg k * (L + ρ)`.
   `o2b = ⟨gI * O.c / S, map (gI * · / S) O.t, cdiv (|gI| * O.r) S + (ns + 1) + cdiv (dI * O.dev) S⟩`
   represents `o' * (g + dg k) - dg k * O.c / S` under `e` (floors: `ns + 1`; the term
   `dg k * (L + ρ)` is at most `δ * O.dev`).
4. Bias. `asw fl b (db k) = b + db k + ρb`, `|ρb| ≤ u * (|b| + δ) + η`. The two perturbation
   terms left over are `P = dg k * O.c + db k * S` (in units), `|P| ≤ K = cdiv (dI * (|O.c| + SC)) SC`.
   `bump` adds `K` to the radius (no slot) or sets the slot's coefficient to `K`.
5. Roundings: `ρg * o'` and the rounding of the product are covered by `chg o2.mag`
   (`o2.mag ≥ (|g| + δ) * |o'| * S`: the `ns + 1` in the radius pays for the floors in the
   coefficients); `ρb` by `chg (|bI| + dI)`; the last rounding by `chg o4.mag`. All sizes are
   far below `M`.
6. Slots. Without a slot everything holds under `e`. With `slot0 = some s0`, coordinate `k`
   uses slot `s0 + k < ns`; the second Boolean says `o2b` is zero from slot `s0` on
   (`zero_facts`), so under any `e'` that agrees with `e` below `s0` the value of `o2b` is
   unchanged (`frame_ff`), and `bump` SETS the coefficient of slot `s0 + k` to `K`. Take
   `e1 k = P / K` (`0` if `K = 0`, then `P = 0`). For `e'` with `e' (s0 + k) = e1 k` for all
   `k < n` and agreeing with `e` below `s0`, coordinate `k` is represented (its coefficients
   at the other slots `s0 + j` are zero). `e1` must be ONE function for all coordinates:
   define it from the list (`fun k => P_k / K_k`).
7. The third Boolean is the magnitude guard on the output (`≤ 15 * SC`); lengths are `ns`.

**The list.** `lnScale` and `lnOuts` both recurse over the centred list, gains and biases
with an index `k`; prove the per-coordinate statement first for arbitrary inputs, then an
induction over the lists with the index general (the lists have equal lengths: `x`, `g`,
`b`, hence `cs`). `VarSound` is applied with `c := lnCentre fl x`, `C := cs` (lengths from
`CentSound`), `RinvSound` with `vh` the argument of `sq`.

**Hints.**
- Submit early: first step 1 to 5 for one coordinate without slots (a partial file FAILS at
  `Final.lean` but shows the errors Lean finds in your part).
- `c / s = c * (1 / s)` in `ℝ`.
- **If the statement is false as written, or a constant in `lnOne` is too small for the
  argument, say so in your reply with the exact place instead of spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/lh"

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
