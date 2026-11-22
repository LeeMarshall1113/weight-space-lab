# Task: rounded sums and dot products with an error relative to the magnitudes

This is framework work, not a test. Prove the five statements of section "la" of
`LNDefs.lean` (namespace `Lane4.LNC`): `RsumRel`, `ArdotRel`, `PdotRel`, `DotRelSound`,
`ScoreRelSound`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd rsum)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2`):

- `theorem rsum_rel : RsumRel`
- `theorem ardot_rel : ArdotRel`
- `theorem pdot_rel : PdotRel`
- `theorem dot_rel_sound : DotRelSound`
- `theorem score_rel_sound : ScoreRelSound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.LNDefs`
(which imports LNCert, LNNet, R8All and with it every rung-7 and rung-8 module and Mathlib),
then `Spec.lean` (empty), then your `Solution.lean`, then `Final.lean`.

**Background. Read these copies first.**
- `LNDefs.lean`, section "la": the real sums `sumL`, `sumAbsL`, `dotP`, `dotT`, `dotR`,
  `dotRA` (plain recursions) and the five statements.
- `LNCert.lean`, section "head tables with rounding charges relative to the magnitudes":
  `totQ`, `dotRel`, `matRel`, `pErrQ`, `ptotQ`, `scoreRel`, `scoreOKR`. `R7Cert.lean`:
  `IV = ℚ × ℚ` (centre, radius), `qabs`, `maxAbs`, `dotC`, `wErrQ`, `smallQ`, `smallM`.
- `R7K2.lean`: `Ctx`, `InIV`, `InIVs`, `Bdd`, and the PROVED rung-7 versions of the last two
  statements with an absolute rounding charge: `dot_sound : DotSound` and
  `score_sound : ScoreSound`. Same hypotheses and shape; only the error term differs. Its
  helper lemmas are usable as `Lane4.R7K2.<name>` (`zqabs_cast`, `zle_maxAbs`, ...). Read
  how they unpack `InIVs`, `Bdd`, `smallQ` and walk the lists.
- `AGate.lean`: `asw fl w d = fl (w + d)`, `ardot`, `armat`. `RSeq.lean`: `pdot`, `rsum`.
  `RSoft.lean`: the rounding model `Rnd u η M fl` with
  `Rnd.err : |x| ≤ M → |fl x - x| ≤ u * |x| + η`, and `Rnd.abs`, `Rnd.near`, `Rnd.bound`.
  `Ctx` gives `0 ≤ u ≤ 2^-24`, `0 ≤ η ≤ 2^-149`, `2^40 ≤ M`.
- `AGateKit.lean`, `AGateKitW.lean`: the old kit lemmas `ardot_near_w`, `pdot_near`. They
  bound the rounding by `n * (W + 1) * (X + 1) / 2^16`, which is NOT enough here; but their
  inductions (`ardot_auxL`, `pdot_aux`) show how to carry an accumulator.

    rsum fl (a :: l) acc              = rsum fl l (fl (acc + a))
    ardot fl (a :: w) (v :: x) d j acc = ardot fl w x d (j + 1) (fl (acc + fl (asw fl a (d j) * v)))
    pdot fl (a :: x) (b :: y) acc     = pdot fl x y (fl (acc + fl (a * b)))

**The mathematics.**

1. `RsumRel`. Each of the `n ≤ 32` partial sums is rounded once: `fl (acc + a)` is within
   `u * |acc + a| + η` of `acc + a`. Generalise over the accumulator: prove by induction on
   `l` a statement about `rsum fl l acc` for every `acc`, for example
   `|rsum fl l acc - (acc + sumL l)| ≤ ((1 + u)^k - 1) * (|acc| + sumAbsL l) + k * (1 + u)^k * η`
   with `k = l.length`, or any invariant you prefer, and then bound `(1 + u)^k - 1 ≤ 2 * k * u`
   for `k ≤ 32`, `u ≤ 2^-24` (e.g. from `(1 + u)^k ≤ 1 + 2 * k * u`, by induction on `k` while
   `2 * k * u ≤ 1`). Everything stays below `M ≥ 2^40`: terms at most `2^30`, at most 32 of
   them.
2. `ArdotRel`. The stored weight `a' = fl (a + d)` is within `u * (|a| + δ) + η` of `a + d`
   (`|a| ≤ 15` from `smallQ`, `δ ≤ 1/2`); the product `fl (a' * v)` is within
   `u * |a' * v| + η` of `a' * v`; then the chain of step 1 on the rounded products. With
   `T = dotT δ r x = Σ (|a_i| + δ) * |v_i|`: each rounded product is within
   `(2 * u + u^2) * (|a_i| + δ) * |v_i| + 20 * η` of `(a_i + d_i) * v_i`, the sum of the
   absolute rounded products is at most `(1 + 3 * u) * T + 20 * n * η`, and the chain adds
   `2 * n * u` times that. Total at most `(2 * n + 2) * u * T * (1 + 10 * u)`, which is below
   `2 * (n + 2) * u * T = (2 * n + 4) * u * T`. The `η` terms: fewer than `200 * n * η` in all
   (`|v| ≤ 17`). You may reuse the generalised chain lemma of step 1 on the list of rounded
   products, or redo the induction for `ardot` directly with the accumulator general.
3. `PdotRel`: the same with exact factors: `fl (x_i * y_i)` within `u * |x_i * y_i| + η`,
   then the chain. Sizes: `|x_i * y_i| ≤ A * B ≤ 2^20`, sums below `2^26`.
4. `DotRelSound`. `dotRel δ r xv = (dotC r xv, wErrQ δ r xv + (n + 2) * totQ δ r xv / 2^21 + 2^-60)`.
   With `x_i` within `e_i` of the centre `c_i` (`InIVs x xv`) and `|d_i| ≤ δ`:
   `|dotP r x d 0 - Σ a_i * c_i| ≤ Σ (|a_i| * e_i + δ * (|c_i| + e_i)) = wErrQ δ r xv`, and
   `dotT δ r x ≤ totQ δ r xv` because `|x_i| ≤ |c_i| + e_i ≤ 16` (`Bdd 16 xv`). Then
   `2 * (n + 2) * u ≤ (n + 2) / 2^23 ≤ (n + 2) / 2^21` and `200 * 32 * η ≤ 2^-60`. The radius is
   non-negative because every summand is.
5. `ScoreRelSound`. `y = armat fl h.A xt dA 0` lies entry by entry in `matRel δ h.A xtv`
   (step 4 per row; the rows of `h.A` have the length of `xt`; `smallM h.A`). The first
   guard of `scoreOKR` gives
   `(maxAbs centres_q + maxAbs radii_q + 1) * (maxAbs centres_y + maxAbs radii_y + 1) ≤ 2^20`,
   so `PdotRel` applies with `A`, `B` those two factors. Then
   `|dotR xq y - Σ cq_i * cy_i| ≤ Σ (eq_i * (|cy_i| + ey_i) + |cq_i| * ey_i) = pErrQ xqv (matRel ...)`
   and `dotRA xq y ≤ ptotQ xqv (matRel ...)`. The centre of `scoreRel` is
   `dotC (xqv.map Prod.fst) (matRel δ h.A xtv) = Σ cq_i * cy_i`. The size bound `≤ 1024` is
   the second guard of `scoreOKR` plus `InIV`.

**Hints.**
- Submit early and often: a partial file FAILS at `Final.lean` but shows the errors Lean
  finds in your part. Prove `rsum_rel` first and submit.
- Connect the real sums to the rational definitions (`dotC`, `wErrQ`, `totQ`, `pErrQ`,
  `ptotQ`) by small cast lemmas proved by induction on the lists (`push_cast`,
  `zqabs_cast`).
- `nlinarith` struggles with products of three unknowns; isolate bounds like
  `u * A ≤ A / 2^24` as separate `have`s and feed them to `linarith`.
- **If a statement is false as written, or a constant is too small for the argument, say so
  in your reply with the exact place instead of spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/la"

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
