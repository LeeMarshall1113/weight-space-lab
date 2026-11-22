# Task: a stored weight row applied to integer affine forms, with its own symbol

This is framework work, not a test. Prove the one statement `Lane4.LNC.DotFSound`
(`LNDefs.lean`, section "le").

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec pdot radd rsum)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2`):

- `theorem dot_f_sound : DotFSound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.LNB1`
(which imports the proved modules LNKA and LNKD, and through them LNDefs, LNCert, LNNet,
R8All, Mathlib), then `Spec.lean` (empty), then your `Solution.lean`, then `Final.lean`.

**Background. Read these copies first.**
- `LNCert.lean`: `SC = 2^56`, `cdiv`, `chg m = m / 2^22 + 1`, `iabs`, `floorQ`, `gridOK`,
  `gridL`, `intL`, the forms `FF`, `linI`, `FF.dev`, `FF.mag`, `FF.wide`, `FF.bump`, `addAt`,
  `zeroFrom`, `freeOpt`, `FF.small`, `lcC`, `lcT`, `sumWR`, `sumWM`, `sumI`, and `dotF`.
- `LNDefs.lean`: `linValI`, `InFF`, `InFFs`, `Shaped`, `AgreeBelow`, and the statement.
- `AGate.lean`: `asw fl w d = fl (w + d)`, `ardot`. `R7Cert.lean`: `smallQ` (`|entry| ≤ 15`).
- **Proved and imported:** `Lane4.LNKA.ardot_rel : ArdotRel` (file `LNKA.lean`; statement
  in `LNDefs.lean`, section "la"): for a row `r` of at most 32 entries of size at most 15,
  perturbations `|d k| ≤ δ ≤ 1/2`, and a real vector with entries of size at most 17,

      |ardot fl r x d 0 0 - dotP r x d 0| ≤ 2 * (n + 2) * u * dotT δ r x + 200 * n * η

  with `dotP r x d 0 = Σ (r_i + d_i) * x_i` and `dotT δ r x = Σ (|r_i| + δ) * |x_i|`.
  And the form lemmas of `LNKD.lean` (section "ld"): `box_sound` (`|v| * 2^56 ≤ a.mag`),
  `frame_ff`, `zero_facts`, and its helper lemmas about `linValI`, floor division and
  `floorQ` on the grid; look them up in `LNKD.lean` and reuse them by name.

**The function** (`dI = floorQ δ`, `wI = intL w`, `bI = floorQ b`, all exact because of the
grid hypotheses: `(floorQ q : ℝ) = q * 2^56`; `ms = X.map FF.mag`, `sd = Σ X_i.dev`,
`sc = Σ |X_i.c|`, `n = wI.length`):

    o0 = ⟨lcC wI X / SC, (lcT ns wI X).map (· / SC), cdiv (sumWR wI X) SC + (ns + 1)⟩
    o1 = o0.wide (cdiv (dI * sd) SC + cdiv ((n + 2) * 2 * sumWM dI wI ms) (SC * 2^22) + 1
                  + chg (iabs bI + dI))
    o2 = (⟨o1.c + bI, o1.t, o1.r⟩).bump slot (cdiv (dI * (sc + SC)) SC)
    result = (freeOpt slot0 o1 && (o2.wide (chg o2.mag)).small, o2.wide (chg o2.mag))

**The mathematics** (units of `2^-56`; `S = 2^56`; `x_i * S = X_i.c + L_i + ρ_i` with
`L_i = linValI X_i.t e 0`, `|ρ_i| ≤ X_i.r`, `|L_i + ρ_i| ≤ X_i.dev`, `|x_i| * S ≤ X_i.mag ≤ 16 * S`).

1. *The exact row* `Σ w_i * x_i` is represented by `o0` under `e`: centre
   `Σ wI_i * X_i.c / S` (floor: one unit), coefficient of slot `j`
   `Σ_i wI_i * X_i.t[j] / S` (floors: at most `ns` units; prove
   `linValI (lcT ns wI X) e 0 = Σ_i wI_i * linValI X_i.t e 0`, all lists of length `ns`),
   radius `Σ |wI_i| * X_i.r / S` rounded up, plus `ns + 1`.
2. *The perturbation of the row.* `dotP w x dW 0 = Σ w_i * x_i + Σ dW_i * x_i`, and
   `Σ dW_i * x_i * S = Σ dW_i * X_i.c + Σ dW_i * (L_i + ρ_i)`. The second sum is at most
   `δ * sd` in size: radius `cdiv (dI * sd) SC`. The first sum, `P1 = Σ dW_i * X_i.c`, has
   `|P1| ≤ δ * sc`.
3. *The stored bias.* `asw fl b db = b + db + ρ_b` with `|ρ_b| ≤ u * (|b| + δ) + η`, which
   `chg (iabs bI + dI)` covers. `db` joins the symbol: `P = P1 + db * S`, `|P| ≤ δ * sc + δ * S`,
   and `cdiv (dI * (sc + SC)) SC ≥ |P|`.
4. *Rounding of the row*, by `ardot_rel` (entries of `x` at most 16): at most
   `2 * (n + 2) * u * dotT δ w x + 200 * n * η`, and `dotT δ w x * S^2 ≤ sumWM dI wI ms`
   (`|x_i| * S ≤ ms_i`), so in units at most `2 * (n + 2) * sumWM / (S * 2^24)`, below
   `cdiv ((n + 2) * 2 * sumWM dI wI ms) (SC * 2^22)`; the `+ 1` covers `200 * n * η * S`.
5. *The last rounding.* `fl (ardot ... + asw fl b db)` is within `u * |sum| + η` of the sum,
   and `|sum| * S ≤ o2.mag` once the sum is known to be represented by `o2` (see 6), so
   `chg o2.mag` covers it. Sizes for `Rnd.err`: everything is below `2^13`.
6. *Where `P` goes.*
   - `slot = none`: `bump` adds `cdiv (dI * (sc + SC)) SC` to the radius. Then the sum is
     represented by `o2` under `e` itself, and the result under `e`.
   - `slot0 = some s0`, `slot = some s`, `s0 ≤ s < ns`, and the guard `freeOpt slot0 o1`
     is true: every coefficient of `o1` from slot `s0` on is zero (`zero_facts`), so
     `linValI o1.t e' 0 = linValI o1.t e 0` for every `e'` that agrees with `e` below `s0`
     (`frame_ff`), and `bump` SETS the coefficient of slot `s` to `K = cdiv (dI * (sc + SC)) SC`
     (it was zero; `addAt`). Take `v = P / K` (and `v = 0` if `K = 0`, in which case `P = 0`).
     Then `|v| ≤ 1` and for every such `e'` with `e' s = v`:
     `linValI o2.t e' 0 = linValI o1.t e 0 + K * v = linValI o1.t e 0 + P`, so the sum is
     represented by `o2` under `e'` with the radius of `o1`, and the result follows as in 5.
     Note that `|e' k| ≤ 1` is NOT assumed for `k ≥ s0`, `k ≠ s`: those coefficients are zero.
7. *The other two conclusions.* The result's coefficient list has `ns` entries (`lcT` gives
   `ns`, `map`, `addAt` keep the length); its magnitude is at most `15 * SC` by the second
   half of the guard (`FF.small`).

**Hints.**
- Submit early: first step 1 alone as a lemma (a partial file FAILS at `Final.lean` but
  shows the errors Lean finds in your part).
- The statement repeats the long `dotF ...` term; start the proof with
  `intro ...; set R := dotF ... with hR` or prove a lemma about an arbitrary result of the
  `let` chain: unfold `dotF` once and name `o0`, `o1`, `o2`.
- `nlinarith` struggles with products of three unknowns; isolate `u * A ≤ A / 2^24`.
- **If the statement is false as written, or a constant in `dotF` is too small for the
  argument, say so in your reply with the exact place instead of spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/le"

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
