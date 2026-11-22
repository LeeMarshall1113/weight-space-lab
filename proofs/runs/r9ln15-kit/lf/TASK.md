# Task: LayerNorm on integer affine forms, first half: mean, centring, variance

This is framework work, not a test. Prove the two statements `Lane4.LNC.CentSound` and
`Lane4.LNC.VarSound` (`LNDefs.lean`, section "lf, lg, lh").

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec pdot radd rsum)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2`):

- `theorem cent_sound : CentSound`
- `theorem var_sound : VarSound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.LNB1`
(which imports the proved modules LNKA and LNKD, and through them LNDefs, LNCert, LNNet,
R8All, Mathlib), then `Spec.lean` (empty), then your `Solution.lean`, then `Final.lean`.

**Background. Read these copies first.**
- `LNNet.lean`: `lnCentre fl x = x.map (fun v => fl (v - fl (rsum fl x 0 / x.length)))`.
- `LNCert.lean`: `SC = 2^56`, `cdiv`, `chg m = m / 2^22 + 1`, `iabs`, the forms `FF`, `linI`,
  `FF.dev`, `FF.mag`, `FF.add`, `FF.sub`, `FF.wide`, `zeroF`, `lcT`, `sumI`, `EPSI`,
  `varF`, `meanF`, `centF`, `varW`.
- `LNDefs.lean`: `linValI`, `InFF`, `InFFs`, `Shaped` (every form has `ns` slots and
  `mag ≤ 16 * SC`), and the statements. `InFF e v a` means
  `|v * 2^56 - (a.c + Σ_k a.t[k] * e k)| ≤ a.r`.
- **Proved and imported:** `Lane4.LNKA.rsum_rel : RsumRel` (file `LNKA.lean`; statement in
  `LNDefs.lean`, section "la"):
  `|rsum fl l 0 - sumL l| ≤ 2 * n * u * sumAbsL l + 2 * n * η` for `n = l.length ≤ 32`, terms
  at most `2^30`. And the form lemmas of `LNKD.lean` (statements in `LNDefs.lean`, section
  "ld"): `Lane4.LNKD.box_sound : BoxSound` (`InFF e v a → Sym e → |v| * 2^56 ≤ a.mag`, ...)
  and the helper lemmas proved in that file about `linValI` (bound by `linI`, additivity
  over `zipWith`); look them up in `LNKD.lean` and reuse them by their names.
- `R7K2.lean`: `Ctx` (`0 ≤ u ≤ 2^-24`, `0 ≤ η ≤ 2^-149`, `2^40 ≤ M`). `RSoft.lean`: `Rnd.err`,
  `Rnd.abs`, `Rnd.near`. `R8Defs.lean`: `Sym`.

**Units.** A form is in units of `2^-56`: write `S = 2^56`. A rounding of a real quantity of
size at most `m / S` costs `u * m / S + η`, i.e. at most `m / 2^24 + 2^-93` units, and
`chg m = m / 2^22 + 1` (integer floor division, then plus one) is at least `m / 2^22`, four
times what one rounding needs. An integer floor division loses less than one unit; `cdiv`
(ceiling) loses nothing.

**CentSound.** `x` has `n` entries (`1 ≤ n ≤ 32`), represented by the forms `X` (each with
`ns ≤ 1024` slots, `mag ≤ 16 * S`, so `|x_k| ≤ 16`).

1. *The mean.* `meanF ns X = ⟨s.c / n, s.t.map (· / n), cdiv s.r n + (ns + 1) + n * chg mx⟩`
   with `s` the exact sum of the forms (`foldl FF.add (zeroF ns)`; show it represents
   `sumL x` with all `ns` slots, by induction) and `mx` the largest magnitude. The exact
   mean `sumL x / n` is represented by `⟨s.c / n, s.t.map (· / n), cdiv s.r n + ns + 1⟩`
   (one unit for the floor of the centre, at most `ns` for the floors of the coefficients).
   The rounded mean `fl (rsum fl x 0 / n)`: by `rsum_rel`,
   `|rsum fl x 0 - sumL x| ≤ 2 * n * u * sumAbsL x + 2 * n * η ≤ 2 * n * u * n * mx / S + ...`;
   dividing by `n` leaves `2 * n * u * mx / S`; the rounding of the quotient adds
   `u * (mx / S) * (1 + small) + η`. Total at most `(2 * n + 2) * u * mx / S + small`, which is
   at most `n * (mx / 2^22)` units for `n ≥ 1` (`(2 * n + 2) / 2^24 ≤ n / 2^22`), and the
   `+ n` in `n * chg mx` absorbs the `η` terms and the floor inside `chg`.
2. *Centring.* Entry `k` of `centF mean X` is `(X_k.sub mean).wide (chg (X_k.mag + mean.mag))`;
   `fl (x_k - m)` is within `u * (|x_k| + |m|) + η` of `x_k - m`.
3. *Magnitudes.* `mean.mag ≤ 17 * S` and each centred form has `mag ≤ 64 * S` (crude bounds
   suffice: `ns ≤ 1024` units are nothing against `S = 2^56`); lengths: `ns` (`zipWith` of
   two lists of length `ns`).

**VarSound.** `c` has `n` entries represented by forms `C` (`ns` slots, `mag ≤ 64 * S`, so
`|c_k| ≤ 64`). The real quantity is
`vh = fl (fl (rsum fl (c.map (fun v => fl (v * v))) 0 / n) + fl (1 / 100000))`.

1. *The exact variance as a form.* Write `c_k * S = C_k.c + L_k + ρ_k` with
   `L_k = linValI C_k.t e 0`, `|ρ_k| ≤ C_k.r`. Then
   `c_k^2 * S^2 = C_k.c^2 + 2 * C_k.c * (L_k + ρ_k) + (L_k + ρ_k)^2`, and `|L_k + ρ_k| ≤ C_k.dev`.
   So `(Σ c_k^2 / n + 1/100000) * S` is within
   `Σ (2 * |C_k.c| * C_k.r + C_k.dev^2) / (n * S)` of
   `Σ C_k.c^2 / (n * S) + S / 100000 + Σ_j (Σ_k 2 * C_k.c * C_k.t[j]) / (n * S) * e j`.
   `varF ns n C` is this with floors: centre (one unit), `EPSI = SC / 100000` (one unit),
   `ns` coefficients (`lcT ns (C.map (2 * ·.c)) C` is the list of `Σ_k 2 * C_k.c * C_k.t[j]`;
   prove `linValI (lcT ns w C) e 0 = Σ_k w_k * linValI C_k.t e 0` by induction), radius by
   `cdiv` plus `ns + 3`.
2. *Rounding.* With `q_k = c_k^2 ≥ 0` and `Q = Σ q_k`: the rounded squares are within
   `u * q_k + η` each; `rsum_rel` on the list of rounded squares (at most `2^13` each) adds
   `2 * n * u * (Q * (1 + u) + n * η) + 2 * n * η`; dividing by `n` and rounding adds
   `u * Q / n * (1 + small) + η`; `fl (1/100000)` is within `u / 100000 + η` of `1/100000`;
   the last rounding adds `u * (Q / n + 1/100000) * (1 + small) + η`. In all at most
   `(2 * n + 4) * u * (Q / n + 1/100000) + small`, and `varW` charges
   `(n + 3) * chg (varF ...).mag`, where `(varF ...).mag ≥ (Q / n + 1/100000) * S` (the form
   represents that number). `(2 * n + 4) / 2^24 ≤ (n + 3) / 2^22`; the `+ (n + 3)` absorbs
   the `η` terms and the floors inside `chg`.

**Hints.**
- Submit after `cent_sound` (a partial file FAILS at `Final.lean` but shows your errors).
- Keep integer facts as small real-valued lemmas: for `b > 0`,
  `((a / b : ℤ) : ℝ) ≤ a / b < ((a / b : ℤ) : ℝ) + 1` and `(a : ℝ) / b ≤ cdiv a b`
  (`LNKD.lean` proves such facts for its own use; reuse them if they are stated generally).
- `nlinarith` struggles with products of three unknowns; isolate `u * A ≤ A / 2^24`.
- **If a statement is false as written, or a constant in `meanF`, `centF`, `varF`, `varW` is
  too small for the argument, say so in your reply with the exact place instead of spending
  submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/lf"

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
