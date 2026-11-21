# Task: the affine-form lemmas of the rung-8 checker

This is framework work, not a test. Prove the seven statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2`):

- `theorem af_range : AFRange`
- `theorem emb_af : EmbAF`
- `theorem dot_af : DotAF`
- `theorem aff_af : AffAF`
- `theorem add_af : AddAF`
- `theorem relu_af : ReluAF`
- `theorem shift_af : ShiftAF`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R8Defs`
(which imports R8Cert, R7All and with it every rung-7 module, AGateAll, ..., Mathlib), then
`Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**Background. Read these copies first.**
- `R8Cert.lean`, section "affine forms": `AF` (centre `c`, coefficient list `t`, radius `r`),
  `sumAbs`, `AF.dev`, `AF.mag`, `AF.small`, `addL`, `AF.add`, `AF.scale`, `AF.shift`,
  `linAF`, `sumMag`, `maxMag`, `dotAF`, `affAF`, `addAF`, `reluAF`, and `dnB`.
- `R8Defs.lean`: `linVal`, `InAF`, `InAFs`, `Sym`. A real `v` is represented by a form `a`
  under symbol values `e` when `|v - (a.c + Σ_k a.t[k] * e k)| ≤ a.r`; symbols are in `[-1, 1]`.
- `R7Cert.lean`: `qabs`, `maxAbs`, `rnd = 1/2^20`, `e0 δ = δ + rnd`, `smallQ`, `smallM`.
- `R7K2.lean`: the same seven jobs for plain intervals, PROVED (`emb_sound`, `dot_sound`,
  `aff_sound`, `add_sound`, `relu_sound`); its helper lemmas are imported and usable as
  `Lane4.R7K2.<name>`: `zqabs_cast`, `zmaxAbs_nonneg`, `zle_maxAbs`, `zrnd_step`,
  `zround_step`, `zasw_e0`, `zlin_step`, `zrnd_real`, `ze0_real`, ... Read how `dot_sound`
  and `zaff_aux` use the kit lemma for a rounded dot product with perturbed weights
  (`ardot_near_w` in `AGateKitW.lean`, copied here) and do the same.
- `AGate.lean`: `asw`, `aswRow`, `ardot`, `araffine`; `RSeq.lean`: `radd`.

**The statements, in the order to prove them.**

1. `ShiftAF`, `AFRange`: unfold `InAF`. For `AFRange` show first, by induction on the
   coefficient list for an arbitrary start index, `|linVal t e k| ≤ sumAbs t` when `Sym e`
   (`zqabs_cast` turns `qabs` into `|·|`).
2. Linearity of `linVal`: `linVal (addL s t) e k = linVal s e k + linVal t e k` (induction
   on both lists; `addL` pads the shorter list) and `linVal (t.map (q * ·)) e k = q * linVal t e k`.
   Hence `AF.add` and `AF.scale` act on represented numbers as expected: if `InAF e v a` and
   `InAF e w b` then `InAF e (v + w) (a.add b)`, and `InAF e (q * v) (AF.scale q a)`.
   Then `linAF r xa` represents `Σ_i r_i * x_i` exactly (radius `Σ_i |r_i| * radius_i`).
3. `EmbAF`: `emb_sound` of `R7K2.lean` gives the stored row inside `(a, e0 δ)` entry by
   entry; a form `⟨a, [], e0 δ⟩` has no symbols, so `InAF` is the same inequality.
   Magnitude: `|a| ≤ 15` and `e0 δ ≤ 1/2 + 2^-20`.
4. `DotAF`. The rounded dot product with stored weights `asw fl r_i (d i)` differs from
   the exact `Σ_i r_i * x_i` by at most `δ * Σ_i |x_i|` (perturbation) plus the rounding
   term `n * (maxAbs r + 1) * (X + 1) / 2^16 + 2^-100` for any bound `X ≥ |x_i|`; this is
   what `dot_sound` extracts from `ardot_near_w` for intervals (there `X` is
   `maxAbs centres + maxAbs radii`; here `|x_i| ≤ (xa_i).mag ≤ maxMag xa`, by `AFRange`, and
   `Σ_i |x_i| ≤ sumMag xa`). Reuse that derivation with the exact vector `x` in place of
   interval centres: one way is to apply `dot_sound` itself to the degenerate intervals
   is NOT possible (`x` is real, intervals are rational), so go to `ardot_near_w` directly
   as `dot_sound` does. Then combine with step 2 and `ShiftAF`.
5. `AffAF`: per row, `araffine` is `fl (ardot ... + asw fl c (db i))`; the stored bias is
   within `e0 δ` of `c` (`zasw_e0`), the rounding of the sum costs `rnd` because the
   result passes the magnitude guard (`AF.small`: `mag ≤ 15`; see `zaff_aux` and
   `zround_step` for the interval version). Lists: induct over the rows with the row index
   generalised, as `zaff_aux` does.
6. `AddAF`: `radd fl x y` is entrywise `fl (x_k + y_k)`; `addAF` adds the forms and widens
   by `rnd`; the guard gives `|x_k + y_k| ≤ 15` up to the radius (see `zadd_aux`).
7. `ReluAF`. For one form `a` with `lo = a.c - a.dev`, `hi = a.c + a.dev` and `v ∈ [lo, hi]`
   (`AFRange`): if `0 ≤ lo`, `relu v = v`; if `hi ≤ 0`, `relu v = 0` and the zero form
   represents 0; otherwise `lo < 0 < hi`, `lam = dnB 20 (hi / (hi - lo))` lies in `[0, 1]`
   (`dnB` of a non-negative number is non-negative and `dnB b x ≤ x`; prove these two facts
   about `dnB` here, they are short: floor division), and for every `v ∈ [lo, hi]`
   `0 ≤ relu v - lam * v ≤ max (-(lam * lo)) ((1 - lam) * hi)` (two cases on the sign of
   `v`). With `mu` half of that maximum, `relu v` is within `mu` of `lam * v + mu`, and
   `lam * v` is represented by `AF.scale lam a`. Smallness of the result: its magnitude is at
   most `max (lam * |lo|) (lam * hi + 2 * mu) ≤ 15` when `a.mag ≤ 15`; check the algebra
   (`lam ≤ hi / (hi - lo)` gives `lam * (hi - lo) ≤ hi`).
   `Lane4.relu` is defined in `Basic.lean` as `max x 0`.

**Hints.**
- Submit after each statement (a partial file FAILS at `Final.lean` but shows the errors
  Lean finds in your part). Do not write everything before the first submission.
- Keep rational-to-real casts in small lemmas (`Rat.cast_le`, `push_cast`,
  `Rat.cast_max`); `AF.mag`, `AF.dev` are rational, the inequalities are real.
- **If a statement is false as written, or a constant in the checker is too small for the
  argument, say so in your reply with the exact place instead of spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r8-kit/ke"

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
