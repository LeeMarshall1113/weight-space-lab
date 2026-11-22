# Task: the reciprocal square root of a quantity known as an integer affine form

This is framework work, not a test. Prove the one statement `Lane4.LNC.RinvSound`
(`LNDefs.lean`, section "lf, lg, lh").

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec pdot radd rsum)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2`):

- `theorem rinv_sound : RinvSound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.LNDefs`
(which imports LNCert, LNNet, R8All, Mathlib), then `Spec.lean` (empty), then your
`Solution.lean`, then `Final.lean`.

**Background. Read these copies first.**
- `LNCert.lean`: `SC = 2^56` (an integer), `cdiv a b = -((-a) / b)` (ceiling division for
  `b > 0`; `/` on `ℤ` is floor division for a positive divisor), `chg m = m / 2^22 + 1`,
  `iabs`, the forms `FF` (centre `c : ℤ`, coefficients `t : List ℤ`, radius `r : ℤ`),
  `linI`, `FF.dev = linI t + r`, `FF.mag`, `sqrtOK`, and `rinvF`.
- `LNDefs.lean`: `linValI`, `InFF`:
  `InFF e v a` means `|v * 2^56 - (a.c + Σ_k a.t[k] * e k)| ≤ a.r` (everything in units of
  `2^-56`), and `Sym e` (`R8Defs.lean`) means every `|e k| ≤ 1`.
- `LNNet.lean`: `SqrtM u η sq : ∀ x ≥ 0, |sq x - Real.sqrt x| ≤ u * Real.sqrt x + η`.
  `R7K2.lean`: `Ctx u η M fl` gives `0 ≤ u ≤ 2^-24`, `0 ≤ η ≤ 2^-149`.

**The statement.** `vh` is a real number (the rounded variance plus epsilon) represented by
the form `v`: `|vh * SC - (v.c + L)| ≤ v.r` with `L = linValI v.t e 0`, `|L| ≤ linI v.t`
(prove this bound first, by induction with the start index general; `Sym e`). Write
`dv = v.dev = linI v.t + v.r` and `vmin = v.c - dv > 0`. So `vh * SC ≥ vmin > 0`, in
particular `vh > 0`, and `|vh * SC - v.c| ≤ dv`. The checker verified

    a ≥ 0,  a * a ≤ v.c * SC < (a + 1) * (a + 1)        (sqrtOK (v.c * SC) a)
    b ≥ 1,  b * b ≤ vmin * SC                           (sqrtOK (vmin * SC) b, 1 ≤ b)

and `rinvF ns v a b = some rinv` unfolds (`a ≥ 1` follows: `v.c * SC ≥ vmin * SC ≥ 1`) to

    glo = SC * SC / (a + 1)          ghi = cdiv (SC * SC) a          g0 = (glo + ghi) / 2
    eg  = ghi - glo + 1 + chg (cdiv (SC * SC) b)                     8 * eg ≤ g0   (the guard)
    k1  = g0 ^ 3 / (2 * SC * SC) + 1
    rinv.c = g0
    rinv.t = v.t.map (fun t => (-k1 * t) / SC)
    rinv.r = cdiv (k1 * v.r) SC + eg + cdiv (4 * k1 * eg * dv) (g0 * SC) + cdiv dv SC
             + cdiv (3 * dv * dv * SC ^ 4) (8 * b ^ 5) + (ns + 2)

To prove: `0 < sq vh`, `InFF e (1 / sq vh) rinv`, `rinv.t.length = ns`.

**The mathematics** (real numbers; `S = 2^56`; write `v0 = v.c / S`, `x = vh`, `f(t) = t^(-1/2)`).

1. *The centre.* `Real.sqrt v0 = Real.sqrt (v.c * S) / S` and `a ≤ Real.sqrt (v.c * S) < a + 1`,
   so `f(v0) * S = S^2 / Real.sqrt (v.c * S)` lies in `(S^2 / (a + 1), S^2 / a]`, hence in
   `[glo, ghi]` (floor below, ceiling above), and `|g0 - f(v0) * S| ≤ ghi - glo`.
   Call `G = f(v0) * S`, `eg0 = ghi - glo`.
2. *Taylor.* For `x, v0 ≥ m > 0`:
   `|f(x) - f(v0) + (1/2) * f(v0)^3 * (x - v0)| ≤ (3/8) * (x - v0)^2 * m^(-5/2)`.
   An elementary route without calculus: with `p = Real.sqrt x`, `q = Real.sqrt v0`,
   `1/p - 1/q + (p^2 - q^2) / (2 * q^3) = (p - q)^2 * (p + 2 * q) / (2 * p * q^3)`
   (check by `field_simp; ring`), and `|p - q| = |x - v0| / (p + q)`, so the left side equals
   `(x - v0)^2 * (p + 2 * q) / (2 * p * q^3 * (p + q)^2)`; with `p, q ≥ r0 = Real.sqrt m` one
   has `(p + 2 * q) / (2 * p * q^3 * (p + q)^2) ≤ (3/8) / r0^5` (cross-multiply: it says
   `8 * r0^5 * (p + 2 * q) ≤ 6 * p * q^3 * (p + q)^2`; since `p + 2 * q ≤ 3 * max p q` and
   `p * q^3 * (p + q)^2 ≥ 4 * r0^5 * max p q`... or prove it by `nlinarith` from `p ≥ r0`,
   `q ≥ r0`, `r0 > 0` after substituting `p = r0 + s`, `q = r0 + t` with `s, t ≥ 0`).
   Here `m = vmin / S` and `b / S ≤ Real.sqrt m` (from `b * b ≤ vmin * S`), so in units of
   `2^-56` the remainder is at most `(3/8) * dv^2 * S^4 / b^5`, which the fifth term of
   `rinv.r` covers.
3. *The linear term in units.* `(1/2) * f(v0)^3 * (x - v0) * S = G^3 / (2 * S^3) * (L + ρ)`
   where `x * S - v.c = L + ρ`, `|ρ| ≤ v.r`, `|L + ρ| ≤ dv`. The form uses `k1 / S` in place
   of `G^3 / (2 * S^3)`: coefficient of symbol `k` is `floor (-k1 * t_k / S)`, each floor
   costs less than one unit times `|e k| ≤ 1`, so `ns` units in all (the list has `ns`
   entries); the `ρ` part costs `k1 * v.r / S`; and the difference of slopes costs
   `|k1 / S - G^3 / (2 * S^3)| * dv`. Since `|g0 - G| ≤ eg0`, `eg0 ≤ eg ≤ g0 / 8`:
   `|g0^3 - G^3| ≤ 3 * eg0 * (g0 + eg0)^2 ≤ 3 * eg0 * g0^2 * (9/8)^2 ≤ 3.8 * eg0 * g0^2`, so
   `|g0^3 / (2 * S^2) - G^3 / (2 * S^2)| ≤ 3.8 * (eg0 / g0) * (g0^3 / (2 * S^2)) ≤ 4 * (eg / g0) * k1`
   (`g0^3 / (2 * S^2) < k1`), and the floor and the `+ 1` in `k1` move it by at most one more.
   Times `dv / S`: the third term `cdiv (4 * k1 * eg * dv) (g0 * SC)` and the fourth,
   `cdiv dv SC`, cover it. Check these inequalities carefully with the actual integers; if
   one does not hold as stated, report the exact place.
4. *The rounded square root.* `s = sq x` with `|s - Real.sqrt x| ≤ u * Real.sqrt x + η`.
   `Real.sqrt x ≥ b / S ≥ 2^-56`, so `η ≤ 2^-149 ≤ 2^-90 * Real.sqrt x`; hence
   `s = Real.sqrt x * (1 + θ)` with `|θ| ≤ 2^-24 + 2^-90`, `s > 0`, and
   `|1 / s - 1 / Real.sqrt x| ≤ (1 / Real.sqrt x) * |θ| / (1 - |θ|) ≤ (1 / Real.sqrt x) / 2^22`.
   In units: `(1 / Real.sqrt x) * S ≤ S^2 / b ≤ cdiv (SC * SC) b`, so this costs at most
   `chg (cdiv (SC * SC) b)`, which is inside `eg`.
5. *Sum.* `|S / s - (g0 + Σ_k rinv.t[k] * e k)|` is at most: step 4, plus `|G - g0| ≤ eg0`,
   plus the Taylor remainder, plus the three costs of step 3, plus `ns` floors. Compare with
   `rinv.r` term by term (`eg = eg0 + 1 + chg (...)`; `ns + 2` leaves two spare units).

**Hints.**
- Work in `ℝ` with explicit casts of the integers; keep each integer fact (`floor`, `cdiv`,
  `sqrtOK` unpacked) as a small lemma: for `b > 0`, `(a / b : ℤ) ≤ a / b` and
  `a / b < (a / b : ℤ) + 1` as real statements (`Int.ediv_mul_le`, `Int.lt_ediv_add_one_mul_self`
  or `Int.floor` lemmas via `Int.cast_div`... choose what compiles), and
  `(a : ℝ) / b ≤ cdiv a b`.
- `linValI (l.map f) e k` for `f t = (-k1 * t) / SC`: prove by induction on `l` that it is
  within `l.length` of `-(k1 / SC) * linValI l e k` (real division), using `|e k| ≤ 1`.
- Submit after each step: a partial file FAILS at `Final.lean` but shows your errors.
- **If the statement is false as written, or a constant in `rinvF` is too small for the
  argument (most likely places: step 3, or the count of units in `ns + 2`),
  say so in your reply with the exact place instead of spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/lg"

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
