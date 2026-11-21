# Task: attention mass outside the certificate's window (rung-8 checker)

This is framework work, not a test. Prove the two statements of `Spec.lean` in this folder:

- `Lane4.Case.HeadTail8` (head level): for a head passing `headOK8`, with the hypotheses of the
  head lemma `Lane4.R8KG.HeadSound8` up to the window `P`, the candidate keys outside `P` carry at
  most `3 * tailB δ h hc` of the total softmax weight `Σ exp(score)` (real `Real.exp` of the
  scores the network computes).
- `Lane4.Case.AttnWindow8` (network level): if `check8 δ N T c = true`, then for every network
  in the ball, every input, every position `i ≥ 1` and every head `a` of the block, such a
  window `P` exists with `P.length ≤ hc.L + 1`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing, inside
`namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2`):

- `theorem head_tail8 : HeadTail8`
- `theorem attn_window8 : AttnWindow8`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R8All`
(R8K, R8Glue, R8KG, R8KF, R8KE, R8KA..R8KD, R8Defs, R8Cert, every rung-7 module, Mathlib), then
`Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**Everything hard is already proved.** The files are copied here to read; they are already
compiled in the import, so use their theorems by full name and do not copy them.

## Part 1, `head_tail8`

Read `R8KG.lean`: the structure `Lane4.R8KG.Env8` (line 625), `open8`, the last theorem
`head_sound8` (how `Env8` is built from exactly the hypotheses you have; `Env8` does not need
`ex`), and above all

    theorem Lane4.R8KG.tail_real (env : Env8 ...) (hi : i < n) (hti : 1 ≤ tok i) (T : List ℕ)
        (hT : T.Nodup) (p0 jr : ℕ) (hp0i : p0 ≤ i)
        (hcp0 : hc.cands.getD (tok p0) false = true)
        (hjr : h.score fl dA dm x i p0 - h.score fl dA dm x i jr ≤ 1)
        (hTk : ∀ k ∈ T, k + hc.L ≤ p0 ∧ k ≤ i ∧ hc.cands.getD (tok k) false = true) :
        (T.map (fun k => Real.exp (h.score .. i k - h.score .. i jr))).sum ≤ ((3 * tailB δ h hc : ℚ) : ℝ)

Also in `R8KG.lean`: `e_mem_cands` (membership in `h.cands` is membership in `cand h.mask n i`
plus the token being a candidate), `AHead.cands_nodup`, `cand_le`, and how `head_keys` reads
`WinPos` (the definition is in `R8Defs.lean`: `P` is strictly decreasing, its members are
candidates, and every other candidate lies before all of them).

The argument. Let `c = h.cands ...`, `T = c.filter (· ∉ P)`.
- If `P.length < fullLen`, the third hypothesis puts every candidate in `P`, so `T = []`, the
  left side is 0, and the right side is non-negative (`tailB` is non-negative: it is `upB` of a
  positive number; the checker's `16 ≤ tailRoom` is in `Env8.room` if you need it; or simply
  bound `0 ≤ 3 * tailB` through `tail_real` applied to `T = []`... choose what is easiest).
- If `P = []` and `fullLen = 0` cannot happen (`fullLen ≥ hc.L ≥ 1`), so `P = []` is the case
  above.
- Otherwise `P.length = fullLen h hc (tok i) ≥ hc.L` and `P ≠ []`. Take `p0 = jr = P.getD 0 0`
  (the newest key; `hjr` is then `0 ≤ 1`). Every `k ∈ T` is a candidate not in `P`, hence before
  every member of `P`; `P` is strictly decreasing with at least `hc.L` members, so its last
  member is at most `p0 - (hc.L - 1)` and `k + hc.L ≤ p0`. `tail_real` gives
  `Σ_{k ∈ T} exp(s k - s p0) ≤ 3 * tailB`. Multiply by `exp(s p0)` (`Real.exp_sub` or
  `Real.exp_add`), and use `exp(s p0) ≤ Σ_{k ∈ c} exp(s k)` because `p0 ∈ c` and every term is
  positive (`List.single_le_sum` or an induction).

## Part 2, `attn_window8`

This is the first half of the assembly of `Lane4.R8K.sound8` (read `R8K.lean`: `check8_open`,
`shape_facts`, `block_shape`, `head_shape`, `weights_facts`, `headOK8_facts`, and the start of
`sound_core8` / `heads_ind8`, which obtain exactly the facts you need for one head: the `Ctx`
from `Rnd` and the bounds on `u`, `η`, the input states `N.init fl p w j` lying in the interval
rows `(N.embed.map (embIV δ)).getD (tokAt w j) []` by `Lane4.R7K2.emb_sound`, the row lengths
and `Bdd 16`, the perturbation bounds from `p.Within`, `headOK8` for head `a` with certificate
`c.heads.getD a _`, the head's shape and `smallM` / `smallQ` facts). `R7K5.lean` is the rung-7
model of the same assembly.

Then `Lane4.R8KF.abs_keys8` (statement at the top of `R8KF.lean`) gives, for head `a`, a `P` with
`WinPos h.mask hc.cands (tokAt w) (w.length + 1) i P`, `P.length ≤ fullLen h hc (tokAt w i)`,
and all candidates in `P` when `P.length < fullLen`. `fullLen ≤ hc.L + 1` by its definition
(`R8Defs.lean`). Apply `head_tail8` with `n = w.length + 1`, `tok = tokAt w`,
`x = N.init fl p w`, `dA = p.A 0 a`, `dm = p.m 0 a`, `dg = p.g 0 a`, `dgb = p.gb 0 a`
(any `dV` with the bound, e.g. `p.V 0 a`), `E = N.embed.map (embIV δ)`.

The hypotheses `B.heads.getD a h = h` and `c.heads.getD a hc = hc` with `a < B.heads.length`
say that `h` is head number `a` and `hc` its certificate (`c.heads.length = B.heads.length` from
`check8_open`). `1 ≤ tokAt w i` for `1 ≤ i ≤ w.length` comes from the token hypothesis on `w`
(see how `sound_core8` does it).

If a statement in `Spec.lean` is false as written (a missing hypothesis, a wrong index), do not
bend it: say exactly what is wrong in your final reply and stop.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/mech-kit/ma"

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
