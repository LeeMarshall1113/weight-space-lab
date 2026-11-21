# Task: the head lemma of the rung-8 certificate checker

This is framework work, not a test. Prove the one statement in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2`):

- `theorem head_sound8 : HeadSound8`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R8B2`
(which imports R8KA, R8KB, R8KC, R8KD, R8KE, R8Defs, R8Soft, R8Cert, every rung-7 module,
AGateAll, ..., Mathlib), then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**Everything analytic is already proved; this task assembles it for one head.** Read, in
this order: `AGate.lean` (`AHead.gate`, `AHead.cands`, `AHead.score`, `aattnRows`,
`AHead.attn`), `R8Cert.lean` section "heads" (`HCert`, `sigFar`, `sigWin`, `softDen`,
`tailRoom`, `tailB`, `sAt`, `vAt`, `headOK8`, `nomAt`, `argmaxNom`, `refRank`, `ratioAt`,
`otherRanks`, `allSome`, `weightIV`, `coordAF`, `headAF`), `R8Defs.lean` (`linVal`, `InAF`,
`InAFs`, `WinPos`, `fullLen`), and the STATEMENTS (the `def ... : Prop` blocks at the top)
of the proved modules:

- `R8KA.lean`: `Lane4.R8KA.score_win : Lane4.R8KA.ScoreWin`. Scores of candidate keys
  against the table `sAt`: a size bound, FAR (a key `k < j`: at most
  `-(m - δ)(j - k)` + centre difference + both radii + `sigFar`), NEAR (both keys within 4
  positions of the query: the nominal difference up to `δ |k - j|` + both radii + `2^-8`).
- `R8KB.lean`: `Lane4.R8KB.savg_arith : Lane4.R8KB.SavgArith`. The rounded softmax average
  `savg` is within `B / 2^13 + 2^-90` of the exact one `eavg` (in `R8Soft.lean`) when the
  candidate list is increasing and every candidate 3 or more positions before the last one
  `p` scores at least `16 + (distance - 3) / 2` below `p`.
- `R8KC.lean`: `round_sound` (`dnB b x ≤ x ≤ upB b x`), `exp_encl`
  (`expLo x ≤ exp x ≤ expHi x` for `x ≤ 6`, `0 ≤ expLo x`).
- `R8KD.lean`: `mix_bound : MixBound`. For a reference key, a window of other keys with
  ratio bounds `lo, hi`, and a tail of total ratio at most `tl`: weights `a i` in the
  intervals that `weightIV` computes (before its outward rounding), non-negative, summing to
  at most 1, the same for every value function, with
  `|eavg - (f ref + Σ a_i (f key_i - f ref))| ≤ 2 tl B`.
- `R8KE.lean`: `af_range`, `shift_af` and the rest of the affine-form lemmas.
- From rung 7: `Lane4.R7K2.gate_sound`, `dot_sound`, `mat_sound`, `score_sound`; and
  `R7K3.lean` (copied here), the rung-7 head lemma, whose helper lemmas show how to open a
  head check, identify the candidate list, and walk the rows of `V` (`hs_rows_aux`,
  `hs_mem_cands`, `hs_gate`, `hs_dot_key`, `hs_Bf_ge`, `hs_Sb`): they are stated over the
  rung-7 environment `HEnv` (which needs `headOK`, not `headOK8`), so restate what you need.

**The argument.** Fix the query position `i`, `q = tok i ≥ 1`, `keys = P.map tok`.

1. *Candidates.* `headOK8` contains `hc.cands.length = E.length` and
   `gateDec δ h E[t] = some hc.cands[t]` for every row; with `gate_sound`: position `k`
   passes the gate filter iff `hc.cands[tok k] = true`. So `c := h.cands fl dg dgb n x i`
   is exactly the positions of `cand h.mask n i` whose token is a candidate token, in
   increasing order (`List.Pairwise (<)`: a filter of `List.range`).
2. *No key.* If `P = []`: `fullLen ≥ hc.L ≥ 1 > 0` so by hypothesis every candidate position
   is in `P`, i.e. there is none; `c = []`, every row of `aattnRows` is `savg` over the empty
   list, which is 0, and `headAF` returned zero forms (`keys.length = 0` branch; `dd` forms,
   and `h.V` has `dd` rows by `h.shapeOK dd`). Any `e'` works.
3. *Otherwise* `P = p0 :: _`. By `WinPos`, `p0` is the largest candidate position: `p0 ∈ c`
   and every `k ∈ c` is `≤ p0`. `headAF` took the second branch: `ref = refRank ...`,
   `others = otherRanks keys.length ref`, the reference-key guard holds when `hc.dense`, and
   `allSome (others.map (ratioAt ...)) = some rs` (so every `ratioAt` is `some`, its
   `hiE ≤ 6`, and `rs` lists the `(lo, hi)` pairs in the order of `others`).
   `ref < keys.length` (an `argmax` over ranks `≤ keys.length - 1`, or 0). Let
   `jr = P[ref]` and `W = others.map (P[·])` (the positions of the other keys).
4. *Values.* For a row `r` of `h.V` (index `ρ`), `f k = ardot fl r (x k) (dV ρ) 0 0`.
   `dot_sound`: `f k` lies in `dotIV δ r E[tok k]`, which is the table entry
   `vAt hc (tok k) ρ` (table equation `hc.VE = E.map (matIV δ h.V)` in `headOK8`); for a
   candidate key `|f k| ≤ hc.Bv[ρ]` (`hc.Bv = valBound ...`, a `foldl max` over candidate
   rows, as in rung 7) and `hc.Bv[ρ] ≤ 2^20`.
5. *Scores and the decay hypothesis of `savg_arith`.* `s k = h.score fl dA dm x i k`.
   From `headOK8`: for candidate tokens `a, b` and the query row,
   `centre b - centre a + radius a + radius b ≤ hc.spread`, and
   `16 ≤ tailRoom = (m - δ) L - spread - sigFar`, `1 ≤ L ≤ 3`. FAR with `j = p0`: for a
   candidate `k < p0`, `s k - s p0 ≤ -(m - δ)(p0 - k) + spread + sigFar`. Since
   `(m - δ) L ≥ 16 + spread + sigFar` and `L ≤ 3`: for `p0 - k ≥ 3`,
   `s k - s p0 ≤ -16 - (m - δ)(p0 - k - 3) ≤ -16 - (p0 - k - 3)/2` (`m - δ ≥ 1/2`). That is
   the hypothesis of `savg_arith` with `p = p0`; `Sb` from the size bound of `score_win`,
   `2 Sb ≤ M` as in `hs_Sb`; `B = hc.Bv[ρ]`, `4 B + 4 ≤ M`.
6. *Ratios of window keys.* For the key of rank `a ≠ ref`, position `P[a]`:
   - if `hc.dense` (every token a candidate): every position of `cand h.mask n i` is a
     candidate, so by `WinPos` the list `P` is the top `P.length` allowed positions,
     consecutive: `P[a] = P[0] - a`, and `P[0]` is `i` (causal) or `i - 1` (strict). With
     `P.length ≤ fullLen ≤ 4` all keys are within 4 positions of the query; NEAR gives
     `s P[a] - s P[ref]` within `δ |a - ref| + radii + 2^-8` of
     `m (P[a] - P[ref]) + centre difference = -(m (a - ref)) + centre difference`: exactly the
     `loE`, `hiE` of `ratioAt` (`sigWin = 2^-8` when dense). `exp_encl` (with `hiE ≤ 6`)
     turns them into `expLo loE ≤ exp (s P[a] - s jr) ≤ expHi hiE`.
   - if not dense: `ref = 0`, `jr = p0`, and rank `a` is at least `a` positions before `p0`
     (`P` strictly decreasing), so FAR gives `s P[a] - s p0 ≤ -(m - δ) a + ... + sigFar`,
     which is `hiE` with `sigWin = sigFar`; lower bound `0 ≤ exp _`.
7. *Tail.* The candidates outside `P` (none unless `P.length = fullLen`, by hypothesis)
   are below every member of `P`, hence at least `P.length ≥ hc.L` positions before `p0`.
   Distinct positions `k ≤ p0 - L`: `Σ exp (s k - s p0) ≤ exp (-tailRoom) * Σ_{j ≥ 0}
   exp (-(m - δ) j)`, and `(m - δ) ≥ 16/3` (from `tailRoom ≥ 16`, `L ≤ 3`) makes the
   geometric factor at most `101/100`; `exp_encl` and `round_sound` give `≤ tailB`.
   Relative to the reference key: `exp (s p0 - s jr) ≤ exp 1 ≤ 3`, by NEAR and the guard
   `radius 0 + radius ref + sigWin + δ ref ≤ 1` together with `nomAt ref ≥ nomAt 0` (the
   argmax) when dense, and trivially (`jr = p0`) otherwise. So the tail relative to `jr` is
   at most `tl = 3 * tailB` in the full case and `0` otherwise, matching `headAF`.
8. *Mix.* `mix_bound` with `c`, `s`, `jr`, `W`, `lo`/`hi` from `rs` (cast to ℝ), `tl`:
   weights `a_j`, the same for every row. `weightIV` rounds the two interval ends outward
   (`round_sound`), so `a_j ∈ [w_j.1, w_j.2]` with `w = weightIV ...`
   (`sumFst rs - lo_j` is `lo.sum - lo.getD j 0`, and so on). Define the symbol
   `e' j = (a_j - mid_j) / rad_j` with `mid = (w.1 + w.2)/2`, `rad = (w.2 - w.1)/2`
   (and `e' j = 0` if `rad_j = 0`); then `|e' j| ≤ 1` and `a_j = mid_j + rad_j * e' j`.
9. *One coordinate.* For row `ρ`: `savg` is within `Bv/2^13 + 2^-90` of `eavg` (step 5),
   `eavg` within `2 tl Bv` of `f jr + Σ_j a_j (f W_j - f jr)` (step 8), and with
   `f k = centre_k + ε_k`, `|ε_k| ≤ radius_k`: `f jr + Σ a_j (f W_j - f jr)
   = centre_ref + Σ a_j (centre_j - centre_ref) + [(1 - Σ a_j) ε_ref + Σ a_j ε_j]`, the
   bracket at most the largest radius among the keys (`a_j ≥ 0`, `Σ a_j ≤ 1`). Substituting
   `a_j = mid_j + rad_j e' j` gives exactly the centre, the coefficients (after `pre` zeros)
   and the radius of `coordAF`. Under an assignment `e` with `e (pre + j) = e' j`, `linVal`
   of `List.replicate pre 0 ++ rads` from index 0 is `Σ_j rads_j * e' j` (prove:
   `linVal (replicate pre 0 ++ l) e 0 = linVal l e pre`).
10. *Rows.* `aattnRows` walks the rows of `h.V` with the row index going up from 0;
    `headAF` returns `(List.range dd).map (coordAF ...)`. Prove the row statement for an
    arbitrary start index and a suffix of the rows, as `hs_rows_aux` does.

**Hints.**
- Split into lemmas in that order and submit after each (a partial file FAILS at
  `Final.lean` but shows the errors Lean finds in your part). Do not write the whole proof
  before the first submission. This is a long proof; keep lemmas small and named.
- `headOK8` and `headAF = some o` are the two things to open into named facts, once each.
- The weights `a_j` and symbols `e'` must be chosen BEFORE the row (they do not depend on
  the row): that is what `mix_bound` gives.
- Keep rational-to-real casts in small lemmas (`Rat.cast_le`, `push_cast`).
- **If the statement is false as written, or a constant or guard in the checker is too weak
  for the argument, say so in your reply with the exact place instead of spending
  submissions.** That would be a finding, not a failure.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r8-kit/kg"

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
