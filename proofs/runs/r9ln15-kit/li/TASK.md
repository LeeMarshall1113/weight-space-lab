# Task: the soundness theorem of the LayerNorm checker, from its pieces

This is framework work, not a test. Prove the one statement `Lane4.LNC.SoundLN` (at the end
of `LNCert.lean`).

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd rsum)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2`):

- `theorem sound_ln : Lane4.LNC.SoundLN`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.LNB4`
(the proved modules LNKA, LNKB, LNKC, LNKD, LNKE, LNKF, LNKG, LNKH, and through them LNDefs,
LNCert, LNNet, R8All with every rung-7 and rung-8 module, Mathlib), then `Spec.lean`
(empty), then your `Solution.lean`, then `Final.lean`.

**The model: `R8K.lean` (copied here).** It is the proved rung-8 version of this job:
`check8_open`, `shape_facts`, `block_shape`, `weights_facts`, `headOK8_facts`, `GoodH`,
`heads_ind8` (induction over the heads), `sound_core8`, `sound8`. Its public lemmas are
imported as `Lane4.R8K.<name>` and the ones that do not mention `check8`/`headOK8` can be
used directly (`shape_facts`, `block_shape`, `weights_facts`, `head_shape`,
`aattnRows_length`, list helpers). Follow its skeleton: open the checker, get the abstract
state of the prefix into `c.states` (`Lane4.R8KF.abs_closed8`, `abs_len8`, `abs_target8`,
`abs_keys8`: they talk about `HCert`, `winNext`, `keysAt`, `absState8`, which this checker
uses in exactly the same expressions with `c.heads`), then follow one position through the
network. What is new is the middle: LayerNorm and integer forms with symbol slots.

**Background. Read these copies first.**
- `LNNet.lean`: the network: `LNNet.hid`, `LNNet.mid`, `LNNet.post`, `LNNet.read`,
  `LNNet.out`, `lnorm`, `LPert`, `LPert.Within`, `SqrtM`.
- `LNCert.lean`: `checkLN` and everything it calls: `intW`, `lnWeightsOK`, `slots`, `ln1Box`,
  `allSomeL`, `boxOK`, `headOKLN`, `resF`, `headsF`, `addHO`, `addOne`, `hoF`, `lnF`, `affF`,
  `dotRows`, `dotF`, `reluF`, `splitOK`, `splitOK1`, `outLN`, `caseOKLN`, `CertLN`.
- `LNDefs.lean`: `InFF`, `InFFs`, `Shaped`, `AgreeBelow`, and the statements of the pieces.
- **Proved pieces** (statements in `LNDefs.lean`; proofs in the copied module files):
  `Lane4.LNKC.head_sound_ln : HeadSoundLN`; `Lane4.LNKD.frame_ff`, `zero_facts`,
  `box_sound`, `add_f_sound`, `relu_f_sound`, `res_f_sound`, `ho_f_sound`;
  `Lane4.LNKE.dot_f_sound : DotFSound`; `Lane4.LNKH.ln_f_sound : LnFSound`. Rung 7/8:
  `Lane4.R7K2.gate_sound` etc. are used inside the head lemma already.

**Symbol slots** (`d` state width, `nh = B.heads.length ≤ 2`, `H = c.W.c1.length`):

    hB = d + 3 * nh      lB = hB + nh * d      wB = lB + d      vB = wB + H      ns = vB + d
    [0, d)                embedding entries of the query's row
    [d + 3k, d + 3k + 3)  attention symbols of head k (rung 8's, `pre = d + 3k`)
    [hB + k d, hB + (k+1) d)   output coordinates of head k
    [lB, wB)  LN2 gain/bias      [wB, vB)  rows of W1      [vB, ns)  rows of W2

`ns ≤ 1024` from the shape facts (`d ≤ 24`, `nh ≤ 2`, `H ≤ 32`). Note `ns = slots B d` when
`c.W = intW N B` (then `c.W.c1.length = B.b1.length`).

**The chain for one position `i` with token `t = tokAt w i`.** Fix the context; write
`x j = N.net.init fl p.a w j` (the stored embedding row of the token at `j`,
`aswRow fl (N.net.embed.getD (tokAt w j) []) (p.a.E (tokAt w j)) 0`) and
`h j = N.hid fl sq p w j = lnorm fl sq N.g1 N.b1 p.g1 p.b1 (x j)`.

1. *LN1 boxes.* For every token row: `res_f_sound` gives forms for the stored row and symbol
   values `e0`; `ln_f_sound` with `slot0 = none` gives forms `Y` for `lnorm ... (row)` under
   any `Sym` assignment agreeing with `e0` below `d` (take `e0` itself where it is used,
   and `0` elsewhere; it must be `Sym`); `box_sound` turns each form into its box. The
   checker's `allSomeL (c.W.E.map (ln1Box dI (slots B d) c.W)) = some c.boxes` says these
   boxes are the rows of `c.boxes`. Hence for every position `j`:
   `tokAt w j < c.boxes.length ∧ InIVs (h j) (c.boxes.getD (tokAt w j) [])`, and `boxOK` gives
   `row.length = d ∧ Bdd 16 row` for every row. This is the hypothesis `hxE`/`hrows` of the
   head lemma, with `x := h` and `E := c.boxes`.
2. *Heads* (induction over the heads as in `heads_ind8`, with `aheadsApply fl ex p.a 0 n h i hs acc k`).
   Invariant after `k` heads: there is `g` with every `|g m| ≤ 1` such that the residual
   vector `accR` is represented (`InFFs`) by the forms `acc` under EVERY `Sym` assignment
   `e` that agrees with `g` on the slots used so far, `[0, d + 3k) ∪ [hB, hB + k d)`; the
   forms have `ns` slots and `mag ≤ 16 * SC`. Start: `res_f_sound` for the query's row (the
   forms `resF dI ns (c.W.E.getD t []) 0`; `c.W.E` is `N.net.embed.map intL`).
   Step for head `k`: `headsF` unfolds to the guard (at most 4 keys; every form of `acc` is
   zero on `[d + 3k, d + 3k + 3)` and from `hB + k d` on), `headAF ... = some ho`, and
   `splitOK (addHO ...) = some acc'`. `head_sound_ln` (with `pre = d + 3k`) gives values `e'`
   for the attention slots; then for each coordinate `r` `ho_f_sound` (with `hB`,
   `slot = hB + k d + r`, `n8 = keys.length - 1`; rung 8's `headAF` produces coefficient lists
   of the form `replicate pre 0 ++ rads` with `rads.length = keys.length - 1`: see
   `coordAF` in `R8Cert.lean`, and `Lane4.R8KG.coordAF_t`) gives a value for the
   coordinate's own slot; `add_f_sound` adds; `frame_ff` + `zero_facts` + the guard show
   that `acc` does not see the new slots. Extend `g` on the new slots.
   After the last head the used slots are exactly `[0, lB)`: so `y = N.mid B fl ex sq p w i`
   is represented by forms `Y` under every `Sym` `e` with `AgreeBelow lB g e`.
3. *LN2.* The guard `Y.all (zeroFrom lB)`, then `ln_f_sound` with `slot0 = some lB`
   (`lB + d ≤ ns`): values `e1` for the slots `[lB, wB)`; extend `g`. `Y` is still represented
   under the extended assignments (`frame_ff`, the guard).
4. *W1* (`affF dI ns wB c.W.W1 c.W.c1 y2 = some a1`, i.e. every Boolean of `dotRows` is true):
   row `hh` of `araffine fl B.W1 B.b1 (lnorm ...) (p.a.W1 0) (p.a.b1 0) 0` is
   `fl (ardot fl row y2 (p.a.W1 0 hh) 0 0 + asw fl bias (p.a.b1 0 hh))`; `dot_f_sound` with
   `slot0 = some wB`, `slot = some (wB + hh)` gives a value for the row's slot under which
   the row is represented for every assignment agreeing below `wB`. Induct over the rows
   (index general, as `araffine` and `dotRows` do); extend `g` on `[wB, vB)`.
5. *ReLU*: `relu_f_sound` per entry; the guard `(a1.map reluF).all FF.small` gives `Shaped`.
6. *W2*: as step 4 with `vB`; then `z = radd fl y a2` by `add_f_sound` per entry (the guard
   in `splitOK (zipWith (fun a b => addOne a (true, b)) y a2)`); `Y` is unchanged under
   the new slots (`frame_ff`, zero from `lB`).
7. *LNf and read-out*: `ln_f_sound` with `slot0 = none`, `dot_f_sound` with `slot = none`
   (`splitOK1`): the output `N.read fl sq p z` is represented by the form `o`.
8. *The bound.* `caseOKLN` gives `4 * (iabs (o.c - (T.out st.1 t) * SC) + o.dev) ≤ SC`; with
   `|out * 2^56 - o.c| ≤ o.dev` (`box_sound` or directly) this is `|out - T.out ...| ≤ 1/4`;
   `abs_target8` identifies `T.out` of the abstract state with `T.target w i`.

**Hints.**
- The proof is long. Build it in the order above and SUBMIT AFTER EACH STEP (a partial file
  FAILS at `Final.lean` but shows the errors Lean finds in your part). State each step as a
  lemma with explicit hypotheses (forms have `ns` slots, `mag ≤ 16 * SC`, lengths `d`), so
  that the steps are independent.
- Write "agrees on the used slots" as one predicate, e.g.
  `∀ m, (m < a ∨ (hB ≤ m ∧ m < b)) → e m = g m`, and build the new `g` with `if`s as
  `heads_ind8` does.
- `Shaped ns` needs `mag ≤ 16 * SC`; every guard `FF.small` gives `mag ≤ 15 * SC`.
- All weights are on the grid and small (`lnWeightsOK`, `weightsOK`), so `intL row` and
  `floorQ b` are exact; `c.W = intW N B` rewrites the certificate's integers into those.
- `LPert.Within` gives the bounds on every perturbation (`hp.a.W1 0 hh k`, `hp.g2 k`, ...).
- **If the statement is false as written, or a guard that the argument needs is missing in
  `checkLN`/`outLN`, say so in your reply with the exact place instead of spending
  submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r9ln15-kit/li"

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
