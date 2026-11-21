# Task: the soundness theorem of the rung-8 certificate checker

This is framework work, not a test. Prove `Lane4.Cert8.Sound8` (the last definition of
`R8Cert.lean`): if the computable checker `check8 δ N T c` returns `true`, then every
network within the additive `δ`-ball of `N`, in the rounding model, is within 1/4 of the
task target at every position of every input of every length the model covers.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and
`open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2`):

- `theorem sound8 : Lane4.Cert8.Sound8`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R8B3`
(which imports R8KG, R8KF, R8KE, R8KA..R8KD, R8Defs, R8Cert, every rung-7 module, AGateAll,
..., Mathlib), then `Spec.lean` (empty for this case), then your `Solution.lean`, then
`Final.lean`.

**Everything hard is already proved; this task is the assembly, and the same assembly was
done for rung 7 in `R7K5.lean` (copied here: read it first, it is the model, about 390
lines).** Then read `R8Cert.lean` (all of it; the per-case path is `keysAt`, `winNext`,
`headsAF`, `outAF`, `caseOK8`, `check8`), `AGate.lean` (`ANet.init`, `aheadsApply`,
`ABlock.apply`, `arunFrom`, `ANet.run`, `ANet.out`, the shape checks), `R8Defs.lean`, and
the STATEMENTS at the top of:

- `R8KE.lean`: `Lane4.R8KE.af_range`, `emb_af`, `dot_af`, `aff_af`, `add_af`, `relu_af`,
  `shift_af` (affine forms: what a form says about its number; embedding rows; stored dot
  product; stored affine map; rounded sum; ReLU; shift).
- `R8KG.lean`: `Lane4.R8KG.head_sound8 : Lane4.R8KG.HeadSound8`, the head lemma: for a head
  passing `headOK8`, a list `P` of the latest candidate positions (`WinPos`), of length at
  most `fullLen` and holding every candidate when shorter than that, and
  `headAF ... (P.map tok) = some o`: there are symbol values `e'` in `[-1, 1]` such that
  under every assignment `e` with `e (pre + k) = e' k` for `k < P.length - 1` the head's
  output is represented by `o` (`InAFs e (h.attn ...) o`).
- `R8KF.lean`: `Lane4.R8KF.abs_closed8`, `abs_len8`, `abs_target8`, `abs_keys8`: the
  abstract state of every input prefix is in a closed state set; it has one window per
  head; the task target is the automaton output on it; and for head `a` (certificate `hc`,
  `1 ≤ hc.L`) there is a `P` with `WinPos`, `P.map (tokAt w) = keysAt h hc (token at i) window`,
  `P.length ≤ fullLen`, and all candidates in `P` when `P.length < fullLen`.
- From rung 7 (`R7K2.lean`): `Ctx`, `InIVs`, `Bdd`, `Lane4.R7K2.emb_sound` (the stored
  embedding row lies in the INTERVAL row `embIV δ row`, which is what the head lemma wants
  for `E`, and is `Bdd 16`).

**The argument.** Fix everything `Sound8` quantifies over; `n = w.length + 1`,
`tok j = tokAt w j`, `E = N.embed.map (embIV δ)`.

1. *Open `check8`.* It can only be `true` when `N.blocks = [B]`. Then a conjunction of
   Booleans: `0 ≤ δ`, `δ ≤ 1/2`, `N.shapeOK T.ntok`, `weightsOK N B`,
   `c.heads.length == B.heads.length`, `headOK8` for each head with its certificate (a
   `zipWith ... |>.all id`), every state has `B.heads.length` windows, the initial state
   (`absInit8 T c.heads`, same expression) is in `c.states`, and for every state and every
   `k < T.ntok`, `caseOK8 δ N B T c st (k + 1)`. Turn it into named `Prop` facts once.
2. *`Ctx`, input states, the run:* exactly as steps 2 to 4 of the rung-7 proof
   (`R7K5.lean`). In addition, for the affine side: the query's own state
   `N.init fl p w i` is represented, under ANY symbol assignment, by the symbol-free forms
   `(N.embed.getD (tok i) []).map (fun a => ⟨a, [], e0 δ⟩)` (`emb_af`), each of magnitude
   at most 16; this list is `x0` in `outAF`.
3. *The closed state.* `st = absState8 T c.heads (w.take (i - 1))`; by `abs_closed8` (the
   second conjunct of `caseOK8` is `absStep8 T c.heads st t ∈ c.states`) `st ∈ c.states`, so
   `caseOK8 δ N B T c st (tok i) = true`: `outAF δ N B c (tok i) st.2 = some o`,
   `|o.c - T.out st.1 (tok i)| + o.dev ≤ 1/4` (rational), and `abs_target8` identifies the
   target.
4. *Open `outAF = some o`.* `headsAF δ x0.length (tok i) B.heads c.heads st.2 0 x0 = some y`,
   the guards `a1.all AF.small`, `a2.all AF.small`, `z.all AF.small`, `o.small`, with
   `a1 = affAF δ B.W1 B.b1 y`, `a2 = affAF δ B.W2 B.b2 (a1.map reluAF)`, `z = addAF y a2`,
   `o = (dotAF δ N.outW z).shift N.outB (e0 δ + rnd)`.
5. *The heads (the one new idea).* `headsAF` walks the heads with a running symbol offset
   `pre` (each head with `keys` uses `keys.length - 1` symbols, natural subtraction) and
   the running sum `acc`. Prove by induction over the list of heads, generalising `acc`,
   `pre`, the head index `k`, the windows and the real accumulator, with this invariant:

       ∃ g : ℕ → ℝ, (∀ m, |g m| ≤ 1) ∧
         ∀ e : ℕ → ℝ, (∀ m, m < pre → e m = g m) → InAFs e acc_real acc

   (at the start `pre = 0`, `acc = x0`, and `emb_af` gives it for every `e`). Step for one
   head: `head_sound8` with the `P` from `abs_keys8` (`keysAt` of the window is `P.map tok`;
   `1 ≤ hc.L` and the mask condition are inside `headOK8`) gives `e'` bounded by 1 such that
   every `e` with `e (pre + j) = e' j` for `j < K` (`K = keys.length - 1`) represents the
   head's output by `ho`. Glue: `g' m = if m < pre then g m else e' (m - pre)`. An `e` that
   agrees with `g'` below `pre + K` agrees with `g` below `pre` and has `e (pre + j) = e' j`,
   so both the old accumulator and the head output are represented under it, and `add_af`
   (with the guard `(addAF acc ho).all AF.small` from `headsAF`) represents their rounded
   sum `radd`. No fact about which coefficients of a form are zero is needed. Head `k` of
   block 0 uses the perturbations `p.A 0 k`, `p.V 0 k`, `p.m 0 k`, `p.g 0 k`, `p.gb 0 k`.
   At the end take `e = g` (the final one): `Sym e`, and `y` represents the real residual
   stream `aheadsApply fl ex p 0 n x i B.heads (x i) 0` under it.
6. *The MLP and the read-out, under that one `e`.* `af_range` gives magnitudes at most 15
   for `y` (its guard), `aff_af` for `B.W1`, `relu_af`, `aff_af` for `B.W2`, `add_af`,
   `dot_af` for `N.outW`, then `shift_af` with the stored output bias (`zasw_e0`-style:
   within `e0 δ` of `N.outB`) and the final rounding (`rnd`, by the guard `o.small`), as the
   rung-7 proof does for intervals. `ABlock.apply` and `ANet.out` unfold to exactly this
   chain.
7. *Conclusion.* `InAF e (N.out ...) o` and `af_range` give
   `|N.out ... - o.c| ≤ o.dev`, so `|N.out ... - target| ≤ |o.c - target| + o.dev ≤ 1/4`.

**Hints.**
- Submit after each step (a partial file FAILS at `Final.lean` but shows the errors Lean
  finds in your part). Do not write the whole proof before the first submission.
- Shapes: `N.shapeOK T.ntok` gives `N.embed.length = T.ntok + 1`, rows of one length
  `d ≤ 24`, and the shapes of `B` (`rowsOK`); the rung-7 proof extracts all of them.
- **If the statement is false as written, or a guard in the checker is missing for the
  argument, say so in your reply with the exact place instead of spending submissions.**

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r8-kit/kh"

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
