# Task: the soundness theorem of the certificate checker

This is framework work, not a test. Prove `Lane4.Cert.Sound` (the last definition of
`R7Cert.lean`): if the computable checker `check (1/1000) N T c` returns `true`, then every
network within the additive 1/1000 ball of `N`, in the rounding model, is within 1/4 of the
task target at every position of every input of every length the model covers.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and `open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2`):

- `theorem sound : Lane4.Cert.Sound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R7B5`
(which imports R7K3, R7K4, R7K2, R7K1, R7Defs, R7Cert, AGateAll, ..., Mathlib), then
`Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**Everything hard is already proved; this task is the assembly.** Read, in this order:
`R7Cert.lean` (the checker, all of it), `AGate.lean` (the network: `ANet.init`,
`aheadsApply`, `ABlock.apply`, `arunFrom`, `ANet.run`, `ANet.out`, the shape checks),
`R7Defs.lean`, and the STATEMENTS (the `def ... : Prop` blocks at the top) of:

- `R7K2.lean`: `Ctx`, `InIV`, `InIVs`, `Bdd`; proved lemmas `Lane4.R7K2.emb_sound`,
  `dot_sound`, `mat_sound`, `aff_sound`, `add_sound`, `relu_sound`, `gate_sound`,
  `score_sound` (their statements are `EmbSound`, `DotSound`, ...).
- `R7K3.lean`: `Lane4.R7K3.head_sound : Lane4.R7K3.HeadSound`, the head lemma: a head
  passing `headOK` returns a vector in `headOut ... (some (tok j))` when `j` is the latest
  candidate position (`Latest`), in `headOut ... none` when there is no candidate, and all
  radii of `headOut` are non-negative.
- `R7K4.lean`: `Lane4.R7K4.abs_closed`, `abs_len`, `abs_target`, `abs_pick`: the abstract
  state of every input prefix is in a closed state set; it has one pick per head; the task
  target is the automaton output on it; and `pickAt` applied to its pick is `none` exactly
  when no allowed position is a candidate, `some t` with `t` the token at the latest
  candidate position otherwise.

**The argument.** Fix everything `Sound` quantifies over; write `δ = 1/1000` (a rational;
its cast is the real `1/1000` of `p.Within`), `n = w.length + 1`, `tok j = tokAt w j`,
`E = N.embed.map (embIV δ)`.

1. *Open `check`.* `check` matches on `N.blocks`; it can only be `true` when
   `N.blocks = [B]`. Then a conjunction of Booleans: `N.shapeOK T.ntok`, `weightsOK N B`,
   `c.cands.length == B.heads.length`, `headOK` for each head with its candidate list
   (a `zipWith ... |>.all id`), every state has `B.heads.length` picks, the initial state
   (`absInit T c.cands`, same expression) is in `c.states` (`List.contains`), and for every
   state and every `k < T.ntok`, `caseOK δ N B T c E st (k + 1)`. Turn it into named `Prop`
   facts once (`Bool.and_eq_true`, `List.all_eq_true`, `decide_eq_true_eq`, `beq_iff_eq`,
   `List.contains_iff_mem` or `List.elem_iff`).
2. *`Ctx`.* From the hypotheses of `Sound`; `2^40 ≤ M` follows from
   `2^40 * (w.length + 1)^2 ≤ M`.
3. *The input states.* `N.init fl p w j = aswRow fl (N.embed.getD (tok j) []) (p.E (tok j)) 0`.
   Tokens of `w` are in `1..T.ntok`, `tok 0 = 0`, and `N.shapeOK T.ntok` gives
   `N.embed.length = T.ntok + 1` with all rows of one length `d ≤ 24`. `emb_sound` (with
   `smallM N.embed` from `weightsOK`) puts the state at `j` in `E.getD (tok j) []`, and
   every row of `E` is `Bdd 16` of length `d`.
4. *The run.* `N.run fl ex p w = arunFrom fl ex p n [B] 0 (N.init fl p w) = B.apply fl ex p 0 n (N.init fl p w)`
   (unfold; `rfl` after rewriting `N.blocks = [B]`).
5. *The closed state.* Let `st = absState T c.cands (w.take (i - 1))`. By `abs_closed`
   (closure: the second conjunct of `caseOK` for each state and token is exactly
   `absStep T c.cands st t ∈ c.states`) `st ∈ c.states`, so `caseOK δ N B T c E st (tok i)`
   holds (`1 ≤ tok i ≤ T.ntok`, and `tok i = w.getD (i - 1) 0` is a member of `w`).
   `caseOK` gives `outOK` (the magnitude guards), the bound
   `qabs (o.1 - T.out st.1 (tok i)) + o.2 ≤ 1/4` for `o = outIV δ N B E c.cands (tok i) sel`,
   with `sel` the `zipWith` of `pickAt` over `zip B.heads c.cands` and `st.2`.
6. *The heads.* Show by induction over a suffix of `B.heads` (generalise the head index
   `k`, the accumulator and its interval, and the matching suffixes of `c.cands` and `sel`):
   `aheadsApply fl ex p 0 n x i hs acc k` lies in `headsOut δ E hs cds ps accv`, given
   `acc` in `accv` with non-negative radii, `headsOK δ E hs cds ps accv = true`, and for
   each head in the suffix: its `headOK`, its shape and weight guards, and what its pick
   means. For one head: its pick is `pickAt h cd (tok i) (st.2.getD k none)`; `abs_pick`
   (head index `a = k`, `h.mask ≠ Mask.all` is the first conjunct of `headOK`) turns it
   into `Latest` or "no candidate", and `head_sound` (with `dd = d`, perturbations
   `p.A 0 k`, `p.V 0 k`, `p.m 0 k`, `p.g 0 k`, `p.gb 0 k` bounded by `p.Within`) puts
   `h.attn ...` in `headOut δ E h cd pick`; then `add_sound` with the guard from
   `headsOK`. The start is `acc = x i` in `E.getD (tok i) []` (radii of `embIV` are `e0 δ ≥ 0`).
   An index-free way to carry "the pick of head `k`" through the induction is to state the
   hypothesis for all heads at once as: for every position `a` in the full list,
   `sel.getD a none = pickAt (B.heads.getD a _) (c.cands.getD a []) (tok i) (st.2.getD a none)`,
   and peel lists with `List.getD_cons_succ`.
7. *The MLP and the read-out.* With `y` the result of step 6 (in `yv = headsOut ...`,
   `Bdd 15` from `add_sound`, or `Bdd 16` if there is no head):
   `aff_sound` for `W1, b1` (guard `a1.all small` from `outOK`; row lengths from
   `B.shapeOK d`), `relu_sound`, `aff_sound` for `W2, b2`, `add_sound` for the residual
   sum. For the read-out, `ANet.out = fl (ardot fl N.outW z p.oW 0 0 + asw fl N.outB p.oB)`
   is the single entry of `araffine fl [N.outW] [N.outB] z (fun _ => p.oW) (fun _ => p.oB) 0`,
   and `outIV` is the single entry of `affIV δ [N.outW] [N.outB] zv`, so `aff_sound`
   applies once more (its guard is `small (outIV ...)` from `outOK`). `Bdd 15` implies
   `Bdd 16`.
8. *Conclusion.* `InIV out o` and `qabs (o.1 - target) + o.2 ≤ 1/4` give
   `|out - target| ≤ 1/4` by the triangle inequality after casting (`abs_target` rewrites
   `T.target w i` as `T.out st.1 (tok i)`; the cast of a natural number through ℚ to ℝ:
   `push_cast`, `Nat.cast` lemmas).

**Hints.**
- Split the work into lemmas in that order and submit after each (a partial file FAILS at
  `Final.lean` but shows the errors Lean finds in your part). Do not write the whole proof
  before the first submission. The heads induction (step 6) is the largest piece; a
  network with zero heads must also be covered (then `headsOut` is the accumulator).
- `outIV` and `outOK` both start with `let`s; `simp only [outIV, outOK]` or `show` with the
  unfolded term, then name the intermediate interval vectors with `set` or `generalize`.
- Shapes: `N.shapeOK T.ntok` unfolds through a `match N.embed`; `rowsOK M r c` is
  `M.length == r && M.all (fun row => row.length == c)`. `B.shapeOK d` gives at most 4
  heads, `b1.length ≤ 32`, `W1` with `b1.length` rows of length `d`, `W2` with `d` rows of
  length `b1.length`, `b2.length = d`; `N.outW.length = d`. Lengths of intermediate
  vectors come from `InIVs` (first component) and from `araffine`/`radd`/`map` length
  lemmas you prove by induction.
- If `Sound` is false as written, or a guard is missing from the checker for this
  argument, say so in your reply with the exact place instead of spending submissions.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r7-kit/k5"

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
