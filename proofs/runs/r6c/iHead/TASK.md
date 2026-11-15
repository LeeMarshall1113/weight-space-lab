# Task: prove one lemma about a hard-attention head (Lean 4)

Prove `Lane4.Inv.HeadStep`, defined at the end of `Spec.lean`. Read there: `Agree`,
`HeadStep`, and (in the `Lane4.TB` part) `zeroOn`, `isZero`, `blindScore`, `headBlind`.
In `Seq.lean` read `qdot`, `matVec`, `cand`, `Head.score`, `Head.sel`, `avg`, `Head.attn`,
`rowsOK`, `Head.shapeOK`, and the kit lemmas `mem_cand_all`, `mem_cand_causal`,
`mem_cand_strict`, `sel_all`.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv`): `theorem head_step : HeadStep`, plus
helper lemmas. The checker builds one file from `import Lane4.Seq` (which imports
Mathlib), then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**What the statement says.** `x` and `y` are two families of state vectors. At every
position `j < n` both have length `d`, they agree at every coordinate `c ∉ T`, and for
each `c ∈ T` the sums over `j < n` of coordinate `c` agree. The head `h` is "token-blind":
EITHER its score matrix `A` is all zeros and its mask is `all`, OR no entry of `A` in a
row `p ∈ T` or a column `q ∈ T` is nonzero and no entry of `V` in a column `c ∈ T` is
nonzero. Claim: `h.attn n x i = h.attn n y i` for `i < n`.

**The intended argument (you may do it differently).**
1. A formula for `qdot` that does not depend on list lengths:
   `qdot a b = ((List.range a.length).map (fun c => a.getD c 0 * b.getD c 0)).sum`
   (induction on `a` generalising `b`; a missing entry of `b` is `getD = 0`). From it:
   if `a.getD c 0 ≠ 0 → b.getD c 0 = b'.getD c 0` for all `c`, then `qdot a b = qdot a b'`.
2. Case "blind score and value" (`blindScore T h.A = true` and `h.V.all (zeroOn T) = true`):
   - for a row `r` with `zeroOn T r = true` and `j < n`: `qdot r (x j) = qdot r (y j)`
     (at `c ∈ T` the row entry is 0; at `c ∉ T` the states agree);
   - so `matVec h.A (x j)` and `matVec h.A (y j)` agree at every row index `p ∉ T`, and at
     `p ∈ T` the row `h.A.getD p []` is all zeros so both entries are 0 (or the row index
     is out of range and `getD` gives 0). Hence `h.score (x i) (x j) = h.score (y i) (y j)`
     for `i, j < n`: use the `qdot` formula on `qdot (x i) (matVec h.A (x j))` with
     `(x i).length = (y i).length = d`, splitting each term on `c ∈ T`
     (`List.getD_map`/`List.getD_eq_getElem?_getD` help with `(matVec A v).getD p 0`);
   - every candidate `k ∈ cand h.mask n i` has `k < n` when `i < n` (three masks), so
     `h.sel n x i = h.sel n y i` (`List.filter_congr`, the `decide`d propositions are
     equivalent because all scores agree);
   - `h.attn` is `h.V.map (fun row => avg sel (fun j => qdot row (x j)))`; selected `j`
     are candidates, so `< n`, and each `row ∈ h.V` has `zeroOn T row = true`.
3. Case "uniform" (`isZero h.A = true`, mask `all`): every score is 0 on both sides
   (`matVec` of an all-zero matrix is a list of zeros), so by `sel_all` both selections
   are `cand Mask.all n i = List.range n`. Then for each row
   `avg (List.range n) (fun j => qdot row (x j))`: write `qdot` by the formula of step 1
   and swap the two finite sums (`List.sum_map_...` lemmas, or convert to `Finset.sum`
   over `Finset.range` with `List.sum_range`-style lemmas and use `Finset.sum_comm`).
   The inner sum over `j` of coordinate `c` is equal for `x` and `y`: for `c ∈ T` by the
   third part of `Agree`, for `c ∉ T` termwise by the second part.
`h.shapeOK d` is available (`h.A` and `h.V` have `d` rows of length `d`) but you may not
need it. Membership `c ∈ T` for `T : List ℕ` is decidable; `List.all_eq_true` unpacks the
Boolean conditions; `beq_iff_eq` turns `(v == 0) = true` into `v = 0`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r6c/iHead"

  It prints PASS or FAIL with Lean's output. You have **12 submissions**; stop at the
  first PASS. A check can take up to 10 minutes and may also wait in a queue. Wait for
  it. Never resubmit while one is pending. You may submit a partial file (helper lemmas
  only) to see Lean's errors for your part; it will FAIL at `Final.lean`.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. Short Python for arithmetic is fine.
- Banned in `Solution.lean` (rejected without running Lean, still costs a submission):
  `sorry`, `admit`, `axiom`, `native_decide`, `macro`, `syntax`, `notation`, `elab`,
  `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`, anything in the `Lean.`
  namespace.
- Standard axioms only. Each check is limited to 600 s and 4.5 GB.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.
- **If the statement is false as written, say so in your reply with the counterexample
  instead of spending submissions.** That would be a useful result.

## When you finish

Reply with PASS or FAIL, the number of submissions used, and three or four sentences on
how you proved it and what went wrong. If you give up, say why and what is left.
