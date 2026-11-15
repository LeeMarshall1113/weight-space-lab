# Task: derive a collision theorem from an invariance theorem (Lean 4)

Prove `Lane4.TB.Invariance → Lane4.TB.Collision`. Both are defined in `Spec.lean` (the
`Lane4.TB` part); read there `tokenBlind`, `SameOffT`, `colSum`, `Invariance`, `Collision`,
and in the `Lane4.Coll` part `qRel`, `vRel`, `mRel`, `hRel`, `bRel`, `netRel`. In `Seq.lean`
read `TNet`, `TNet.shapeOK`, `rowsOK`, `tokAt` and the lemmas `tokAt_zero`, `tokAt_succ`.
You do NOT need the network evaluator: `Invariance` is a hypothesis.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll Lane4.TB`): `theorem collision_of_invariance : Invariance → Collision`.

**The intended argument (you may do it differently).**
- If `s = o` the two inputs are the same list (`replicate a s ++ replicate (b+1) s` and
  `replicate (a+1) s ++ replicate b s`; `List.replicate_add`/`List.replicate_succ` or
  `List.ext_getElem`), and `N₁ = N₂ = N` works: `netRel τ N N` holds because `0 ≤ τ`
  (from `1 ≤ τ * (2a+1)`) and every relation is reflexive (`|a - a| = 0 ≤ τ * |a|`;
  `List.Forall₂` reflexivity by induction, e.g. `List.forall₂_same` / `List.Forall₂.imp`).
- If `s ≠ o`. Let `d₁s = (1 - τ*(a+1))/a`, `d₂s = -τ`, `d₁o = -τ`, `d₂o = (1 - τ*(b+1))/b`.
  All four have absolute value at most `τ` (uses `τ ≤ 1`, `1 ≤ τ*(2a+1)`, `1 ≤ τ*(2b+1)`,
  `a, b ≥ 1`), and `a*(1+d₁s) = (a+1)*(1+d₂s)`, `(b+1)*(1+d₁o) = b*(1+d₂o)`.
  Define, for factors `fs fo : ℚ`, the network `scale N T s o fs fo` equal to `N` except
  that in embedding row `s` every entry at a coordinate in `T` is multiplied by `fs`, and
  in row `o` by `fo`. One way: `embed := N.embed.zipIdx.map (fun (row, t) => row.zipIdx.map
  (fun (v, c) => if c ∈ T then (if t = s then v * fs else if t = o then v * fo else v) else v))`
  (or `List.mapIdx`; use whatever indexing API you can make compile; if unsure of a lemma
  name, prove the small `getD` facts you need by induction on the list).
  `N₁ = scale N T s o (1+d₁s) (1+d₁o)`, `N₂ = scale N T s o (1+d₂s) (1+d₂o)`.
  * `netRel τ N Nᵢ`: blocks, read-out unchanged (reflexivity); each embedding entry is
    either unchanged or `v * (1 + d)` with `|d| ≤ τ`: `|v*(1+d) - v| = |d|*|v| ≤ τ*|v|`.
  * `SameOffT N Nᵢ T`: same blocks, read-out, same number of rows, same row lengths,
    entries off `T` unchanged.
  * Inputs `w₁ = replicate a s ++ replicate (b+1) o`, `w₂ = replicate (a+1) s ++ replicate b o`
    are valid and have the same length `a + b + 1`.
  * Column sums: for `c ∈ T`, with `E t = (N.embed.getD t []).getD c 0`:
    `colSum N₁ w₁ c = E 0 + a * (E s * (1+d₁s)) + (b+1) * (E o * (1+d₁o))` and
    `colSum N₂ w₂ c = E 0 + (a+1) * (E s * (1+d₂s)) + b * (E o * (1+d₂o))`; equal by the two
    identities. (`colSum` sums over positions `0..length`; position 0 is BOS, token 0;
    tokens `s`, `o` are `≥ 1` so row 0 is never scaled. A helper: for any `g : ℕ → ℚ`,
    `((List.range (w.length+1)).map (fun j => g (tokAt w j))).sum = g 0 + (w.map g).sum`,
    then `List.map_append`, `List.map_replicate`, `List.sum_replicate`, `smul_eq_mul`,
    `nsmul_eq_mul`.)
  * Apply `Invariance` with `N, N₁, N₂, ntok, T`.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      python <repo>/tools/submit.py "<repo>/runs/r6c/cColl"

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
