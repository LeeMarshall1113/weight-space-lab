"""Build rung-6c proof cases (PREREG_R6C.md) under runs/r6c/.

    python tools/make_r6c_cases.py iHead          (then iNet, cColl, cBounds as each predecessor passes)

Each case imports the unchanged module `Seq`. Spec.lean = text of Lane4/Collision.lean +
Lane4/TokenBlind.lean + the already proved predecessor solutions (moved to their own
namespaces) + the case's own statement. Existing folders are left alone.
"""
import json, os, shutil, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = lambda *p: os.path.join(HERE, *p)
read = lambda p: open(p, encoding="utf-8").read()
SUBMIT = 'python <repo>/tools/submit.py "<repo>/runs/r6c/%s"'


def body(name, ns):
    s = read(R("Lane4", name))
    return s[s.index("namespace " + ns):]


BASE = body("Collision.lean", "Lane4.Coll") + "\n\n" + body("TokenBlind.lean", "Lane4.TB") + "\n\n"

AGREE = """namespace Lane4.Inv
open Lane4.Seq Lane4.Coll Lane4.TB

/-- The invariant carried through the blocks: at every position below `n` the two state
families have length `d` and agree at every coordinate not in `T`, and for every
coordinate in `T` their column sums over the positions below `n` are equal. -/
def Agree (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) : Prop :=
  (∀ j, j < n → (x j).length = d ∧ (y j).length = d) ∧
  (∀ j, j < n → ∀ c, c ∉ T → (x j).getD c 0 = (y j).getD c 0) ∧
  (∀ c ∈ T, ((List.range n).map (fun j => (x j).getD c 0)).sum =
            ((List.range n).map (fun j => (y j).getD c 0)).sum)

/-- The head step: a token-blind head of the right shape gives the same output on the two
state families at every position below `n`. -/
def HeadStep : Prop :=
  ∀ (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (h : Head), Agree T d n x y →
    headBlind T h = true → h.shapeOK d = true →
    ∀ i, i < n → h.attn n x i = h.attn n y i

end Lane4.Inv
"""

RULES = """
## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      %s

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
"""

TASK_HEAD = """# Task: prove one lemma about a hard-attention head (Lean 4)

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
""" + RULES % (SUBMIT % "iHead")

FINAL_HEAD = """namespace Lane4Final
theorem final : Lane4.Inv.HeadStep := Lane4.Case.head_step
end Lane4Final
#print axioms Lane4Final.final
"""


BLOCK = """namespace Lane4.Inv
open Lane4.Seq Lane4.Coll Lane4.TB

/-- The block step: a token-blind block of the right shape preserves the invariant. -/
def BlockStep : Prop :=
  ∀ (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (B : Block), (∀ c ∈ T, c < d) → Agree T d n x y →
    blockBlind T B = true → B.shapeOK d = true → Agree T d n (B.apply n x) (B.apply n y)

end Lane4.Inv
"""

TASK_BLOCK = """# Task: prove that one transformer block preserves an invariant (Lean 4)

Prove `Lane4.Inv.BlockStep`, defined at the end of `Spec.lean`. `Spec.lean` also contains,
already proved, `Lane4.HeadProof.head_step : Lane4.Inv.HeadStep` (and its helper lemmas,
which you may use; read their statements). Read `Agree`, `HeadStep`, `BlockStep`,
`blockBlind`, `headBlind`, `zeroOn` in `Spec.lean`, and in `Seq.lean`: `qdot`, `vadd`,
`affine`, `Head.attn`, `Block.apply`, `rowsOK`, `Head.shapeOK`, `Block.shapeOK`.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv`): `theorem block_step : BlockStep`.
The checker builds one file from `import Lane4.Seq`, then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`.

**The intended argument (you may do it differently).** Fix `i < n`. Recall

    B.apply n x i = vadd y' (affine B.W2 B.b2 ((affine B.W1 B.b1 y').map (fun v => max v 0)))
    where y' = B.heads.foldl (fun acc h => vadd acc (h.attn n x i)) (x i)

1. By `head_step`, `h.attn n x i = h.attn n y i` for every `h ∈ B.heads` (each head is
   blind by `blockBlind`, has shape `d` by `B.shapeOK d`). Each `h.attn n x i` has length
   `d` (`h.V` has `d` rows). So the two folds add the SAME list of vectors, each of length
   `d`, to `x i` and to `y i`. Prove by induction on the list of heads (generalising the
   start vectors) that the results have length `d`, agree off `T`, and that for every
   coordinate `c < d` the increment `result.getD c 0 - start.getD c 0` is the same on
   both sides. Key fact: for `a`, `b` of length `d` and `c < d`,
   `(vadd a b).getD c 0 = a.getD c 0 + b.getD c 0`, and `(vadd a b).length = d`.
2. `affine B.W1 B.b1` gives the same list on both sides: each row of `B.W1` is zero on
   `T` (`blockBlind`), the two folded vectors have the same length and agree off `T`, so
   each `qdot row _` is equal (a congruence lemma of this kind should be among the helper
   lemmas of the head proof; check its exact name and hypotheses, or prove your own). So
   the MLP output `affine B.W2 B.b2 (...)` is literally the same list on both sides, of
   length `d` (`B.W2` has `d` rows and `B.b2` has length `d`; `affine` is a `zipWith`).
3. Conclude the three parts of `Agree` for the new states: lengths `d`; off `T` equal
   (old values equal, same increments); for `c ∈ T` (so `c < d`) the new coordinate is
   the old coordinate plus an increment that is the same on both sides, so the two sums
   over `j < n` change by the same amount (`List.sum_map_add`, or an induction on `n`).
`Bool` conditions unpack with `Bool.and_eq_true`, `List.all_eq_true`, `beq_iff_eq`,
`decide_eq_true_eq`; `rowsOK M r c = true` gives `M.length = r` and every row of length `c`.
"""

FINAL_BLOCK = """namespace Lane4Final
theorem final : Lane4.Inv.BlockStep := Lane4.Case.block_step
end Lane4Final
#print axioms Lane4Final.final
"""

TASK_NET = """# Task: prove an invariance theorem for token-blind transformers (Lean 4)

Prove `Lane4.TB.Invariance`, defined in `Spec.lean` (in the `Lane4.TB` part). `Spec.lean`
also contains, already proved: `Lane4.HeadProof.head_step : Lane4.Inv.HeadStep` and
`Lane4.BlockProof.block_step : Lane4.Inv.BlockStep`, with their helper lemmas (you may
use any of them; read their statements). Read `tokenBlind`, `SameOffT`, `colSum`,
`Invariance`, `Agree`, `BlockStep` in `Spec.lean`, and in `Seq.lean`: `pos`, `tokAt`,
`TNet.init`, `TNet.run`, `TNet.out`, `TNet.shapeOK`, `Block.shapeOK`, `rowsOK`, and the
lemmas `tokAt_zero`, `tokAt_succ`, `tokAt_zero_or_mem`.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv`): `theorem invariance : Invariance`.

**The intended argument (you may do it differently).** Let `de = (N.embed.getD 0 []).length`,
`d = de + 8`, `n = w₁.length + 1` (equal to `w₂.length + 1`).
1. Unpack `tokenBlind N ntok T = true`: `N.shapeOK ntok = true` (so `N.embed` is
   `e :: _` with `ntok + 1` rows, every row of length `de = e.length`, every block has
   `Block.shapeOK d`, `N.outW.length = d`); every `c ∈ T` has `c < de`; for `c < de`,
   `c ∉ T`, all rows `1..ntok` have the same entry at `c`; every block is `blockBlind T`;
   `zeroOn T N.outW`.
2. Initial states `x j = N₁.init w₁ j`, `y j = N₂.init w₂ j` satisfy `Agree T d n x y`:
   - lengths: `tokAt w j` is `0` or a member of `w` (so between 1 and `ntok`), hence a
     valid row index; rows of `N₁`, `N₂` have the lengths of the rows of `N` (`SameOffT`),
     which is `de`; `pos` has length 8.
   - off `T`: for `c < de`, `c ∉ T`: both entries equal the entry of `N` (`SameOffT`); at
     `j = 0` both tokens are BOS (`tokAt_zero`); at `1 ≤ j < n` both tokens are real, and
     real tokens agree at `c` in `N`. For `c ≥ de` the entry is a position feature
     `(pos j n).getD (c - de) 0`, the same on both sides (same `j`, same `n`).
   - sums on `c ∈ T` (`c < de`): `(x j).getD c 0 = (N₁.embed.getD (tokAt w₁ j) []).getD c 0`,
     so the sum is `colSum N₁ w₁ c`, and the hypothesis gives equality.
3. `TNet.run` is a `List.foldl` of `Block.apply n` over `N₁.blocks = N.blocks = N₂.blocks`.
   By induction on the list of blocks (generalising `x`, `y`), `block_step` gives
   `Agree T d n (N₁.run w₁) (N₂.run w₂)`. Mind that `n` is `w₁.length + 1` on one side
   and `w₂.length + 1` on the other: rewrite with the length hypothesis first.
4. `N₁.out w₁ i = qdot N₁.outW (N₁.run w₁ i) + N₁.outB`; `outW`, `outB` are those of `N`;
   `N.outW` is zero on `T` and the two final states at `i < n` have the same length and
   agree off `T`, so the two `qdot`s are equal.
"""

FINAL_NET = """namespace Lane4Final
theorem final : Lane4.TB.Invariance := Lane4.Case.invariance
end Lane4Final
#print axioms Lane4Final.final
"""


def proved(case, ns):
    """A proved Solution.lean moved from namespace Lane4.Case to its own namespace."""
    s = read(R("runs", "r6c", case, "Solution.lean"))
    assert "namespace Lane4.Case" in s and "end Lane4.Case" in s
    return s.replace("namespace Lane4.Case", "namespace " + ns).replace("end Lane4.Case", "end " + ns) + "\n\n"


TASK_COLL = """# Task: derive a collision theorem from an invariance theorem (Lean 4)

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
"""

FINAL_COLL = """namespace Lane4Final
theorem final : Lane4.TB.Invariance → Lane4.TB.Collision := Lane4.Case.collision_of_invariance
end Lane4Final
#print axioms Lane4Final.final
"""

TASK_BOUNDS = """# Task: derive two radius bounds from a collision theorem (Lean 4)

Prove `Lane4.TB.Collision → Lane4.TB.ParityBound` and `Lane4.TB.Collision → Lane4.TB.SortBound`.
All are defined in `Spec.lean` (the `Lane4.TB` part); read there `Collision`, `ParityBound`,
`IsRank`, `SortOnBall`, `SortBound`, and in the `Lane4.Coll` part `Task`, `Task.Valid`,
`Task.Correct`, `Task.OnBall`, `netRel`. You do NOT need the network evaluator.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll Lane4.TB`):

- `theorem parity_of_collision : Collision → ParityBound`
- `theorem sort_of_collision : Collision → SortBound`

**The intended argument (you may do it differently).** Both by contradiction: assume
`1 ≤ τ * (2a+1)` and apply `Collision` with `b = a` to get `N₁`, `N₂` in the ball with
equal outputs at every position `i ≤ 2a+1` on `w₁ = replicate a s ++ replicate (a+1) o`
and `w₂ = replicate (a+1) s ++ replicate a o`. Both inputs are valid, non-empty, of
length `2a+1` (`a + a + 1 = 2*a + 1`: `omega`).
- Parity: at `i = w.length = 2a+1`. The counts `countP K.inS` are `a` and `a+1`
  (`List.countP_append`, `List.countP_replicate`, with `K.inS s = true`, `K.inS o = false`).
  `OnBall` gives `0 < out ↔ a % 2 = par` and `0 < out ↔ (a+1) % 2 = par` for the same
  `out`; with `K.par < 2` this is contradictory (`omega` after extracting the two iffs).
- Sort: tokens `s = 1`, `o = 2` (`2 ≤ ntok`), position `i = a + 1`. `SortOnBall` gives
  `t₁`, `t₂ : ℕ` with `N₁.out w₁ (a+1) = t₁`, `IsRank w₁ (a+1) t₁` and likewise for `w₂`;
  equal outputs give `t₁ = t₂` (`Nat.cast_injective`). In `w₁ = 1^a 2^(a+1)`:
  `countP (· < t)` and `countP (· ≤ t)` are computed by `List.countP_append`,
  `List.countP_replicate` and a case split on `t` (`t = 0`, `t = 1`, `t = 2`, `t ≥ 3`);
  `IsRank w₁ (a+1) t` forces `t = 2`, and `IsRank w₂ (a+1) t` forces `t = 1`. Contradiction.
  A convenient helper: `(List.replicate m v).countP p = if p v then m else 0`.
"""

FINAL_BOUNDS = """namespace Lane4Final
theorem final : (Lane4.TB.Collision → Lane4.TB.ParityBound) ∧ (Lane4.TB.Collision → Lane4.TB.SortBound) :=
  ⟨Lane4.Case.parity_of_collision, Lane4.Case.sort_of_collision⟩
end Lane4Final
#print axioms Lane4Final.final
"""


def put(d, name, text):
    open(os.path.join(d, name), "w", encoding="utf-8", newline="\n").write(text)


def mk(cid, spec, final, task):
    d = R("runs", "r6c", cid)
    if os.path.exists(d):
        print("exists, left alone:", cid)
        return
    os.makedirs(os.path.join(d, "scratch"))
    put(d, "Spec.lean", spec)
    put(d, "Final.lean", final)
    put(d, "TASK.md", task)
    for f in ("Seq.lean", "Basic.lean"):
        shutil.copy(R("Lane4", f), os.path.join(d, f))
    json.dump({"id": cid, "arm": "kit", "rung": "6c", "import": "Seq", "final_theorems": ["Lane4Final.final"],
               "max_attempts": 12, "lean_timeout": 600}, open(os.path.join(d, "case.json"), "w"))
    print("built", cid)


if __name__ == "__main__":
    which = sys.argv[1]
    if which == "iHead":
        mk("iHead", BASE + AGREE, FINAL_HEAD, TASK_HEAD)
    elif which == "iBlock":      # argv[2] = folder name of the passing head case
        head = proved(sys.argv[2], "Lane4.HeadProof")
        mk("iBlock", BASE + AGREE + "\n" + head + BLOCK, FINAL_BLOCK,
           TASK_BLOCK + RULES % (SUBMIT % "iBlock"))
    elif which == "iNet":        # argv[2] = passing head folder, argv[3] = passing block folder
        head = proved(sys.argv[2], "Lane4.HeadProof")
        blk = proved(sys.argv[3], "Lane4.BlockProof")
        mk("iNet", BASE + AGREE + "\n" + head + BLOCK + "\n" + blk, FINAL_NET,
           TASK_NET + RULES % (SUBMIT % "iNet"))
    elif which == "cColl":
        mk("cColl", BASE, FINAL_COLL, TASK_COLL + RULES % (SUBMIT % "cColl"))
    elif which == "cBounds":
        mk("cBounds", BASE, FINAL_BOUNDS, TASK_BOUNDS + RULES % (SUBMIT % "cBounds"))
    else:
        sys.exit("unknown case " + which)
