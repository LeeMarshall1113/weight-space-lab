"""Build the rung-7 kit case folders k4 (automaton lemma) and k3 (head lemma).
Spec.lean of each case is written by hand beforehand; this adds Final.lean, case.json,
TASK.md and the framework copies."""
import json, shutil, os

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(HERE)
nl = "\n"
t = open("runs/r7-kit/kT/TASK.md", encoding="utf-8").read()


def mk(cid, imp, names, head, copies):
    K = "runs/r7-kit/%s/" % cid
    os.makedirs(K + "scratch", exist_ok=True)
    for c in copies:
        shutil.copy("Lane4/" + c, K + c)
    body = ("⟨" + ", ".join("Lane4.Case." + b for _, b in names) + "⟩") if len(names) > 1 else "Lane4.Case." + names[0][1]
    fin = ("namespace Lane4Final" + nl + "theorem final : " + " ∧ ".join("Lane4.Case." + a for a, _ in names) + " :=" + nl
           + "  " + body + nl + "end Lane4Final" + nl + "#print axioms Lane4Final.final" + nl)
    open(K + "Final.lean", "w", encoding="utf-8", newline=nl).write(fin)
    json.dump({"id": cid, "arm": "kit", "rung": 7, "import": imp, "final_theorems": ["Lane4Final.final"],
               "max_attempts": 30, "lean_timeout": 600}, open(K + "case.json", "w"))
    rules = t[t.index("## Rules"):].replace("r7-kit/kT", "r7-kit/" + cid)
    open(K + "TASK.md", "w", encoding="utf-8", newline=nl).write(head + rules)


K4 = '''# Task: the abstract states of the certificate checker mean what they should

This is framework work, not a test. Prove the four statements in `Spec.lean`. They are
about lists and natural numbers only: no real numbers, no rounding.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)` and
`open Lane4.AGate Lane4.Cert`):

- `theorem abs_closed : AbsClosed`
- `theorem abs_len : AbsLen`
- `theorem abs_target : AbsTarget`
- `theorem abs_pick : AbsPick`

and whatever helper lemmas you need. The checker builds one file from
`import Lane4.R7Defs` (which imports R7Cert, AGateAll, ..., Mathlib), then `Spec.lean`,
then your `Solution.lean`, then `Final.lean`.

**Background.** Read `R7Defs.lean` and `R7Cert.lean` (copied here; in `R7Cert.lean` you
need only `Task`, `Task.target`, `pickAt`, `pickNext`). `Seq.lean` (copied) has
`cand` and `tokAt`:

    def cand (m : Mask) (n i : ℕ) : List ℕ :=
      match m with
      | Mask.all => List.range n | Mask.causal => List.range (i + 1) | Mask.strict => List.range i
    def tokAt (w : List ℕ) (i : ℕ) : ℕ := (0 :: w).getD i 0

An input is a list `w` of tokens; position 0 holds the BOS token 0 and position `i ≥ 1`
holds `w[i-1]`. A task is an automaton (`Task`: `init`, `step`, `out`). Each attention
head has a set of candidate tokens `cd : List Bool` (indexed by token, BOS is index 0).
The abstract state after reading a prefix (`absState`) is the task state together with,
per head, the most recent candidate token seen so far, BOS included (`none` if there has
been none). `pickAt` then gives the token a head attends to at the query position: for a
causal mask the token of the query itself if it is a candidate, otherwise the stored pick.

- `AbsClosed`: induction along the prefix (prove it for `foldl` from an arbitrary state in
  the set, or use `List.reverseRecOn` with `List.foldl_append`).
- `AbsLen`: `zipWith` keeps the length when both lists have the same length; the initial
  pick list is a `map` over `cands`.
- `AbsTarget`: unfold `Task.target`; the first component of `absState` is
  `foldl T.step T.init` of the prefix (a small induction, generalising the start state),
  and for `1 ≤ i` the token `tokAt w i` is `w.getD (i - 1) 0`.
- `AbsPick` is the real work. A good invariant, by induction on `k` for the prefix
  `w.take k` with `k ≤ w.length`: with
  `p = (absState T cands (w.take k)).2.getD a none` and `cd = cands.getD a []`,
  `p = none → ∀ j ≤ k, cd.getD (tokAt w j) false = false`, and
  `p = some t → ∃ j ≤ k, tokAt w j = t ∧ cd.getD t false = true ∧
     ∀ j2 ≤ k, cd.getD (tokAt w j2) false = true → j2 ≤ j`.
  (`tokAt w 0 = 0`; `tokAt w (k + 1) = w.getD k 0`; `w.take (k + 1) = w.take k ++ [w.getD k 0]`
  when `k < w.length`.) Then take `k = i - 1` and split on the mask: for `Mask.strict` the
  allowed positions are `j < i`, that is `j ≤ i - 1`; for `Mask.causal` they are `j ≤ i`,
  and `pickAt` adds the token of the query when it is a candidate. `List.mem_range` turns
  membership in `cand` into inequalities. The entry `a` of a `zipWith` is the function of
  the two entries (`List.getD` through `zipWith`, both lists of length `cands.length`).

**If a statement is false as written, say so in your reply with the counterexample instead
of spending submissions.** You may submit a partial file (some theorems missing) to see
whether what you have compiles; it will FAIL at `Final.lean` but shows the errors Lean
finds in your part.

'''

K3 = '''# Task: the head lemma of the certificate checker

This is framework work, not a test. Prove the one statement in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.Seq (Mask cand tokAt)`,
`open Lane4.RSeq (Vec pdot radd)` and `open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2`):

- `theorem head_sound : HeadSound`

and whatever helper lemmas you need. The checker builds one file from `import Lane4.R7B3`
(which imports R7K2, R7K1, R7Defs, R7Cert, AGateAll, ..., Mathlib), then `Spec.lean`, then
your `Solution.lean`, then `Final.lean`.

**Background. Read these copies first:** `AGate.lean` (the head: `AHead.gate`,
`AHead.cands`, `AHead.bias`, `AHead.score`, `aattnRows`, `AHead.attn`), `R7Cert.lean` (the
checker: `gateDec`, `scoreIV`, `scoreOK`, `slopeRoom`, `gap`, `valBound`, `headOK`,
`headOut`), `R7Defs.lean` (`Latest`), and the STATEMENTS at the top of `R7K2.lean`
(`Ctx`, `InIV`, `InIVs`, `Bdd`, and the eight proved interval lemmas, available as
`Lane4.R7K2.dot_sound`, `mat_sound`, `gate_sound`, `score_sound`, ...) and of `R7K1.lean`
(`Lane4.R7K1.savg_near12 : Lane4.R7K1.SavgNear12`, the softmax lemma with a score gap of
12 per unit of distance). From the older kit: `bias_gap : BiasGap` (AGateKit.lean),
`soft_zeros` (RSoftKit.lean), `Rnd.near`, `Rnd.abs`, `Rnd.bound` (RSoft.lean).

**The argument.** Fix the query position `i` (token `tok i ≥ 1`) and write `E[t]` for row
`t` of the interval table.

1. *Candidates.* `headOK` says `cd.length = E.length` and `gateDec δ h E[t] = some cd[t]`
   for every row `t`. With `gate_sound` (state `x k` lies in `E[tok k]`, `h.g.length = dd`
   from `h.shapeOK dd`): position `k` passes the gate filter iff `cd[tok k] = true`. So
   `h.cands fl dg dgb n x i` is exactly the positions `k ∈ cand h.mask n i` whose token is
   a candidate token; it is duplicate-free (a filter of `List.range`).
2. *No candidate.* If no allowed position holds a candidate token the list is empty, each
   row of `aattnRows` is `savg` over the empty list, which is 0 (`soft_zeros`, or unfold),
   and `headOut ... none` is the zero intervals of the same length (`h.V.length`).
3. *Winner.* Otherwise let `j` be the latest candidate position (`Latest`). For another
   candidate `k` (so `k < j`): with `s k = fl (bias k + content k)`,
   - `bias_gap`: `bias k + (m - δ) * (j - k) - (m + 2) / 32 ≤ bias j`, and
     `|bias| ≤ (m + 2) * (n + 1)`; its hypotheses `1 ≤ m ≤ 1024` are in `headOK`, its `n`
     is the `n` here (positions are `< n`), and `2^12 * (n + 1) ≤ M` follows from
     `2^40 * n^2 ≤ M` and `1 ≤ n`.
   - `score_sound` (query row `E[tok i]`, key rows `E[tok j]`, `E[tok k]`; `scoreOK` for
     candidate keys and query rows `E.drop 1` is in `headOK`): each content score is in
     its interval and at most 1024 in size; the pair condition in `headOK` gives
     `content k - content j ≤ slopeRoom δ h = m - δ - 12 - 3 * (m + 2) / 64`.
   - rounding the sum: `|bias + content| ≤ (m + 2) * (n + 1) + 1024`, so `fl` moves it by
     at most `u * ((m + 2) * (n + 1) + 1024) + η`, and `u * n ≤ 1/256`, `u ≤ 2^-24` make
     this at most `(m + 2) / 256 + 2^-12` (the exact small constant is yours to choose).
   - together: `s j - s k ≥ (m - δ) * (j - k) - (m + 2)/32 - 2 * ((m + 2)/256 + 2^-12)
     - slopeRoom ≥ 12 * (j - k)`, using `j - k ≥ 1`, `m - δ - 12 ≥ 0` and
     `(m + 2) / 128 ≥ 3 / 128 > 2^-11`. (`ndist j k` cast to ℝ is `|j - k|`:
     `ndist_cast`.)
   - `savg_near12` with `f k = ardot fl r (x k) (dV row) 0 0` for a row `r` of `V`:
     `dot_sound` puts `f k` in `dotIV δ r E[tok k]`, so `|f k| ≤ B` with `B` the entry of
     `valBound` for that row (a `foldl max` over the candidate rows: show it bounds
     `|centre| + radius` of every candidate row), and `B ≤ 2^20` from `headOK` gives
     `4 * B + 4 ≤ M`. Score bound `Sb = (m + 2) * (n + 1) + 1025` or similar, `2 * Sb ≤ M`.
     Result: `|savg - f j| ≤ B / 100 + 2^-90`, hence `savg` lies in the interval
     `(centre of dotIV δ r E[tok j], its radius + B / 100 + 2^-90)`, which is the entry of
     `headOut ... (some (tok j))`.
4. *Rows.* `aattnRows` recurses over the rows of `V` with the row index going up from 0;
   `headOut` is a `zipWith` over `matIV δ h.V E[t]` and `valBound`. Prove the row statement
   for an arbitrary start index and a suffix of the rows.
5. *Radii.* The last conjunct (`0 ≤` every radius of `headOut`) is arithmetic:
   `dot_sound`/`mat_sound` give non-negative radii, `valBound` entries are `≥ 0` (the fold
   starts at 0).

**Hints.**
- Split the work into lemmas in that order and submit after each (a partial file FAILS at
  `Final.lean` but shows the errors Lean finds in your part). Do not write the whole proof
  before the first submission.
- `headOK` is a conjunction of Booleans: open it once into named `Prop` facts
  (`Bool.and_eq_true`, `decide_eq_true_eq`, `List.all_eq_true`, `beq_iff_eq`), with the
  `zipWith`/`zip` parts turned into statements about indices `t < E.length`.
- Keep rational-to-real casts in small lemmas (`Rat.cast_le`, `push_cast`); the cast of
  `slopeRoom δ h` is the real expression above.
- If the statement is false as written, or a constant in the checker is too small for the
  argument, say so in your reply with the exact place instead of spending submissions.

'''

mk("k4", "R7Defs", [("AbsClosed", "abs_closed"), ("AbsLen", "abs_len"), ("AbsTarget", "abs_target"), ("AbsPick", "abs_pick")],
   K4, ["R7Defs.lean", "R7Cert.lean", "Seq.lean"])
mk("k3", "R7B3", [("HeadSound", "head_sound")], K3,
   ["AGate.lean", "AGateKit.lean", "RSoftKit.lean", "RSoft.lean", "RSeq.lean", "Seq.lean", "R7Cert.lean", "R7Defs.lean",
    "R7K2.lean", "R7K1.lean"])
print("built k4, k3")
