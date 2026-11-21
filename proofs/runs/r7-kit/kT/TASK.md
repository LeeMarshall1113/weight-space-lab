# Task: prove that a network perturbed by the difference to a second network IS the second network

This is framework work, not a test. Prove the two statements in `Spec.lean`.

**What to write.** `Solution.lean` in this folder, with no `import` line, containing,
inside `namespace Lane4.Case` (with `open Lane4.RSeq (Vec)`, `open Lane4.RSoft Lane4.AGate`
and `open Lane4.Seq (Mask cand tokAt)`):

- `theorem out_shift : OutShift`
- `theorem diff_within : DiffWithin`

and whatever helper lemmas you need. The checker builds one file from
`import Lane4.AGateAll` (AGateKitW, AGateKit, AGate, RSoftKit, RSoft, RSeq, Seq, Basic,
Mathlib), then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**Background.** `AGate.lean` (copied here, read it first) defines the forward pass
`ANet.out N fl ex p w i` of a network `N` under an additive perturbation `p : APert`: every
written weight `a` is used as `asw fl a d = fl (a + d)` with its own `d` taken from `p`.
`Spec.lean` defines `diffP W T`, the perturbation whose entries are the weights of `T`
minus the weights of `W` (0 where an index is out of range), and `zeroP`.

- `OutShift`: if `W` and `T` have the same shape (`sameShape W T = true`: same list
  lengths everywhere and the same masks), then `W` under `diffP W T` and `T` under `zeroP`
  give the same output, for every `fl`, `ex`, input and position. The reason is one line:
  `asw fl a (b - a) = fl (a + (b - a)) = fl b = fl (b + 0) = asw fl b 0`, for every weight.
  The work is carrying that through every recursive definition of `AGate.lean`.
- `DiffWithin`: if also every pair of corresponding weights is within `δ`
  (`nearNet δ W T = true`), then `(diffP W T).Within δ`. Out-of-range entries are
  `0 - 0 = 0` and `0 ≤ δ`.

**Hints (you may ignore them). If a statement is false as written, say so in your reply
with the counterexample instead of spending submissions.**

- Prove one lemma per recursive definition, by induction on the lists with the index
  generalised: `aswRow`, `ardot`, `armat`, `araffine`, `aattnRows`, then `AHead.gate`,
  `AHead.cands`, `AHead.bias`, `AHead.score`, `AHead.attn`, `aheadsApply`, `ABlock.apply`,
  `arunFrom`, `ANet.init`, `ANet.run`, `ANet.out`. A convenient form: two weight lists
  `r r'` of equal length and two offset functions `d d'` with
  `∀ k, k < r.length → (r.getD k 0 : ℝ) + d (j + k) = (r'.getD k 0 : ℝ) + d' (j + k)`
  give `ardot fl r x d j acc = ardot fl r' x d' j acc`; then instantiate `d = dq r r'`
  (shifted) and `d' = 0`.
- `List.getD` on a `cons` shifts the index by one; `List.zipWith ... |>.all id = true`
  unfolds by induction (`List.all_cons`, `Bool.and_eq_true`).
- `aheadsApply` takes the head index `k` and uses `p.A b k`; `hd W b k` is
  `(blk W b).heads.getD k nilHead`, so relate the tail of the heads list at offset `k` to
  `getD`. The same for blocks in `arunFrom` with block index `b`.
- `dq` casts a rational difference to a real: `push_cast` then `ring` or `linarith`.
- For `DiffWithin`: from `nearL δ a b = true` and equal lengths get
  `∀ c, |dq a b c| ≤ δ` (in range: the two inequalities of `nearQ`, cast to reals with
  `Rat.cast_le`; out of range: both `getD` are 0).
- You may submit partial files to see whether they compile; they will FAIL at
  `Final.lean` but show Lean's errors for your part.

## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      C:/Python314/python.exe tools/submit.py "runs/r7-kit/kT"

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
