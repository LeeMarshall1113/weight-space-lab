# this study, rung 6c pre-registration: a necessary radius for every token-blind network

**STATUS: REGISTERED, 2026-11-14 evening (EST), before any proof attempt.** No proof of
any statement below has been attempted by the study team or by an agent, and the membership
checks have not been run in Lean. What exists: the statement file `Lane4/TokenBlind.lean`
(definitions and `Prop`s), a type-check of it (`scratch/R6cStatements.lean`, compiled
under a memory reservation: the five `#check`s print their types), an exact-rational numeric test of
the statements on the ten proved rung-2 networks, and the scope note `SCOPE_R6C.md`.
The private commit is not independently verifiable; frozen hashes are at the bottom.

## Framing: whose phenomenon this is

Hahn and Rofin (arXiv:2402.09963, Theorem 6) show that soft-attention encoders with layer
norm computing highly sensitive functions sit at sharp points of parameter space: an
average-case bound over random perturbations of all parameters, as a limit in input
length and radius. That is the general effect. It does not formally imply the statements
here (ours are worst-case inside a relative ball with zeros fixed, a measure-zero family
of their directions; hard attention; unbounded exact position features; an explicit
radius at each length), and ours do not imply theirs. If this rung passes, the fair
description is: a machine-checked, worst-case, explicit-constant form of a known effect,
for a decidable class of networks. We read their article through the abstract and a
summarising fetch of the first 100,000 characters of the HTML version; proofs not read.

## The class (decidable)

`tokenBlind N ntok T : Bool` (exact text in `Lane4/TokenBlind.lean`). `T` is a list of
embedding coordinates. The condition holds when: the network has the rung-2 shape; every
coordinate in `T` is an embedding coordinate; all real tokens `1..ntok` have the same
embedding entry at every embedding coordinate not in `T`; every head either has an
all-zero score matrix and mask `all`, or has no nonzero score entry in a row or column of
`T` and no nonzero value entry in a column of `T`; no MLP first-layer entry in a column
of `T` is nonzero; no read-out entry on `T` is nonzero. It depends only on which entries
are zero (and on equalities between embedding entries off `T`), so it is unchanged by
any relative perturbation that keeps those embedding entries equal; the proofs perturb
only embedding entries on `T`.

## The statements (exact text in `Lane4/TokenBlind.lean`)

1. **`Invariance`.** `N` token-blind for `T`; `N₁`, `N₂` equal to `N` except for
   embedding entries on `T`; `w₁`, `w₂` valid, of equal length, with equal column sums of
   their embedded tokens on every coordinate of `T`. Then `N₁.out w₁ i = N₂.out w₂ i` at
   every position `i ≤ length`.
2. **`Collision`.** `N` token-blind, `s`, `o` real tokens, `τ ≤ 1`, `a, b ≥ 1`,
   `1 ≤ τ(2a+1)`, `1 ≤ τ(2b+1)`. Then there are `N₁`, `N₂` in the relative ball of radius
   `τ` around `N` with equal outputs at every position on `s^a o^(b+1)` and `s^(a+1) o^b`.
3. **`ParityBound`.** `N` token-blind, a counted token and an uncounted token, wanted
   parity 0 or 1: if every network in the ball of radius `τ ≤ 1` is correct for the
   parity task up to length `2a+1` (`a ≥ 1`), then `τ(2a+1) < 1`.
4. **`SortBound`.** `N` token-blind over at least two tokens: if every network in the
   ball is correct for sort rank (the rung-2 spec: the output at position `i` is the
   `i`-th smallest token, as an exact integer) up to length `2a+1`, then `τ(2a+1) < 1`.

**Constant.** `τ < 1/L` at odd length `L = 2a+1`, the same for every network of the
class. It is about twice weaker than rung 6b's `1/(2L−1)` because both tokens'
embeddings may be nonzero on `T`.

**Membership.** `tokenBlind net ntok T = true` for p05, p10, p29 (`T = [0]`), s00
(`T = [1]`) and s01 (`T = [0, 1]`), with the exact network text proved at rung 2, to be
established by a mechanical check: `decide`, `decide +kernel`, `rfl`, or `simp`/`norm_num`
with only the definitions unfolded. `native_decide` stays banned. No per-network
argument is allowed in a membership proof.

**Corollaries the study team derives** per member network: the radius bound for its own task,
and "for every `τ > 0` some length fails".

## Numeric test before registration (done; exact rationals)

`scratch/r6c_statement_test.py`, results `results/r6c-statement-test.json`, log
`logs/r6c-statement-test.log`. On the exported exact weights of the ten proved rung-2
networks:
- The condition, written in Python as in Lean, holds for p05, p10, p29, s00, s01 and
  fails for the other five for the reasons the scope note gave: d10, d15, d18: the
  token-reading head is a causal average, not a global one; a00, a01: a strict-mask head
  whose score reads tokens, and an MLP that reads tokens (a01 also the read-out).
- Each of the five non-members is not permutation-invariant even unperturbed (the inputs
  `[1, 2]` and `[2, 1]` give different outputs), so no statement of the form of
  `Invariance` could hold for them. They are outside the class for a real reason.
- Members, `Invariance`: 30 trials each with a random input of length 2 to 9, a random
  permutation of it, every non-embedding weight randomly perturbed within 2% (the same
  in both runs) and embedding entries on `T` randomly scaled: outputs equal at every
  position, 30 of 30, for all five.
- Members, `Collision`: for `(a, b)` = (1,1), (2,3), (4,4), (5,2), with `τ` the smallest
  radius the statement allows: equal outputs at every position for all five networks;
  and with only the embedding moved, at (4,4), one of the two answers is wrong for the
  task (parity: sign at the last position; sort: the value at position `a+1`).
No contradiction with the 2x2 version 2 either: at relative 1/200 the statement asserts
breaks from odd length 201; the screen found breaks for all five of these networks at
length 1,000, and found some earlier (other weights move too).

## Plan, agents, budget

Proof cases under `runs/r6c/`, each importing the unchanged module `Seq`, one Sonnet
doctor at a time, fresh agent per case, 12 submissions, the rung-5 doctor prompt:
1. `iHead`: the head step. With the invariant `Agree T d n x y` (states of length `d`
   that agree off `T` at every position below `n`, with equal column sums on `T`), a
   token-blind head gives equal outputs at every position below `n`.
2. `iNet`: the block step, the induction over blocks and the read-out: `Invariance`,
   with the proved head step included in its Spec.
3. `cColl`: `Collision` from `Invariance`.
4. `cBounds`: `ParityBound` and `SortBound` from `Collision`.
5. Memberships and corollaries: by the study team, mechanically, compiled under a memory reservation.
At most 2 fresh Sonnet attempts per statement; if the head step stalls twice the
coordinator is asked for one Fable step (a lab rule); the study team does not start it.
Estimated 4 to 8 Sonnet cases, 1 to 2.5M tokens. Usage: theorem line, no new case at or
above 70% weekly, hard stop 75%; checked and logged before each case.
Intermediate statements written by the study team for cases 1 and 2 (`Agree`, `HeadStep`) are
not registered claims; if one is false it is corrected without an amendment, and that is
logged. The four registered statements change only by dated amendment.

## Bars (set now)

- **Pass:** `Invariance` and `Collision` kernel-checked with standard axioms, at least
  one of `ParityBound`/`SortBound` kernel-checked, and membership of at least the three
  parity networks and one sort network by a mechanical check.
- **Kill:** a registered statement is false and cannot be repaired without making the
  class trivial (for example by assuming the invariance); or membership cannot be
  established mechanically for the networks (then the class is not usable as a
  syntactic one, and that is reported). A false statement repaired by adding a missing
  hypothesis is an amendment, reported, as at rung 6b.
- Partial results are reported as what they are: for example "invariance proved,
  membership not mechanical".
- **Headline wording if passed:** "for every rung-2 network that reads tokens only
  through global uniform averages (a decidable condition; 5 of our 10 proved networks),
  kernel-checked: no relative weight ball of radius 1/L or more is correct for parity
  or sort rank up to odd length L. A known effect (Hahn and Rofin) made worst-case,
  explicit and machine-checked for this class; hard attention, exact arithmetic."

## What would make the result weak, written down now

- The class is "permutation-invariant by construction". A network that reads tokens
  positionally is not covered; `ParityNoBall` stays a conjecture.
- The five member networks were written by the same model family for the same two task
  families.
- Relative ball, hard attention, exact rationals. The collision moves embedding entries
  only.
- The effect is known in general form; the contribution is the checked, explicit form.
- Dyck and addition are not covered (and are not attempted here).

## Frozen files

sha256 list in `scratch/freeze_r6c.sha256` (TokenBlind.lean, Collision.lean,
R6cStatements.lean, the test script and its results, the five rung-2 Solution files,
Seq.lean, Basic.lean); its own sha256 is in the commit message and the lab log.

## Correction (2026-11-14, 5:15 pm EST): time

"Evening" in the status line is wrong: the registration commit (02ef7d5) is stamped
4:34 pm EST. Nothing else changes.
