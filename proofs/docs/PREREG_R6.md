# this study, rung 6b pre-registration: a necessary radius for counting through a uniform-attention average

**STATUS: REGISTERED, 2026-11-14 evening (EST), before any proof attempt.** No proof of
any statement below has been attempted by the study team or by an agent. What exists: the
statement file `Lane4/Collision.lean` (definitions and `Prop`s only), a type-check of it
together with the three membership statements (`scratch/R6Statements.lean`, compiled under
a reservation: all eight `#check`s print `Prop`), an exact-rational numeric sanity check, and a
novelty search. The private commit is not independently verifiable; the frozen hashes are
at the bottom. Rung 6a (`PREREG_R6A.md`, registered at f9b1c0e) is unchanged and now runs
after this rung.

## Where this comes from

An independent AI reviewer's review, point 8 (second independent read): prove a lower bound for a sharply
defined sub-class in which a count reaches the rest of the network only as the scaled
average `z = (1 + d)·k/n`. Two (count, perturbation) pairs with the same `z` and opposite
parity cannot both be answered correctly, which gives a necessary radius of order `1/L`.

## The claim under test, and what is NOT claimed

Claim: the statements below are kernel-checked in Lean 4 with the standard axioms, and at
least one of the three proved rung-2 parity networks (p05, p10, p29) is a kernel-checked
member of the class, so that for that network: **no relative weight ball of radius
`τ ≥ 1/(2L − 1)` is correct up to length `L`**.

Not claimed:
- `Lane4.Conj.ParityNoBall` or `ParityRadiusBound` (every network of the architecture).
  This rung proves a bound for networks with a count channel, and membership network by
  network. A network that counts another way is not covered.
- That the theorem is deep. The collision argument is a few lines of arithmetic. The
  value, if it passes, is a machine-checked necessary radius for networks we built, with
  an explicit constant, next to the kernel-checked proofs that the same networks are
  exactly correct at every length when unperturbed.
- Anything about soft attention, trained networks, additive perturbations, Dyck or sort.
- That the bound is tight for the full ball. It uses one weight. The numeric check below
  finds breaks at about `1/(8L)` when every weight on the count path moves.

## The statements (exact text in `Lane4/Collision.lean`)

Architecture `Lane4.Seq.TNet` (rung 2), exact rationals. Relative ball `netRel τ N N'`:
every weight `a` becomes some `b` with `|b − a| ≤ τ·|a|`; written zeros stay zero.

A task `T` is: tokens `1..V`, a set of counted tokens `inS`, a wanted parity `par`.
`T.Correct N w`: `0 < N.out w w.length ↔ (count of counted tokens in w) % 2 = par`.
`T.OnBall N τ L`: every `N'` with `netRel τ N N'` is correct on every valid `w` of length
at most `L`. These are the rung-2 parity specs.

**The class.** `T.CountChannel N`:

    ∃ D : ℕ → ℚ → ℚ, ∀ d : ℚ, |d| ≤ 1 → ∃ N' : TNet, netRel |d| N N' ∧
      ∀ w, T.Valid w → N'.out w w.length = D (w.length + 1) ((1 + d) * k(w) / (w.length + 1))

One decoder `D` for every input and every `d`; along a one-parameter family inside the
ball the output at the last position depends on the input only through the number of
positions and the scaled average. This is a semantic class (a property of the function
family), not a syntactic one: membership is a theorem per network.

**Statement 1, `CollisionBound`.** For every task with a counted and an uncounted valid
token, every `N` with `T.CountChannel N`, every `0 ≤ τ ≤ 1` and `L ≥ 2`:

    T.OnBall N τ L  →  τ * (2 L − 1) < 1.

`CollisionBound'` is the same with the witness exposed: if `1 ≤ τ(2L − 1)` and `τ ≤ 1`
there is `N'` in the ball and a valid `w` of length at most `L` on which `N'` is wrong.

The intended proof (not yet attempted): inputs of length `L` with `L − 1` and `L` counted
tokens; `d₂ = −τ`, `d₁ = (1 − τL)/(L − 1)`; then `|d₁| ≤ τ` exactly when `τ(2L − 1) ≥ 1`,
and `(1 + d₁)(L − 1) = (1 + d₂)L`, so the two networks give the same output on inputs of
opposite parity.

**The constant.** `τ < 1/(2L − 1)`, i.e. `τ·L < 1/2 + τ/2`. It does not depend on the
network: within the class the constant is universal. The dependence on the network is
all in whether it is a member.

**Statements 2 to 4, membership.** `Lane4.Member.p05.Membership`, `.p10.`, `.p29.`:
`task.CountChannel net` with `net` the exact text of the network proved at rung 2 and
`task` its rung-2 spec (p05: tokens 1..4, counted {1,3,4}, even; p10: tokens 1..3,
counted {1,2}, even; p29: tokens 1..4, counted {2,3}, odd).

**Corollaries the study team derives** (from Statement 1 and a membership, in `Final.lean`):
`Radius`: for that network, `T.OnBall net τ L → τ(2L − 1) < 1`; and `NoBall`: for every
`τ > 0` there is an `L` with `¬ T.OnBall net τ L`.

**Are the three networks members? Expected yes, to be proved.** All three have the same
plan: block 1 is one head with a zero score matrix (uniform attention; relative
perturbation keeps it zero) whose single value weight writes the average of the counted
flag into slot 1; block 2 is one head whose score is `a·z·j − b·j²/n` (so it reads slot 1
and position features only) and whose value reads `(−1)^j`; the read-out reads that slot.
Scaling the block-1 value weight by `(1 + d)` gives `z = (1 + d)k/n` and nothing else in
the network sees the tokens. The second block does see the sequence (slot 0 holds each
token's flag), but its written weights on that slot are zero and stay zero in the relative
ball. If a membership proof shows this reading is wrong for a network, that network is
reported as not a member, with the reason.

## Sanity check before proving (done; `scratch/r6_collision_sanity.py`, exact rationals)

Results in `results/r6-collision-sanity.json`, log `logs/r6-collision-sanity.log`.

- A closed form for the output as a function of `(n, z)` agrees with the exact evaluator
  `tools/seqnet.py` on 25 (count, d) pairs at length 30 for each of the three networks,
  and on the collision pair at length 100.
- The collision pair of the intended proof gives equal outputs for all three networks at
  `L` = 20, 100 and 1,000, and one of the two answers is wrong each time.
- Smallest radius with a break when only the block-1 value weight moves: `0.5000/L` at
  all three lengths, for all three networks. The statement's radius is `1/(2L − 1)`
  (`0.513/L`, `0.5025/L`, `0.50025/L`): just above the true single-weight threshold, as
  a necessary-radius statement must be, and within 2.6% of it at `L = 20`.
- Smallest radius with a break when every nonzero weight on the count path moves
  (embedding entry, value weight, the two score weights): `0.126/L`, `0.1253/L`,
  `0.1250/L`. So the full ball fails about four times earlier than the statement says.
- Against the 2x2 version 2 (relative 1/200; `writeup/NOTE_2x2_v2.md`): the screen found
  no break for the three parity networks at lengths up to 20 and breaks at lengths 100
  and 1,000. The statement is silent at lengths up to 20 (its radius there is `1/39` or
  larger) and at length 100 (`1/199 > 1/200`, by a hair), and asserts a break at length
  1,000 (`1/1999 < 1/200`). The count-path closed form puts the break at `1/200` between
  lengths 20 (needs `1/158`) and 100 (needs `1/798`). No contradiction in any cell.
- One detail the check exposed: at `L = 100` with only the value weight moved, radius
  exactly `1/200` breaks p05 and p10 (a tie, output 0, wanted positive) but not p29
  (output 0, wanted non-positive). The statement does not depend on this.

## Novelty (search of 2026-11-14; scope: arXiv listings and web search, pages opened)

We did not find this statement, or any machine-checked necessary weight-ball radius for
a transformer on a counting task. Closest work, each opened on its own page:
- Hahn and Rofin, "Why are Sensitive Functions Hard for Transformers?" (arXiv:2402.09963):
  Theorem 6 lower-bounds an AVERAGE directional sharpness for soft-attention transformers
  with layer norm computing high-sensitivity functions, in the limit of small radius and
  long inputs. General and much deeper than this rung; average case, a limit statement,
  no explicit radius, not in a proof assistant. It also recalls that Chiang and Cholak's
  parity construction is fragile in one parameter. **Our statement is a special,
  worst-case, explicit-constant instance for hard attention and a restricted class; it
  should be presented as consistent with their result, not as a new phenomenon.**
- Chiang and Cholak, "Overcoming a Theoretical Limitation of Self-Attention"
  (arXiv:2202.12172): the two-layer parity construction with a length-dependent position
  encoding that the rung-2 networks resemble; no perturbation theorem in the abstract.
- Kozachinskiy, Steifer, Wałęga, "Parity, Sensitivity, and Transformers"
  (arXiv:2602.05896) and Hsu, "Lower bounds for one-layer transformers that compute
  parity" (arXiv:2605.12171): expressivity lower bounds (depth, heads), not perturbation.
- "A completely uniform transformer for parity" (arXiv:2501.02535): a construction
  without length-dependent encodings.
- Viswanathan et al., "Formally Verified Autoresearch for Analyzing the Expressivity of
  Multi-Head Attention" (NeurIPS 2026 workshop page 157626): Lean-checked head-complexity
  results for one-layer attention; no weight perturbation.
- Wesonga, "Formalizing PARITY Circuit Lower Bounds in Lean" (arXiv:2609.24188): Håstad's
  circuit bound in Lean 4; no transformers.
Not searched: full texts beyond abstracts except Hahn and Rofin; GitHub code search by
hand. "We did not find" is the claim, with this scope.

## Plan, agents, budget

1. Kit case `runs/r6b/kColl`: prove `CollisionBound` and `CollisionBound'` (import
   `Seq`, spec = the text of `Lane4/Collision.lean`). One Sonnet doctor.
2. Membership cases `runs/r6b/m05`, `m10`, `m29`: prove `task.CountChannel net`. The
   doctor is given the rung-2 proof of the same network as its worked example. One Sonnet
   doctor at a time.
3. The study team's `Final.lean` derives `Radius` and `NoBall` and prints axioms.
Doctors: Sonnet, fresh agent per case, 12 submissions, 600 s and 4.5 GB per check, the
rung-5 doctor prompt, `native_decide` banned and counted. At most 2 Sonnet attempts
(fresh agents) per statement. A statement that stalls two attempts is reported to the
coordinator, who may clear one Fable step with the coordinator (a lab rule); the study team
does not start it. Estimated cost: 4 to 8 Sonnet cases, 150k to 300k tokens each.
Usage: no new case at or above 60% weekly (70% if the coordinator agrees; until then
60%); checked and logged before each case.
`tools/check.py` gets one new module entry (`Collision`); that changes a file frozen for
rung 6a and is recorded as an amendment there before any 6a doctor runs.

## Bars (set now)

- **Pass:** Statement 1 and at least one membership kernel-checked, with the corollaries.
  Headline wording if passed: "for N of the 3 proved rung-2 parity networks, kernel-checked:
  no relative weight ball of radius 1/(2L − 1) or more is correct up to length L; the
  bound holds for every network with a count channel; it is a restricted class, one
  weight is moved, hard attention, exact arithmetic."
- **Kill (the coordinator's rule):** if no membership can be proved without changing the
  class into one that makes the bound trivial (for example a class that assumes the
  collision), stop and report that as the finding. Also a kill: Statement 1 false as
  written (a counterexample found); then the statement is corrected in a dated amendment
  before any further attempt, and the correction is reported.
- Partial: Statement 1 proved and no membership: reported as "a bound for a class with
  no proved member", which is worth much less, in those words.

## What would make the result weak, written down now

- The class is defined by the property the proof needs (a one-parameter family through
  which the output factors). It is not empty only if memberships are proved.
- The argument is elementary and the phenomenon is known in general form (Hahn and
  Rofin; Chiang and Cholak's remark).
- One weight; relative ball; hard attention; exact rationals; parity only.
- The three networks share one construction, so three memberships are closer to one
  result than to three.
- The constant is four times looser than the measured full-ball threshold.

## Stretch, stated and not promised

The same statement for the Dyck-depth and sort-rank networks of rung 2 (needs a different
decoder separation property than parity); a class in which the second block may read the
sequence (the collision argument does not cover it, as the review says); Lean witnesses
at a stated length for the full-ball `1/(8L)` threshold.

## Frozen files

sha256 list in `scratch/freeze_r6b.sha256` (Collision.lean, R6Statements.lean, the sanity
script and its results, the three rung-2 Solution files, Seq.lean, Basic.lean); its own
sha256 is recorded in the commit message and in the lab log.

## Amendment 1 (2026-11-14 evening EST): Statement 1 was false as written

The first proof attempt (Sonnet, case `runs/r6b/kColl`, 4 submissions) reported that
`CollisionBound` and `CollisionBound'` are false as registered: `Task.par` is any natural
number, and with `par = 2` the condition `count % 2 = par` never holds, so a network
with constant output −1 is "correct" on every ball and has a count channel (constant
decoder). The counterexample was argued by hand by the agent and agrees with where its
Lean proof stopped (everything compiled except the final parity step). This is the
pre-stated case "Statement 1 false as written": a lane fault in the statement, not a
fault in the idea. Correction: both statements gain the hypothesis `T.par < 2`. Nothing
else changes; the three membership tasks have `par` 0, 0 and 1. The corrected file is
`Lane4/Collision.lean`; the proof case is rebuilt as `runs/r6b/kColl2` (fresh agent, given
the first attempt's compiled partial file); the membership cases were rebuilt before any
agent saw them. The first attempt does not count toward the two-attempt limit, because
the statement it was given was false.

## Correction (2026-11-14, 5:15 pm EST): times

"Evening" in the status line and in amendment 1 is wrong: the registration commit
(565e994) is stamped 3:52 pm EST and the amendment commit (5ed45c6) later the same
afternoon. Nothing else changes.
