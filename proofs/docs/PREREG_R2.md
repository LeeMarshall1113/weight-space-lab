# Pre-registration: rung 2 (all sequence lengths)

Written 2026-11-11, late evening, after rung 1 closed (commit 6cd7ebd) and after the
the project owner's go was relayed. Written before any rung-2 doctor run and before any rung-2
twin is trained. It extends PREREG.md, which stays unchanged. Later changes go in a dated
"Amendments" list at the end of this file.

Read first: NOVELTY.md, "Re-check for rung 2". The nearest prior work is arXiv 2602.16473
(C-RASP programs verified with SMT model checkers). This rung does not claim a first.

## Question

Can a doctor write the weights of a fixed-size hard-attention transformer **and** a Lean 4
proof, accepted by the kernel, that the network is correct on input sequences of **every
length**?

## Fixed framework

`Lane4/Seq.lean`, written by the study team. In short:

- Weights are exact rationals. All arithmetic is over ℚ. Inputs are token lists, so no
  real numbers are involved.
- The framework prepends a BOS token (token 0). The state at a position starts as the
  token's embedding row plus eight fixed position features:
  `1, i, i², 1/(i+1), (-1)^i, n, 1/n, i/n` (i = position, n = number of positions).
- Attention is **average-hard**: a bilinear score, and the positions with the maximal
  score among the mask's candidates share the weight equally. Masks: all, causal (j ≤ i),
  strict (j < i). This is not softmax attention and is not the standard architecture.
- A block is heads plus a one-hidden-layer ReLU MLP, both residual. Limits: at most 4
  blocks, 4 heads per block, state width 24, MLP width 32.
- A lemma kit about the selected set and averages is part of the framework.
- Why these choices: unique-hard attention provably cannot compute parity at every
  length (Hahn 2020), so ties must share weight, and the position features are the ones
  the known constructions for the four families need. The study team has checked by hand that
  each family below is expressible in this architecture. That is a design-time fact about
  the architecture, not a result.

## Task families and statements

Tokens are 1..V. Four families, each with random parameters:

| Family | Parameters | Statement, for every non-empty token list w with tokens in 1..V |
|---|---|---|
| parity | V in 2..4, a non-empty proper subset S of the tokens, a target bit | `0 < out w (last position)` exactly when (number of tokens in S) mod 2 = target |
| dyck | V in 2..4, a weight in {+1, −1, 0} per token (at least one +1 and one −1) | `0 < out w (last position)` exactly when every prefix sum is ≥ 0 and the total is 0 |
| sort | V in 2..4 | at every position i in 1..length: `out w i` equals the i-th smallest token of w (stated through counts) |
| add | base b in 2..3; a token is a digit pair, least significant first | at every position i: `out w i` equals (a_i + c_i + carry into i) mod b, with the schoolbook carry |

Classification families use the sign of the output at the last position. Sequence
families require exact equality at every position. No statement has a length bound.

## Pool, draw, blindness

- `tools/seqpool.py pool`, seed 20261113: every distinct parameter setting of the four
  families, capped at 30 per family by a seeded shuffle.
- `tools/seqpool.py draw`, seed 4043: per family, a seeded shuffle. **Dev** = 1 case from
  each of two families chosen by the seed. **Test** = 10 cases: 3 parity, 3 dyck, 2 sort,
  2 add. The next 2 per family are reserve, used only for faults in the study team's generator.
- Blindness is weaker than at rung 1 and is reported as such: the four families are
  famous and their constructions are in the literature. Only the parameters are drawn
  blind. The study team's worked example is on a task outside the four families (does the input
  contain a given token).

## Arms (the same 10 test cases in each)

| Arm | Doctor writes | Theorem |
|---|---|---|
| **net** (primary) | `net : TNet` and `net_correct` | the family statement, for all w |
| **prog** (plain-code control) | `prog`: a single left-to-right pass, `List.foldl` with an explicit step function (two passes allowed for sort); no library counting, summing or sorting and no call to the spec; and `prog_correct` | the same statement with `prog` in place of the network output |
| **twin** (trained, no doctor) | nothing | see below |

Twin protocol: train a soft-attention transformer of the net-arm solution's shape (or 2
blocks, 2 heads, widths 16 and 32 if the net arm failed) on random inputs of length 1-10,
seeds 0, 1, 2. Then replace softmax by average-hard attention, round weights to multiples
of 1/1024, and evaluate exactly on 200 random inputs in each length band: 1-10, 11-20,
21-40, and exactly 100. Reported: exact accuracy per band. One wrong output at any length
refutes the all-lengths statement for that twin. No proof is attempted on twins. A twin
"generalises" if it is 100% correct in every band; the number of such twins is reported.
Training details are fixed in `tools/train_seq_twin.py` before any twin is trained, and
its hash is recorded here by amendment.

## Doctor protocol

As rung 1: one episode per case and arm, 12 submissions, 600 s and 4.5 GB per check, no
web, no nested agents, no Lean outside the submit command, the same banned tokens
(`native_decide` banned and counted; kernel evaluation by `decide` is allowed). Doctors
get TASK.md, Spec.lean, Final.lean, copies of Basic.lean and Seq.lean, and one worked
example. New at rung 2:

- **Models.** Sonnet first on every case. A net-arm case that Sonnet fails gets one Fable
  episode (one Fable agent at a time machine-wide, cleared with the scheduler
  session, reason in the run log (not released)). The table reports the Sonnet-only count and the
  Sonnet-plus-Fable count separately. The prog arm is Sonnet only.
- Each doctor gets a scratch folder inside its own case folder and is told to keep every
  helper file there (rung 1 doctors overwrote each other's files in a shared folder).
- The child-memory log matches the case folder path, so scratch scripts are measured.
- A doctor that reports while a submission is still pending is told once, in fixed
  words, that the queue is working and the episode is not over.

## Measures and bars

- Primary: **S2 = number of the 10 test cases with a kernel-checked all-lengths net
  proof** (Sonnet or Fable). The Sonnet-only count is reported next to it.
- **Kill: S2 < 5 → report rung 1 only**, with rung 2 as a negative result.
- Pass: S2 ≥ 7. 5-6 is "partial".
- Plain-code control: if the prog count ≥ S2 and the median submissions in prog ≤ net,
  the reading is again "the network adds nothing over a verified program", stated in the
  headline.
- Twin contrast: claimed only if at least 7 of the 10 seed-0 twins are wrong at some
  length beyond training **and** S2 ≥ 7. Otherwise "no contrast shown".
- Per case: submissions, Lean seconds, proof lines, blocks, heads, state width,
  `native_decide` attempts, other banned-token rejections, memory kills, timeouts.
- Float gap: stated, and measured by a float32 forward pass on 1,000 random inputs of
  length up to 100 per passing net (outputs that differ from the exact output are
  counted). Position features grow with length, so float error is expected to grow.
  Nothing about floats is proved.

## Not claimed

Not a first. Not softmax attention. Not natural language. Not that trained transformers
cannot be proved correct (no proof is attempted on twins). Not blind in the rung-1 sense.

## Compute

One lean.exe at a time under a 3 GB memory reservation (service). Doctors under a 1 GB memory reservation per two
doctors, with slots agreed with lanes 2 and 5 (3 lab-wide). The service memory reservation and the
doctor memory reservation are requested as a pair, and the service idle limit is 60 minutes. Twin
training is numpy on CPU, under its own memory reservation if it needs more than 4 GB or 15 minutes.

## Amendments

1. **2026-11-11, before any doctor run, test ids unread.** The pool has only 3 sort
   settings and 2 add settings (V in 2..4; base 2..3), so those two families are not blind
   draws: the test set uses 2 of the 3 sort settings and both add settings, and they have
   no reserve. The first draw picked dev families by seed and landed on sort, which would
   have left one dev case. Changed before use: **dev = one parity case and one dyck
   case** (the two families with spare settings). Pool sha256
   `09ecec3c09b39f64f1f845183a619fd1d1a71e2cee66fee4850cb036c46cadaf`; the test-id hash is
   in the run log (not released).
2. Expressibility was checked by test, not only by hand: the study team built one reference
   network per family in `private/expr_check.py` and compared it exactly with the spec on
   random inputs up to length 60 (parity, add) or 25 (dyck, sort). These reference
   networks are lane-private and are never placed in a case folder.
3. **2026-11-11, before any twin is trained.** Twin trainer fixed:
   `tools/train_seq_twin.py`, sha256
   `f98a8e0562eb47d21ff70ccfee3c214dc48b7869c4da94a10106267704b7bdd2`. numpy, softmax
   attention, Adam 20,000 steps, batch 64, one length per batch drawn from 1-10, lr 3e-3
   with cosine decay, gradient norm clipped at 1. Loss: logistic on the last position
   (classification), squared error per position (sequence). Dyck inputs are half random
   and half drawn from a constrained walk that ends accepted, in training and in testing,
   because random strings are almost never accepted. Its gradients were checked against
   finite differences (relative error 2e-6).
   Changes from the text above, made because exact rational evaluation of a dense trained
   network at length 100 is too slow: the hardened twin is evaluated in **float64**, not
   exactly (the float64 hard forward pass agrees with the exact evaluator to 4e-16 on a
   test network). A sequence output counts as correct when it **rounds** to the right
   integer at every position, which is more lenient than the exact equality asked of
   doctors. Added: the soft (softmax) network's accuracy per band is reported next to the
   hardened one, so a failure caused by hardening can be told apart from a failure to
   generalise in length. The twin-contrast bar is read on the better of the two (soft or
   hardened) per twin, so hardening cannot manufacture a contrast.
4. **2026-11-12, 1:35 am EST, after the dev pilot, before any test case was built or read.**
   Dev pilot (not a result): net d09 PASS (2 submissions), net p15 PASS (1), prog d09 PASS
   (2), prog p15 PASS (1). No prompt or framework change was made after the pilot.
   Frozen hash (make_seq_cases.py, train_seq_twin.py, check.py, service.py, submit.py,
   doctor_prompt_r2.txt, EXAMPLE_seq_net.lean, EXAMPLE_seq_prog.lean, Basic.lean, Seq.lean,
   concatenated in that order), sha256: `91280d44484f734777e644949e5f5d7064c2d2f000e6b54b1a62a3f78b85ed12`
   Stated now because the pilot made it plain: the parity dev case was solved on the first
   submission in seven minutes with the construction known from the literature. If the
   test set goes the same way, the reading is "Sonnet can recall and formally verify known
   constructions in an architecture built to express them", not "Sonnet discovers
   length-general algorithms".
5. **2026-11-12, 2:15 am EST, after the doctor arms finished and before any twin is
   trained.** The twin's shape is now read from an exact export of the passing network
   (Lean prints the net as JSON; `tools/export_nets.py`), not parsed from the solution
   text with regular expressions, which could not follow doctors' named sub-definitions.
   Only the shape-reading lines of `tools/train_seq_twin.py` changed; training and scoring
   are as in amendment 3. New sha256: `34524715e7976d8b0267a6396467f703f6532809bb30c7a53f3b77972714fb42`
