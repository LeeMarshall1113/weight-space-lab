# Lane 4, rung 4 pre-registration: transformers proved correct at every length, for every nearby weight setting, with a rounded forward pass

Written 2026-11-12/13 before any doctor episode. The framework (`Lane4/RSeq.lean`) and one
worked example were written and compiled by the lane before this file; no doctor has seen
either. Changes after this point go in dated amendments at the bottom.

## Why this rung

Rung 2 proved ten written transformers correct at every length, in exact arithmetic, for
the written weights only. Rung 3 then measured that all ten break when a single weight
moves by 1/1000 (eight at 1e-6), and that the proved sort network fails in float32 from
length 300. So those theorems are about one point in weight space and about arithmetic no
computer runs. Rung 4 asks whether an LLM doctor can write transformers, and proofs, that
do not have either weakness.

## The claim under test, and what is NOT claimed

Novelty (NOVELTY.md, rung-4 section): a narrow first survives a web search over abstracts.
It is "the first proof-assistant-checked proofs that a transformer is correct at every
input length for every weight setting in a stated ball, and for a modelled rounded forward
pass up to a stated length". Not claimed:

- That fragility of exact constructions is new. It is known in theory (Hahn 2020; Chiang
  and Cholak 2022; Merrill and Sabharwal 2023).
- Anything about trained networks, soft attention, or networks of practical size.
- Anything about real IEEE arithmetic beyond the stated model (see "The float model").

## The statement (one theorem per case)

    ∀ u fl, Rounding u fl → 0 ≤ u → u ≤ 2^-24 →
    ∀ p : Pert, p.Within (1/200) →
    ∀ w (tokens in 1..V), u * (length w + 1) ≤ 1/256 →
    ∀ i in 1..length w,  |net.out fl p w i − target w i| ≤ 1/4

Read at its two ends:

- **u = 0, fl = identity:** exact arithmetic, **every input length**, every weight setting
  in the ball.
- **u = 2^-24:** a rounded forward pass, every weight setting in the ball, every input with
  at most **65,535 positions**.

One theorem covers both, and everything between. A case counts only if this whole
statement is kernel-checked with the standard axioms. There is no partial credit for the
exact end alone.

### The weight ball

Relative: a written weight `w` is used as `fl (w * (1 + d))` with `|d| ≤ τ = 1/200`, one
independent `d` per weight, embeddings, attention, MLP and read-out all included. A weight
written as 0 stays 0.

Why relative and not the absolute ball of rung 3: with position features that grow with
length, an absolute perturbation of a zero entry lets every unit read τ·n, so no task has
an absolute ball that does not shrink with length. This is a weaker ball than rung 3's
and the results must say so. It is the right model for rounding of stored weights and for
multiplicative noise; it does not cover pruning errors or additive noise.

τ = 1/200 was chosen by the lane from a hand calculation on its own construction for the
carry family (error about 0.11 against the 1/4 tolerance; at 1/100 about 0.22). It is one
value for all cases. It was not tuned on doctor results.

### The float model

`Rounding u fl`: relative error at most u (`|fl x − x| ≤ u·|x|`), monotone, idempotent,
odd, exact on integers up to 2^24. Every multiplication, addition and division in the
forward pass is rounded, sums run left to right, stored weights and position features are
rounded too. IEEE binary32 round-to-nearest satisfies this with u = 2^-24 **as long as no
operation overflows or underflows**. Overflow, underflow, subnormals, fused multiply-add,
reordered or vectorised sums, and softmax are **not** modelled. Attention is hard
(arg-max with ties averaged), not softmax. So the theorem is about the model, and its
link to a real float32 run is the lane check below, not a proof.

### Output tolerance

1/4 around an integer target (targets are 0..3), so rounding the output to the nearest
integer gives the target.

## Which tasks (and which are left out, plainly)

Analysis in NOVELTY.md: a ball that does not shrink with length is possible for tasks
solved by unique hard attention with exact-zero penalties, and not for tasks that must
count. So:

- **In:** four families, pool in `tools/r4pool.py`. `carry` (a generalised addition carry
  chain, modulus 2 or 3), `last` (value of the last marked token), `first` (bit of the
  first marked token, combined with the current token mod 2), `induct` (token after the
  most recent earlier occurrence of the current token, through a table; needs two
  layers and one head per token).
- **Out: parity, dyck, sort** (three of rung 2's four families). They need a ball that
  shrinks like 1/n, and the reduced position features of this framework may not express
  them at all. **No doctor arm is run for them.** The results must state that rung 4
  covers only the non-counting kind of task, and that for counting tasks the best
  possible statement is "every length up to c/τ", which nobody has proved here.

**Feasibility, checked numerically by the lane before this file (nothing proved):** hand
constructions for the two hardest families, carry and induct, on 12 pool settings
(c34-c39, i24-i29, `scratch/r4_feas.py`). Exact at zero perturbation; worst deviation
found under random sign-corner perturbations at τ: 0.03 to 0.10 (tolerance 0.25); the
tolerance is first broken at 4τ to 16τ. So the statement is reachable and the ball is
within about one order of magnitude of the limit for these constructions. Those 12
settings are excluded from the draw.

Pool seed 20261114, at most 40 settings per family (150 settings; sha256 of the pool
1448b52fe161dcf3d702b21a583451977579c782f91184676adabbe9ea3b4dad). Draw seed 4045: per family 1 dev,
3 test, 2 reserve. So **4 dev cases, 12 test cases**. Test settings are not read by the
lane before the freeze. A reserve case is used only if a test case is unusable through a
lane fault (logged), never because a doctor failed.

## Arms

1. **net** (the claim): weights + proof of the statement above. 12 test episodes.
2. **prog** (plain-code control): a one-pass `List.foldl` program with a proof that it
   equals the target at every length, same 12 specs. The program may use the spec's token
   tables but not its fold or search. This control is expected to be easy and it proves a
   different, exact statement; it is here to keep the comparison of rungs 1-3 and to show
   what the proof effort for the same task is without a network.

No trained-twin arm: no trainer here produces unique hard attention, and a twin under
this statement would be a different project.

Doctors: Sonnet, fresh agent per case, 12 submissions, 600 s and 4.5 GB per check, at
most 2 at once (lab cap 3). No nested agents. `native_decide` is banned by the checker and
every attempt is counted. One prompt for all cases (`prompts/doctor_prompt_r3.txt`
reused unchanged).

**What doctors are given.** `RSeq.lean` with a lemma kit (rounding bounds, relative-error
products, rounded positions, unique selection), one worked example on a task outside the
four families ("output the previous token", one head, no MLP), and three sentences of
advice in the task file: zeros stay exactly zero, equal written weights are not equal
once stored, margins must beat a perturbation that multiplies position features. The
exact-zero penalty score itself is not shown; the example's score is position-only. This
help is part of the result and must be reported with it.

## Fable

Sonnet first on every case. If the net arm ends below the pass bar, the lane may run
**one Fable doctor at a time** on test cases Sonnet failed, in family order, after
clearing each use with the compute scheduler and logging the reason. Fable results are
reported in a separate column and never added to the Sonnet count without saying so.

## Bars (set now)

S4 = number of the 12 test specs whose net-arm statement is kernel-checked by a Sonnet
doctor.

- **Kill: S4 ≤ 2.** Report "Sonnet cannot do this with this kit", run the Fable step
  above if cleared, stop.
- **Pass: S4 ≥ 6, with at least 2 families fully or partly solved.**
- **Headline wording if passed:** "N of 12 written transformers kernel-checked correct at
  every length for every weight setting within 0.5% (relative), and under a modelled
  rounded forward pass up to 65,535 positions; non-counting tasks only."
- Family counts are reported separately; a family with 0 of 3 is named.

Dev pilot (4 cases, net arm): used only to find faults in the kit, example, prompt and
tools. If the pilot shows the task file or kit is broken or misleading it may be fixed;
then everything is frozen by hash before the test draw is opened. Pilot results are not
results.

## Checks the lane runs on every proved network (no doctor)

`tools/r4_checks.py`, numpy, under a memory reservation. Networks exported from the kernel-checked
file.

1. **Inside the ball, exact (float64) arithmetic:** random and sign-corner relative
   perturbations at τ (60 of each), inputs at lengths 6 to 2,000 in four patterns
   (uniform random, one token dominating, random head with a constant tail, constant
   with one change). These patterns produce long propagate runs and inputs with no or
   one marked token, but they are not a per-family adversarial search. Expect no output further than 1/4 from the target. Any violation is a contradiction
   with a kernel-checked theorem and stops the rung.
2. **Non-vacuity:** the same search at 2τ, 4τ, ... up to 64τ and lengths up to 20,000.
   Report the smallest multiple at which some output leaves the tolerance. If no
   multiple up to 64 breaks a network, say so: its ball was far from tight.
3. **Real float32:** a numpy float32 forward pass that follows the framework's operation
   order, written weights and 5 sign-corner perturbations at τ rounded to float32, at
   1,000, 16,000 and 65,534 tokens (at most 1,000 query positions per input at the two
   larger sizes). Report the worst deviation. Beyond the theorem, one-block networks
   only (two-block ones cost too much memory here): 200,000 and 2,000,000 tokens, written
   weights; report whether it still holds. Lengths past 2^24, where float32 stops
   representing every position, are not tested. A failure inside the theorem's range would mean the float model
   misses something real; it must be reported, not explained away.
4. **Rung-2 comparison (carry family only, base-2 addition is a special case):** quote
   rung 3's measured break point of the rung-2 addition networks (single weight, 1e-4)
   next to the proved radius here. Different architecture and ball type; say so.

## What would make the result weak, written down now

- A relative ball is weaker than rung 3's absolute ball.
- The tasks are easier than rung 2's (no counting) and the lane picked the families
  knowing which mechanism works.
- The kit and the example carry part of the proof.
- 12 cases, one model, one τ, one tolerance.
- The float statement is about a model with stated gaps.
- If the prog control is again trivially easy, the transformer adds nothing practical
  over a verified program; the result is about what can be proved of weights, not about
  usefulness.

## Logging and stopping

Every run goes in `run log (not released)`, dead ends included. Results are saved per case as it
finishes (`results/rung4-*.json`). All Lean and all doctor batches run under scheduler
memory reservations with repo-specific match patterns. Stop for a go after the final table, or as soon
as the kill bar is certain.

## Amendment 1, 2026-11-13 about 2:10 am EST: dev pilot done, freeze

- Smoke (`tools/smoke4.sh`, `logs/smoke4-01.log`): both examples pass; a wrong weight,
  a `native_decide` and a banned `take` are rejected; the four dev specs compile and
  match the python reference targets on 15 inputs each.
- Dev pilot, net arm, Sonnet, 4 cases (c16, l12, f04, i04): 4 of 4 kernel-checked, at
  submissions 2, 2, 2, 1; solution files 345 to 829 lines. These are not results.
  All four doctors found an exact-zero penalty score on their own.
- The pilot showed no fault in kit, example, prompt, task file or checker, so nothing
  was changed after it. The check wording in "Checks the lane runs" had been aligned
  with `tools/r4_checks.py` before the prereg commit.
- A warning the pilot gives: 4 of 4 at two submissions suggests the test arm may be
  near its ceiling, in which case the result says the kit plus Sonnet makes these
  tasks routine, and the pass bar was set low. The bars are not changed.
- Frozen files (sha256 list in `scratch/freeze_r4.sha256`; sha256 of that list
  0d71ccfa127bbe0791eee017557c20f68beb9bf7347ed62622ca9c248877a2b1): Lane4/Basic.lean,
  Seq.lean, RSeq.lean, both rung-4 examples, the doctor prompt, make_r4_cases.py,
  check.py, service.py, submit.py, r4pool.py, r4_checks.py, r4net.py.
- Test-set sha256 (ids): bee0427d138132b68a071767e04617772b750ef59dda4e04d3a803ac8986c646.
  Test cases are built after this commit.
