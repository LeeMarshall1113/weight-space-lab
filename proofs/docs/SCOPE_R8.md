# Rung 8 scope: from the rung-7 result toward a standard-architecture theorem

Written 2026-11-20 (Friday morning EST). **Scope only: nothing here has been trained, prototyped
or proved, and nothing starts without the project owner's go.** Every odds figure is my judgement.
Where a claim about what the rung-7 networks do rests on a measurement, the file is named; where it
is my reading and not a measurement, it says so.

## Where rung 7 leaves us (from `RESULTS_R7.md`)

A soundness theorem for a certificate checker, and per-network theorems with no per-network proof
work, for a one-block GATED transformer on one carry task. Held-out acceptance: 4 of 9 screened
networks (4 of 20 trained seeds). Statement A, the ungated architecture (every earlier position is
a candidate key; digit sum of the last two tokens mod 5): 0 of 18.

Why A fails, from the 18 kernel rejections (`results/rung7-kernel.json`): 16 networks because the
content score varies across keys by 11 to 27 while the checker allows 10.78 (slope 24 minus the
fixed gap 12 minus rounding); 2 because the output interval is wider than 1/4. Two different
things hide in the first group, and I have not separated them by measurement:

- spread 11.0 to 17.4 (12 of the 16): the latest position still wins the softmax, by a score
  margin of 24 minus the spread, so by about 7 to 13 instead of the 12 the proof constant
  demands. The attention is still nearly hard; only the lemma is too coarse.
- spread 23.8 (1 network): the margin is under 1; two keys nearly tie and the head output is a
  mixture.
- spread above 24 (3 networks: 24.5, 25.6, 27.0): a key two positions back can outscore the
  previous token for some token pairs. The head is then not "latest position wins" at all; which
  key wins depends on the last few tokens.

These spreads are the worst pair the checker met first in each network (it stops at the first
failure), so each is a lower bound on that network's worst spread, not the worst itself.

## Prior work (searched again on 2026-11-20; nothing below is carried over from Thursday unchecked)

- **teal-sea/lean-checked-network** (GitHub): Lean 4, standard axioms. **Read from the repository
  on 2026-11-20** (by a Sonnet reader through the GitHub API, Lean source quoted; I did not read
  the files myself). It is the closest neighbour, and closer in method than I had assumed:
  - *The all-lengths adder* (`rnn/lean/RnnAdder/Network.lean`, `Trained.lean`, `Trained16.lean`):
    a TRAINED recurrent network with 4 (and 16) binary threshold units, weights rounded to
    integers, that adds two binary numbers bit by bit. Theorems, `Trained.lean` lines 42 to 54:
    `theorem sums_correct (xs : List Input) : run net net.h0 xs = addBits false xs` and
    `theorem adds (xs : List Input) : bitsToNat (run net net.h0 xs) + 2 ^ xs.length * (if finalCarry net net.h0 xs then 1 else 0) = bitsToNat (xs.map Prod.fst) + bitsToNat (xs.map Prod.snd)`.
    Proof: a finite certificate over the 5 reachable states times 4 inputs (`transOk`, by
    `decide +kernel`), then induction on the list. Exact integer arithmetic, threshold
    activations; no floating point, no rounding model, no perturbation ball; no attention.
  - *The transformer* (`transformer/mathlib/TransformerBridge/FinalRaw.lean` lines 69 to 79,
    `raw_model_adds_mod_113`): one layer, 4 heads, d_model 128, no LayerNorm; fixed 3-token input
    `[a, b, =]`, all 12,769 pairs by exhaustive kernel evaluation; integer-quantised weights with
    an exact real softmax, "not the float checkpoint" (their README).
  - A draft PR (#24) proves a trained byte-level lexer network equal to a reference lexer on
    every byte list, again exact integers.
  - No theorem there covers softmax attention at unbounded length, a rounding model, or a
    soundness theorem for a checker over a class of networks.
  **Consequence for our wording.** "Finite certificate over reachable abstract states, then
  induction over the input" is their idea as much as ours, and they had an all-length theorem for
  a trained network first. What rung 7 adds is the object (softmax attention, real-valued with a
  floating-point rounding model and a weight ball) and the form (one soundness theorem for a
  checker, then no proof work per network). Any write-up must cite them for the pattern.
- **Gross et al., arXiv 2406.11779** (NeurIPS 2024): accuracy lower bounds for small trained
  transformers on Max-of-K at a fixed sequence length, 151 seeds, proofs as verified computations,
  with the finding that shorter proofs need more mechanistic understanding. Not all-length, not a
  per-input correctness statement in a proof assistant kernel as far as the abstract says. An
  ICLR 2025 follow-up treats group composition (S5) in the same style.
- **TorchLean, arXiv 2602.22631** (ICML 2026): a Lean 4 framework with one semantics for running
  and verifying networks; IBP and CROWN/LiRPA bounds with certificate checking; demonstrations are
  certified robustness, PINN residual bounds, Lyapunov controllers. Fixed input shape. The
  snippets show no softmax-attention certificate and no statement over all input lengths.
- **Somani, arXiv 2605.24033** (May 2026), "Towards Verifiable Transformers": redesigns the
  architecture (sparsemax attention, L1 norm, LeakyReLU) so circuits are SMT-checkable over
  bounded finite domains. A different trade: change the model so a solver can handle it.
- **Vertex-Softmax, arXiv 2605.10974v1** (Rezazadeh and Gholami Davoodi, 8 May 2026). **Read on
  2026-11-20** (by a fetch agent from the arXiv HTML; the first 40% verbatim, the rest as a
  summary, appendix D not read). For fixed values c and scores s in a box, F_c(s) = c · softmax(s)
  attains its minimum at a vertex of the box (Theorem 3.1), and after sorting c the minimiser
  puts upper endpoints on the m smallest c_j and lower endpoints on the rest for some m in 0..K
  (Theorem 3.2), so K + 1 candidates suffice. Proof: with one coordinate free the expression is a
  Möbius function of e^{s_i}, monotone, so each coordinate moves to an endpoint; the paper credits
  the vertex property to Dinkelbach (1967) and claims the threshold reduction. Values are exact
  in the theorem; value uncertainty is handled by substituting a lower bound. Paper proofs in real
  arithmetic, fixed K (experiments to 128 keys), no proof assistant, and the authors say their
  floating-point implementation is "not by itself a proof-carrying floating-point certificate".
  **Use for rung 8:** the prototype (`tools/r8_proto.py`) does not need the theorem: with two or
  three window keys it bounds each attention weight separately from the score ratios and carries
  the weights as symbols, which is cruder per coordinate but keeps the correlation between
  coordinates. If a Lean lemma for the exact box optimum is wanted later, this is the source.
- **Huang et al., AAAI 2026**, "Parameterized Abstract Interpretation for Transformer
  Verification": tighter linear abstract domains for attention inner products, robustness, fixed
  length. Relevant to the interval-width problem; not formalised.
- **Length-generalisation theory**: Yang et al., arXiv 2603.02238, prove there are no computable
  length-generalisation bounds for two-layer C-RASP and hence for transformers in general. That
  does not conflict with a checker: ours is a sufficient condition that says "yes" or "not
  covered", never "no". It does mean no checker can be complete, which is worth saying in any
  write-up.

In this search I found no kernel-checked, all-length correctness theorem for a transformer with
softmax attention whose weights came from training, other than what rung 7 now has on the gated
variant. The teal-sea all-lengths adder, now read, is an all-length kernel-checked theorem for a
trained network, but a threshold RNN in exact integers. "I found none" is the claim; it is not
"there is none".

## Candidates

### (a) Standard (ungated) attention: a windowed, mixture-aware checker with affine intervals

**Theorem.** The rung-7 headline, word for word, for statement A's architecture: one block, plain
causal softmax attention over all earlier positions with a relative-position score bias, ReLU MLP,
residuals, trained weights; every input length, the whole additive ball, binary32. Still not a
vanilla transformer: fixed relative-position slope, no LayerNorm, no learned position embeddings,
width 8.

**What has to be built.**
1. A softmax lemma with the gap as a parameter (see (b)); most of A's spreads leave margins of
   about 7 to 13.
2. Abstract states that remember a window: the tokens at the last L positions, with L read from
   the certificate so that beyond the window the position bias beats any content score. For
   spreads up to 27 at slope 24, L = 2 or 3; at 5 tokens that is 36 or 216 window states times
   the task state. The checker decides, per window, which key wins or which few keys share the
   attention.
3. Near-ties: when two keys in the window are within the gap, the head output is a mixture. A
   sound bound on a softmax-weighted sum from score intervals (the Vertex-Softmax result, or a
   cruder two-key hull) with a Lean proof.
4. Tighter propagation through the MLP: affine forms (one noise symbol per input coordinate)
   instead of plain intervals, with a proved ReLU relaxation. Two networks fail on width alone
   today and the one I read by hand (seed 110) had 0.54 against 0.25.

**New against prior work.** All-length and trained and ungated softmax attention, in a kernel;
a formalised vertex-type softmax bound. Gross et al. and teal-sea are fixed-length; TorchLean has
the affine machinery for fixed shapes but no attention-over-all-lengths argument.

**Odds.** Soundness proved within a K-b style rule: 50% (items 3 and 4 are each a real proof, not
bookkeeping; rung 7's cases all fell to the first doctor, which makes me less pessimistic than I
was for rung 7, where I said 45% and it passed). Given soundness, at least 2 of 3 fresh screened A
networks accepted: 40% (this is the weak link: I do not know how often trained A networks are
near-tied or how wide affine bounds come out, and I will not know without a prototype). Overall
about 20%.

**Cost.** 8 to 10 kit cases, 2 to 3.5 million Sonnet doctor tokens, one stronger-model step held in
reserve; a prototype in exact rationals first (no doctor tokens). Lean jobs as now.

**Kill rules.** K1: the prototype (frozen before any fresh seed) accepts fewer than 6 of the 18
existing A u3 networks: stop before any Lean, the method does not fit what training produces.
K2: kernel evaluation of the windowed check exceeds 600 s or 4.5 GB in split form. K3: a kit case
fails two Sonnet doctors and the one stronger-model step. Bar: at least 2 of the first 3 screened networks
from fresh seeds (140 upward, never looked at), plus the count on 20 fresh seeds.

### (b) The gap read per network instead of the constant 12

**Theorem.** Same as rung 7 (gated architecture, statement B), with the softmax lemma stated for
any gap g at least some small constant: error at most B times a constant times exp(-(g - 1)),
and the checker choosing the largest g each head's content spread allows.

**What it buys.** All 6 rejected B networks, test and reserve, were rejected on spread (10.7 to
15.9 against 10.78), so their true margins are 8 to 13 where the proof wanted 12. A smaller gap
costs a larger leak term, which then goes through the MLP, so not all six will pass; my guess is
3 or 4 of the 6, lifting held-out acceptance from 4 of 9 to about 6 or 7 of 9. That guess is not a
measurement.

**New against prior work.** Nothing in kind; it sharpens rung 7.

**Odds.** Soundness: 85% (k1 and k3 restated with a parameter; the old proofs are the template).
Lift to at least 6 of 9 on a fresh set: 55%. Overall about 45%.

**Cost.** 3 kit cases, about 0.5 million Sonnet tokens. The constant would again be chosen by a
rule fixed in advance (largest g that passes), not tuned, so a fresh seed set gives a clean count.

**Kill rule.** Prototype on the 15 screened B networks accepts no more than the present 9.

### (c) Scale: more blocks, more width, a second task family

**Theorem.** The rung-7 headline for two blocks, or width 16 to 32, or a second automaton task.

**What has to be built.** For a second task or more width: nothing new in the proof, `Sound`
already covers any automaton and any width up to 24; only training and kernel time. That part is
nearly free and should be run whatever is chosen, as a robustness row. For a second block the
states entering block 2 are intervals, not one of finitely many embedding rows, so gates and
winners of block 2 must be decided per abstract state of block 1; the abstract state space
multiplies and the head lemma needs restating over interval inputs.

**Odds.** Second task and width on the gated architecture: 70% each for at least one accepted
network (cheap). Two blocks: 30%.

**Cost.** Second task and width: no doctor tokens, a few hours of training and Lean. Two blocks:
5 or more kit cases, 2 million tokens or more.

**Kill rule.** Two blocks: prototype accepts no trained two-block network out of 10 screened.

## Which one I would register as primary

**(a), with (b)'s parameterised softmax lemma as its first stage.** I agree with the project owner
that the standard architecture is what moves the level: (b) and the cheap half of (c) make the
rung-7 result sturdier but leave it a result about an architecture we designed; a reader's first
question about rung 7 is "does this work without the gate", and today the answer is 0 of 18.

Reasons for folding (b) in, not running it separately: A cannot work without it (its margins are
mostly 7 to 13, short of the fixed constant once rounding and error radii are added), it is the cheapest piece, it is where a failure would show first, and it lifts B as a
by-product, so if (a) dies at K1 the rung still ends with a better number on B.

Where I would push back, or at least be explicit: (a) at about 20% is a low-odds target, taken on
the project owner's rule that the higher level is preferred even at lower odds. Its first kill rule (K1, the
prototype on the 18 existing A networks) costs no doctor tokens and no Lean, and I would treat
its result as the real decision point: if fewer than 6 of 18 pass a windowed, mixture-aware,
affine prototype, the honest conclusion is that trained ungated networks of this size do not
compute this task in a way this style of certificate can follow, and that is itself worth
writing down. One design question I cannot settle from here: whether "standard" should also mean
dropping the fixed relative-position slope for learned position information. I would not: without
some unbounded position signal no all-length statement is possible for this task, and the slope
is the smallest such signal. That limit should be stated wherever the word "standard" is used.

## Order of work if the go is given

1. Read teal-sea's all-lengths adder and the Vertex-Softmax proof (no tokens beyond reading).
2. Prototype of the (a) checker in exact rationals on the 18 existing A u3 networks and the 15
   screened B networks; freeze; K1 read. No Lean, no doctor.
3. Registration (PREREG_R8.md) with the prototype's numbers disclosed, fresh seeds named.
4. Kit cases, one Sonnet doctor at a time; kernel feasibility test early, as K-a was.
5. Fresh seeds, bar read, controls.

## K1 read (2026-11-20, 6:27 am EST): PASSED on the tuning set

Prototype `tools/r8_proto.py`, runner `tools/r8_k1.py`, frozen by `scratch/freeze_r8_k1.sha256`
before the run and unchanged after it; one job under a 3 GB reservation (454 s, peak commit 0.17 GB);
`results/rung8-k1.json`, `logs/r8-k1.log`. No Lean, no doctor, no seed above 139.

**The 18 A networks are a tuning set from here on.** Before the freeze I ran the prototype on
them four times while designing it (plain first version; a finer ball; two tightened charges; a
different reference key). The count below is therefore how well a design fitted to these
networks fits these networks. It says the design is not hopeless; it is not an acceptance rate.

| Set | Networks | Accepted, skeleton and ball 2^-14 | Accepted, rung-7 skeleton and ball 1/1000 | Rung-7 checker |
|---|---|---|---|---|
| A u3 (ungated), screened | 18 | **18** | 1 | 0 |
| B u5 (gated), screened, test and reserve | 15 | **15** | 15 | 9 |

- **K1 (at least 6 of 18): passed, 18 of 18** at the design value. Worst proved bound per A
  network 0.056 to 0.180 against 0.25. Windows of 1 to 3 positions; 16 of the 18 have rows where
  two keys share the attention.
- **No A network is rejected at the design value**, so there is no per-network rejection reason
  to list there. At the rung-7 ball of 1/1000, 17 are rejected, every one because the output
  interval is wider than 1/4 (radius 0.20 to 0.85); 12 of those in rows with shared attention.
  By ball size, A accepted: 1 (2^-10), 9 (2^-11), 16 (2^-12), 18 (2^-13 and smaller).
- **What changed the picture is the ball, not only the checker.** These A networks amplify a
  weight perturbation about 13 times, and sampled perturbations at 1/1000 already reach 0.08 to
  0.16 (one network breaks at twice that radius). The registered 1/1000-ball statement is close
  to false for them. A ball of 2^-14 around a 2^-14-grid skeleton still contains the trained
  network, so the headline (the network as trained, every length, binary32) is unchanged; the
  robustness claim shrinks by a factor of 16. That is a change of statement and must be
  registered as one.
- **B improves as a by-product:** all 15 screened B networks, including the 6 the rung-7 checker
  rejects, at either ball.
- **Controls** (A u3 seed 110, ball 2^-14): wrong task, swapped embedding rows, negated read-out,
  radius times 16 and times 64 are rejected. The two A networks that failed the screen (107, 112)
  are ACCEPTED, and that is correct, not a failed control: both solve the task (error 0.03 to
  65,534 tokens) and failed only the screen's 1/1000-ball robustness test. No trained A network
  fails the task itself, so A has no "wrong network" control; on B, all 25 networks that fail the
  task are rejected (`results/rung8-k1-controlB.json`).
- **Numeric soundness test of the prototype** (not a proof): float64 forward passes with sampled
  perturbations inside the ball on short inputs, and float32 passes at 2,000 and 65,534 tokens,
  compared with the prototype's interval for the abstract case of each position: 137,282
  positions over 33 networks, 0 violations, smallest slack 0.0028.

**What the 18 of 18 rests on that is not proved.**
- P1 and P2 (marked in the code): for ungated heads the score-rounding slack is charged as 2^-10
  where rung 7 proved about 1.0, and the softmax-arithmetic error as B/2^16 where rung 7 proved
  B/100. My argument is that the competing keys are within three positions of the query, so their
  biases are small numbers, and that the rounded sums are dominated by their last few terms. Both
  are new lemmas about the rounding model. With the rung-7 charges in their place the prototype
  accepted 1 of 18 even at the small ball, so P1 and P2 carry the result.
- Affine forms and the ReLU relaxation, the weight bounds for shared attention, the window
  argument, and rational enclosures of exp that the kernel can evaluate: all new proofs.
- Kernel cost is unknown: up to 156 window states times 5 tokens with about 40 symbols per form.

**Odds for (a) now: about 30%**, up from about 20%. The weak link has moved. "Does the method
fit what training produces" was 40% and is now, on this evidence, about 85%. Soundness inside a
kill rule I keep at 50%: there are more and newer lemmas than in rung 7 (about ten kit cases),
and P1 or P2 failing as charged would reopen the fit question. Kernel feasibility about 70%.

**For the registration, if the go is given:** statement A with skeleton and ball 2^-14 and the
limit "fixed relative-position slope, no LayerNorm" in the statement's own words; fresh seeds
140 upward for the bar; P1 and P2 as the first two kit cases, because the design dies with them;
a kernel feasibility test on one tuning-set network before the other cases.
