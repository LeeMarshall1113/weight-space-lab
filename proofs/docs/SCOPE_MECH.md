# Scope: from "what the network does" to "how it does it" (rung 8 networks)

Written 2026-11-21 (Saturday afternoon EST) at the project owner's request, for the project owner's question.
**Scope only, one page: nothing registered, nothing prototyped, no proof work, no doctor tokens;
rung 8 frozen files untouched.** Odds are my judgement. What I read in the Lean source is marked;
the rest is reasoning.

## What is already there

`Sound8` says what every network in the ball outputs. Its proof and each certificate already
contain a mechanism, unexported:

- per head, the checker computes an interval for each attention weight inside a window of the
  last one to three positions and a bound on everything older (`weightIV`, `tailB` in
  `Lane4/R8Cert.lean`); the head lemma `HeadSound8` (`R8KG.lean`) proves the head's output is the
  matching mixture of value vectors, but states it as an enclosure of the output, not as a
  statement about the weights;
- per network, a table: (current token, recent tokens per head) → output interval. 19 accepted
  task-A networks: 30 rows (3 networks), 155 rows (15), 780 rows (1);
- `Task` is an argument of `check8` and of `Sound8`: any finite automaton (`ntok`, `init`, `step`,
  `out` over ℕ; read in `R7Cert.lean`), not only the one we wrote down.

## Candidates

**(b) Extracted program. Cheapest, and I think the best.** The finder never needs the task: it
can round each row's interval centre to the nearest integer, merge states with equal behaviour,
and emit the smallest automaton T′ that the table defines. Then `check8 δ N T′ cert` by
`decide +kernel` and **`Sound8` as it stands** gives: every network in the ball is within 1/4 of
T′ at every position of every length. A second small theorem, by `decide`, says T′ and the
intended task agree (or, for a network trained on something else, T′ simply is the finding).
- New Lean: none for the main theorem. One small lemma that two automata with a checked
  bisimulation have equal `target` on all inputs: 1 kit case, about 0.1 to 0.2 million tokens.
  Generator work in Python.
- Readability, said plainly: for task A the minimal program should be 6 states and 30 rows
  ("remember the last digit; output the sum mod 5"). It is readable because the task is trivial.
  The 155 and 780 row tables collapse to the same 30; that collapse is itself a checked fact
  (the older tokens in the window provably do not matter).
- Odds 90%. Not yet verified: that `decide` evaluates a table-defined `step` inside the limits
  (I expect so; the supplied task is evaluated the same way).

**(a) Attention facts.** "On every input of every length and every weight in the ball, head h
puts at least 1 − ε on the last L positions, and weight in [lo, hi] on each of them", with L, ε,
lo, hi per network from the certificate.
- New Lean: the facts are proved inside the 1,700-line head lemma but not stated; exporting them
  means a new statement and a proof that reuses its sub-lemmas (`geo_tail`, `weights_symbols`).
  1 to 2 kit cases, 0.3 to 0.5 million tokens. Odds 80%.
- Honest form: "1 − ε on ONE named position" is false for some accepted networks. The checker
  marks rows with mixed attention (a second key above 1%), and for those the true statement is
  about the window. ε for the window is of the order e^-16.

**(c) Component roles by ablation.** "With head h's value matrix zeroed (or tokens a, b swapped in
it) the network is wrong by more than 1/4 on this input."
- New Lean: a refutation direction the study team does not have. The enclosures are proved sound only
  under an accepting check; one needs "a case enclosure that excludes the target, plus a concrete
  input reaching the case, implies a wrong output". 2 to 3 kit cases, 0.6 to 1 million tokens.
  Odds 60%. It proves necessity on one input, not a role in general; "which direction carries
  which token" as a universal statement I do not see how to state without overclaiming.

**(d) Two blocks (if rung 9 passes).** The rung-9 certificate has to name classes of block-one
outputs ("this position holds token t after token p") that block two reads back. Exported, that is
a checked account of composition: what block one writes, what block two reads. Cheap **if the
classes are kept explicit in `check9` from the start**; I will design for that. 1 to 2 kit cases
on top of `Sound9`; odds 70% given rung 9 passes (itself about 20%).

## Against prior work, so we do not overclaim

- **Gross et al. (2406.11779)** own the idea that a mechanistic account is what makes a proof
  about a trained transformer short, and they measure it (proof length against bound tightness,
  151 seeds, Max-of-K, fixed length, accuracy bounds). Ours would differ in object, not idea:
  kernel-checked, every length, a weight ball, exact per-position correctness. We must not write
  that we "connect proofs and mechanisms"; they did. Our certificate is a small instance of their
  thesis.
- **teal-sea**: their trained RNN adder theorem already is "network equals a finite-state
  program" (5 reachable states, kernel-checked, all lengths, exact integers). (b) is that
  statement for softmax attention with rounding and a ball, with the program read off the
  network. Cite them for the form.
- Neither, as far as I have read, exports attention-weight facts at every length; (a) looks new
  but small.

## Level, and where it belongs

**A row in the rung 8 write-up, not a rung.** (b) plus (a) cost 2 to 3 kit cases and turn the
headline from "it computes the task" into "it is this 30-row program, and here is where each head
looks, proved". That makes rung 8 easier to explain and harder to dismiss as a black-box check;
it does not change its level, because the mechanism of a one-block two-token network is trivial
and a reader will say so. The level-raising version is (d): an explained composition in a trained
two-block network. So: (b) and (a) as rows for the rung 8 release if the release can wait a day
for them; (c) only if someone asks for causal evidence; (d) folded into rung 9's design now.

Not done for this page: no new literature search (the two comparisons rest on the readings in
`SCOPE_R8.md`), no prototype of the extraction, no kernel timing.
