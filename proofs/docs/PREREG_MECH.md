# the proofs study: mechanism rows for the rung 8 networks (registration)

Written 2026-11-21 (Saturday afternoon EST), after the project owner's go on `SCOPE_MECH.md` (b)
then (a), as **rows for the rung 8 write-up, not a rung**. Lee asked for the extension.

**Fixed conditions.** New files only. `Sound8`, the rung 8 checker, mirror and generator are used
as they stand; no rung 8 frozen file or result is edited (`scratch/freeze_r8_checker.sha256`
must stay all OK). Development on tuning-set networks (seeds below 140) only; the 19 accepted
fresh task-A networks (seeds 140 to 159 without 153) are touched only after the finder and
generator are frozen by hash. Budget: at most 3 kit cases, about 0.7 million Sonnet tokens in
all, one Sonnet retry per case, no stronger-model step; stop and report if it needs more. Rung 9 keeps
priority on reservations; one Lean job at a time; every run under a reservation.

## What had been seen when this was written

`RESULTS_R8.md` and everything behind it. No extraction has been run on any network.

## A fact to state before anything is run

For a network that rung 8 already accepted, **the extracted program cannot differ from the
task.** `Sound8` puts the network within 1/4 of the task's integer target; a second acceptance
puts it within 1/4 of the extracted program's integer output; two integers within 1/2 are equal.
So on the 19 networks the minimal program is determined in advance: the task's own minimal
automaton, which has **5 states and 25 rows** (the state is the last digit; BOS behaves as digit
0). `SCOPE_MECH.md` said 6 states and 30 rows; that was a miscount of mine.
What the rows can still show is therefore limited to three things, and the write-up must not
suggest more: (1) the program is obtained from the network's weights alone, the finder is never
given the task; (2) the reduction from the certificate's 30, 155 or 780 rows to 25 is itself
kernel-checked, i.e. the older tokens in the attention window provably do not affect the output;
(3) the same pipeline applies unchanged to a network whose task nobody wrote down.

## (b) Extracted program

**Extraction rule (fixed now).** Input: the skeleton W14 and the radius 2^-14. Nothing else; the
finder (`tools/mech_extract.py`) does not import the task.
1. Enumerate the reachable window states exactly as the rung 8 checker does (per head, the list
   of the newest L key tokens; L, the score and value tables from the weights).
2. For each state and each next token compute the read-out enclosure centre c and deviation d.
   The row's output is the integer n nearest to c. **If |c − n| + d > 1/4 for any row, the
   extraction fails for this network** and that is its reported result.
3. This gives a Mealy machine on window states. Merge states by partition refinement (states
   are equal when they give the same output and equivalent successor for every token) to the
   minimal machine; number its states in order of first visit from the initial state.
4. The program is that machine as a `Task` (`ntok`, `init`, `step` and `out` as lookup tables).

**Theorems per network** (generated file, closed Booleans by `decide +kernel`, standard axioms,
`native_decide` banned):
- `accept : check8 δ net prog cert = true`, with `prog` the extracted program;
- `program_all_lengths`, `program_binary32`: the rung 8 theorems `trained_exact_all_lengths` and
  `trained_binary32` with `prog.target` in place of the task's target (the network as trained,
  every length; and the skeleton over the whole ball, `skeleton_ok`);
- `prog_is_task`: for every valid input and position, `prog.target w i = target w i`, where
  `target` is the registered task-A target. By a checked bisimulation between `prog` and the
  rung 8 task automaton, and the rung 8 lemma `target_eq`.

**New Lean, one kit case (kit case 1).** `Lane4/MechBisim.lean` (new): a Boolean `bisimOK T1 T2 R`
(R a list of state pairs containing the initial pair, closed under every token with equal
outputs) and the theorem that it implies equal `Task.target` on every input with tokens in
1..ntok at every position 1 ≤ i ≤ length. If the study team can prove this short lemma directly, no
doctor is used and the case is not counted.

**Success for (b), fixed now.** On the 19 accepted fresh networks: the extraction succeeds, the
kernel accepts with `prog`, `prog_is_task` is proved, each within 900 s and 6 GB per file.
Reported for **every** network: the certificate's states and rows, the minimal program's states
and rows, its tables, whether it is the 5-state program, kernel time. A network where any step
fails is reported with the step and the reason. Counted separately and labelled: the tuning-set
networks used for development.

**Also run, reported as rows with no bar:**
- the one rejected fresh network (seed 153): the extraction is expected to fail at step 2;
- three of the rung 8 wrong-network controls, those that still compute *something* (embedding rows
  swapped, read-out negated, read-out bias raised by 1/2, on dev seed 110): what does the finder
  return? A certified program different from the task would be the one place where this
  pipeline tells us something we did not put in. Kernel-checked if the extraction succeeds.

## (a) Attention facts, in the window form

**Statement (in words; the Lean statement is fixed by an amendment, type-checked, before its kit
case).** For a network and certificate accepted by `check8` at radius δ, for every head h with
certificate window L_h: in every network of the δ-ball, in the rounding model, for every input
of every covered length and every position i ≥ 1, the attention weights of head h at query i on
keys outside the L_h newest allowed positions (L_h + 1 for the causal head, which also sees i)
sum to at most ε_h, where ε_h is computed by the checker from the certificate (of the order of
the tail bound, e^-16). Not claimed: weight 1 − ε on one named position; the checker's own table
shows rows where two keys share the weight.

**Per network:** L_h and ε_h for both heads, and from the mirror's table the largest weight
interval of a non-reference key (how far the head is from one-hot), reported as a mirror figure
unless a second kit case exports the per-row weight intervals as a theorem.

**New Lean:** kit case 2 (window mass), kit case 3 only if the per-row intervals are exported.
**Success for (a):** the window-mass theorem kernel-checked with standard axioms and
instantiated for the 19 networks without new per-network proof work.

## Wording (binding)

- Gross et al. (arXiv 2406.11779) have the idea that a mechanistic account is what makes a proof
  about a trained transformer compact, and measure it. These rows are a small kernel-checked
  instance of that thesis at every length and over a weight ball; they do not originate it.
- teal-sea's adder theorem already has the form "trained network equals a finite-state program"
  (exact integers, threshold RNN). Row (b) is that form for softmax attention with rounding and
  a ball, with the program read off the weights. Cite both.
- The program is trivial because the task is. Say so in the same sentence as the result.
- No "first".

## Frozen before the fresh networks

`scratch/freeze_mech.sha256`: this file, `tools/mech_extract.py`, `tools/make_mech_net.py`,
`Lane4/MechBisim.lean` and its proof module. Written when development on the tuning set ends;
the study's private log (not included) records the moment.
