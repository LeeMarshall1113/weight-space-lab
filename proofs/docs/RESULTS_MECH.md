# Mechanism rows for the rung 8 networks: results

Written 2026-11-21 (Saturday evening EST). Registered in `PREREG_MECH.md`; tools frozen by hash
(`scratch/freeze_mech.sha256`) after development on tuning-set networks and before any fresh
network was touched. These are **rows for the rung 8 write-up, not a rung.** Rung 8's frozen
files and results are unchanged (`scratch/freeze_r8_checker.sha256`: all OK); `Sound8` is used as
it stands.

## Row (b): the program read off the weights

**For all 19 trained networks that rung 8 accepted (fresh seeds 140 to 159 without 153), a finder
that is never given the task reads a finite-state program off the weights, and the kernel checks
that the network equals that program at every position of every input length, over the whole
2^-14 weight ball and in the binary32 rounding model. In all 19 cases the program has 5 states
and 25 rows and is proved equal to the task.**

Said in the same breath, as registered: this outcome was fixed in advance. A network already
proved within 1/4 of the task cannot be within 1/4 of a different integer-valued program, and the
task's smallest automaton has 5 states. The program is trivial because the task is: remember the
last digit, output the sum mod 5. What the row adds is narrower:

1. **The program comes from the weights alone.** `tools/mech_extract.py` imports no task. It
   enumerates the checker's window states, rounds each read-out enclosure to the nearest integer
   (failing if any is not within 1/4 of one), and minimises the resulting machine.
2. **The collapse is kernel-checked.** The certificates have 30 rows (3 networks), 155 rows (15)
   or 780 rows (1), indexed by the last one to three tokens per head. The program has 25, indexed
   by the last token only. So "the older tokens in the attention window do not affect the output"
   is a theorem per network, not an observation.
3. **It applies to a network whose task nobody wrote down**; see the control below, where it
   returns a different program.

### Theorems per network (generated file `runs/mech/<tag>/Net.lean`, no per-network proof work)

- `accept : check8 δ net prog cert = true` (the frozen rung 8 checker, with the extracted program
  as its task argument; every closed Boolean by `decide +kernel`);
- from `Lane4.R8K.sound8` unchanged: `skeleton_ok`, `exact_all_lengths`, `binary32` (the skeleton
  over the ball) and `trained_exact_all_lengths`, `trained_binary32` (the network as trained),
  each against `ptarget = prog.target`;
- `prog_is_task : ptarget w i = target w i` for every valid input and position, by a checked
  bisimulation with the rung 8 task automaton.

New Lean: `Lane4/MechBisim.lean` (60 lines, written by the study team): `bisim_sound`, axioms `propext`,
`Quot.sound`. **No kit case was used and no doctor tokens were spent.**

### Counts (`results/mech-rows.json`, collected from the logs by `tools/mech_collect.py`)

| | fresh, accepted by rung 8 (19) |
|---|---|
| extraction succeeds | 19 |
| kernel accepts against the extracted program | 19 |
| all seven theorems, standard axioms, no `sorry` | 19 |
| `prog_is_task` proved | 19 |
| program is the 5-state, 25-row one | 19 |
| within 900 s and 6 GB | 19 (largest: 470 s, 4.89 GB, the 780-row network) |
| `native_decide` | 0 |

Kernel time per file: 22 to 24 s (30-row certificates), 76 to 94 s (155 rows), 470 s (780 rows).
Tuning-set development, labelled as such: the finder on 20 networks (seeds 100 to 119), all the
same 5-state program; two of them (seeds 110 and 116) kernel-checked.

### The rejected network and the controls (rows with no bar)

- **Fresh seed 153** (rejected by rung 8 for an output interval of 2.030 ± 0.220): I registered
  the expectation that the extraction would fail. **It did not**: the finder's enclosure is
  slightly tighter than the frozen checker's on that row and it proposed the same 5-state
  program. The frozen checker then rejects, and the file proves `check8 … = false` in the kernel,
  as in rung 8. So the finder only proposes; the checker decides. The small difference between
  the finder's arithmetic and the mirror's is a looseness to fix before anyone relies on the
  finder's failure as a signal.
- **Embedding rows 1 and 2 swapped** (dev seed 110): the finder returns a 5-state program that is
  **not** the task: tokens 1 and 2 act as digits 1 and 0. **Kernel-checked** (25.8 s, 4.39 GB,
  standard axioms): `accept`, `skeleton_ok`, `exact_all_lengths`, `binary32` against that
  program, i.e. every network within 2^-14 of the altered skeleton computes the swapped-digit sum
  at every length. (No trained-network theorems: nothing was trained to this skeleton.) This is
  the one place where the pipeline certifies something we did not hand it as a task. It is still
  a network we altered ourselves, so it shows the pipeline is not hard-wired to task A; it is not
  a discovery about a network trained on an unknown task.
- **Read-out negated:** extraction fails (nearest integer −1; the task type has outputs in ℕ).
- **Read-out bias raised by 1/2:** extraction fails at the rounding step (read-out 0.531 ± 0.042 is
  not within 1/4 of an integer), as expected.

## Row (a): where each head looks

**For all 19 networks: in every network of the 2^-14 ball, in the rounding model, on every input
of every covered length and at every position, each head puts all but 2^-21 (about 4.8 × 10^-7)
of its softmax weight on a short window of its latest positions. Kernel-checked per network.**

| head | window proved | networks |
|---|---|---|
| head 0 (strict mask: sees earlier positions only) | **the previous position alone** (L = 1) | 19 of 19 |
| head 1 (causal mask: sees itself too) | itself and the previous position (L = 1) | 3 |
| | itself and the previous two (L = 2) | 15 |
| | itself and the previous three (L = 3) | 1 (seed 149) |

So for head 0 the stronger form, "at least 1 − ε on one named position", is a theorem on every
network. For head 1 it is not claimed and is not true in general: inside its window the weight
can be shared (the certificate's rows with mixed attention), and the theorem says only that
nothing outside the window matters. The windows are the certificate's, chosen by the checker from
the weights; a network with a larger window is one whose content scores vary more against the
fixed slope.

**What "weight" means here.** The exact softmax, `Real.exp` of the scores the network computes
in the rounding model, over the head's candidate keys. The network's own rounded exponentials
differ from it by the rounding model's error; the statement is about the scores, which is the
part a reader means by "where the head looks".

**Theorems.** Generic, new (`runs/mech-kit/ma/Spec.lean`, proof `Solution.lean`, 192 lines):
`Lane4.Case.head_tail8` (head level) and `Lane4.Case.attn_window8` (if `check8` accepts, every
head at every position has a window `P` of at most `L + 1` latest positions with the weight
outside it at most `3 * tailB` of the total). The bound was already a lemma inside rung 8's head
proof (`Lane4.R8KG.tail_real`); the case states and exports it. Per network
(`runs/mech/<tag>/Attn.lean`): `attn_window` (the generic theorem at this network, its program and
certificate, from the file's own `accept`), `attn_eps0`, `attn_eps1` (`3 * tailB ≤ 2^-21`,
`decide +kernel`), `attn_L0`, `attn_L1`.

**Counts** (`results/mech-attn.json`): 19 of 19 fresh networks with all attention theorems,
standard axioms only, no `sorry`, `native_decide` 0, within limits (largest 500 s, 4.89 GB).
Tuning-set development: seed 110 only.

**Cost.** One kit case, one Sonnet doctor, passed at its first submission (kernel-checked by the
study team's verdict tool), about 140,000 tokens. Budget set for the rows: 3 cases, 0.7 million tokens.

## Wording for any write-up (binding, from the registration)

Gross et al. (arXiv 2406.11779) have the idea that a mechanistic account is what makes a proof
about a trained transformer compact; this row is a small kernel-checked instance of it at every
length and over a weight ball. teal-sea's adder theorem already has the form "trained network
equals a finite-state program". The program here is trivial because the task is. No "first".

## Files

`PREREG_MECH.md`, `SCOPE_MECH.md`, `tools/mech_extract.py`, `tools/make_mech_net.py`,
`tools/mech_collect.py`, `tools/make_mech_attn.py`, `tools/mech_collect_attn.py`, `Lane4/MechBisim.lean`,
`runs/mech-kit/ma/` (kit case for row (a)), `results/mech-attn.json`, `scratch/freeze_mech_attn.sha256`, `runs/mech/` (one folder per network: `Net.lean`,
`lean.log`, `meta.json`), `results/mech-rows.json`, `logs/mech-gen-*.log`,
`scratch/freeze_mech.sha256`.
