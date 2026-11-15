# reading/: reading and certifying small networks from their weights. Four finished units, all boundaries or negatives

Personal work. Views are my own.

This folder holds four finished units from a study of LLM agents ("doctors") reading and
analysing small neural networks from their weights, and of kernel-checked certificates for them
(units 3 and 4 use no agents). None is a positive headline result.
Each is a boundary or a negative, stated with what it does not show. Numbers below are
copied from `RESULTS.md` in this folder (an excerpt of the study's own results file). **The
agent runs and the numeric scripts were not re-run for this release.** The Lean files of
units 3 and 4 were re-checked from a clean clone; see `../proofs/VERIFY.md`.

Not included: the earlier RNN stage (reading, repairing and extending random small RNNs, closed).

## Unit 1. Compiled versus trained transformers: weights-only reading works only on compiled ones

*Question.* Can a Sonnet agent, given only the weights of a small transformer, write a RASP
program with the same function (functional match: at least 0.99 whole-sequence agreement
with the network on 1,000 held-out inputs)?

*Result* (`RESULTS.md`, "Transformer stage", n = 20 networks per decisive arm, one run per
network, every run audited for rule breaks):

| Networks | Weights only | 20 input-output examples only |
|---|---|---|
| Tracr-compiled | **20/20** functional | 14/20 |
| Gradient-trained (2 layers, d = 64) | **0/20** | 19/20 |
| Trained for discreteness (annealed attention, L1-sparse MLPs, or both) | **0/41** | 10/12 on the "both" nets |

On compiled networks weights-only reading beats the examples-only arm (McNemar p = 0.016,
6 against 0 discordant cases). On trained networks it fails completely, and weights plus
five queries do no better than five queries alone (7/20 against 8/20). Training for
discreteness did not make trained networks readable. Reading survives a random rotation of
the residual basis (16/20) and a larger scramble (20/20).

*What it does not show.*
- **Function, not source.** On the compiled networks the doctors recover the function but
  rarely the original program: 3 of 20 exact structure, 6 partial, 11 different (blind
  Sonnet judge).
- **The compiled case is the easy case:** compiled weights are sparse and structured, and
  the doctors read them by pushing hand-built residual vectors through the layers.
- **The two arms are not matched in everything.** The compiled calibration used the same
  program pool without one template (the "permute" template) that the trained networks
  included. Other differences (architecture, size) were not isolated.
- A prior-only guesser that knows the program generator scores about 17 to 18 of 20 given 20
  examples, so the program pool is easy from examples.
- One doctor model, one run per case, n = 20, no second model.
- **Comparisons with published decompilers are not like-for-like.** A neural decompiler
  (Thurnherr and Riesen, arXiv 2410.00061) reported 73% functional on its own generator
  and check. An analytic decompiler for trained transformers (arXiv 2602.08857) was **not
  run**: it needs a different model family and retraining, so no comparison is made.
- Whether weights-only reading of trained networks is possible by other means is not
  addressed.

Pre-registration: `docs/PREREG_XF.md` (with amendments). Data: `results/doctor_XF-*.jsonl`,
`results/xf_*`. Code: `xf/`. The compiled networks (`xf/cases_tracr*`) are included. The
trained networks (about 54 MB) are not; the case manifests list seeds, regeneration was
not tested for this release.

## Unit 2. A decay curve from compiled networks could not be built (corrected)

*Question.* Starting from compiled (readable) networks, move them step by step toward
trained-like weights while keeping the function, and measure where reading breaks.

*Result* (`RESULTS.md`, "Legibility decay curve", with its correction). The pre-registered
feasibility rule stopped the experiment: no gradient arm moved any compiled network to 0.05
relative parameter drift while keeping sampled agreement at or above 0.99 (0/20 for each of
six learning rates). One noise-and-repair schedule and one compression schedule kept 6 to 7
of 20, mostly the same networks. No doctor episodes were run.

*Corrected, as the results file says.* The first write-up claimed more than the data show.
Withdrawn: that the other 14 networks "have essentially no robustness margin", that
compiled networks "are isolated points, not one end of a continuum", that this explains why
gradient training never lands on compiled-like weights, and that "write tables lose
discreteness first". What was shown: these schedules, at these budgets, failed. That does
not show that function-preserving paths do not exist (exact rotations and scalings in the
perturbation ladder preserve the function). The agreement gate is sampled (1,000 random
inputs) and the same inputs were reused to pick checkpoints.

Pre-registration: `docs/PREREG_DECAY.md`. Data: `results/decay_*.jsonl`. Code: `xf/decay*.py`.

## Unit 3. The bridge: kernel-checked weight-ball certificates for tiny trained ReLU nets, and where they stop

*Statement tested.* A small trained ReLU classifier (n boolean inputs, two hidden layers,
one output) on an exact finite spec has a Lean-kernel-checked certificate: **for every
weight and bias within 1/1000 (absolute) of the trained values, the output has the correct
sign on every one of the 2^n inputs.** Method: weight-space interval bound propagation in
exact rationals, proved sound once (`bridge/lean/Bridge/IBP.lean`), then checked per input
by kernel reduction (`decide +kernel`; no `native_decide`; axioms within the standard three).
No proof agents were used. **The method is known** (interval bound propagation, Weng et al.
2020; Lean-checked variants exist); nothing here is a new technique.

*Results* (`RESULTS.md`, "Bridge"; test seeds run once, bars fixed in `docs/PREREG_BRIDGE.md`
before training):
- **Stage 1 (n = 6, popcount mod 3, 16 test networks):** 8/8 ordinarily trained and 8/8
  "structured" networks kernel-checked at 1/1000 (bar: at least 6 of 8, met). The
  pre-registered "structured training helps" effect was **not met** (certified radius
  0.77 times the ordinary one, not 4 times). The certificate is about the quantized network
  (multiples of 1/256).
- **Tightness:** the smallest confirmed breaking radius over the largest certified radius has
  median 1.29 (range 1.01 to 2.47; bar at most 4, met).
- **Float weights:** on the exact dyadic float64 weights of 8 retrained networks, 8/8
  kernel-checked, removing the "quantized only" caveat at n = 6.
- **Size ladder (fails):** the fraction of networks certified at 1/1000 is 8/8, 8/8, 5/8, 0/8
  at n = 6, 8, 10, 12 inputs. Per-input Lean cost grows with 2^n (about 1 to 2 s per input);
  per-input checking stopped at n = 10 (a 900-second time limit was hit). Region certificates
  (cubes of inputs) on a majority task cover about 0.55 to 0.67 of 2^n and do not shrink
  with n. The pre-stated closure conditions both hold: **this kind of certificate does not
  get beyond enumeration of small input spaces and cannot carry to unbounded inputs.**
- **Radius alone is not evidence:** random near-constant networks, certified against their own
  sign, reach larger radii (up to 0.035) than any trained network; radius must be read against
  margin and tightness. "STR has more radius per unit margin" is descriptive, not a registered
  effect.

*What it does not show.* Nothing about transformers, attention, or inputs of unbounded
length; only finite Boolean inputs and small ReLU networks (hidden width 16 to 64). The
statement is the weight ball of the `proofs/` study at one radius. The size ladder uses
CPU timings from a shared machine. A route to all-length statements for trained networks
would need a symbolic or relational certificate or a different statement (for example a
recurrent network with a proved invariant); the study's next stage, on that, is unit 4
(trained RNNs), which also stops short of a pass.

Pre-registration: `docs/PREREG_BRIDGE.md` (amendments A1 to A8). Lean files:
`bridge/lean/Bridge/` (`IBP.lean`, `Region.lean`, `Nets/*.lean`); data: `results/bridge_*`,
`bridge/nets/`. Python: `bridge/*.py`.

## Unit 4. The RNN invariant: kernel-checked all-lengths certificates for trained RNNs, and where they stop

*Statement tested.* A trained clipped-ReLU Elman RNN (hidden width 4 to 16) recognising a
small regular language has a Lean-kernel-checked certificate: **for every weight and bias
within 1/1000 (absolute) of the trained values, the RNN's accept/reject read-out is correct
on every input string of every length.** Method: a finite family of boxes in hidden-state
space, one per cluster of reached states, with a transition map between them, proved sound
once (`bridge/lean/Bridge/RNN.lean`, `RNNClust.lean`) and then checked per net by kernel
reduction (`decide +kernel`; no `native_decide`; standard three axioms). The certificate
size does not depend on the input length. **The idea (an inductive invariant) is standard;
nothing here is a new technique.** No proof agents were used.

*Result, as registered* (`RESULTS.md`, "RNN invariant ... test result"; test seeds 100 to 107,
one blind run of the frozen procedure, bars fixed in `docs/PREREG_RNN.md` and its amendments
A1 and A2 before the run). **No pass.** Certified at 1/1000, out of 8 test seeds per cell
(gate = the net is exact on all strings of length at most 12 and on 1,000 strings of length 200):

| Language (width) | Ordinary training: gate / certified | Saturation-penalty training: gate / certified | Random-weight control |
|---|---|---|---|
| Parity (8) | 5 / **3** | 1 / **1** | 0/8 |
| Mod-3 counter (16) | 4 / **0** | 2 / **0** | 0/8 |
| Tomita 4 (8) | 6 / **1** | 5 / **4** | 0/8 |

- **Pass bar (at least 6/8 on parity, and mod-3 above 0): not met.** Status: **boundary**.
- **"Trained to be certifiable helps"**: met on Tomita 4 only (4 against 1, one-sided
  Fisher p = 0.14, so weak), and reversed on parity (1 against 3, because the penalty made
  most parity nets fail the gate: 1/8 against 5/8).
- **Why it stops (cluster count).** The nets are exact, but they reach many saturated
  hidden-state points, not one per state of the minimal automaton (2 to 4 states). The
  certified nets use 5 to 20 clusters; the gate-passing nets that did not certify use 12 to
  149 (mod-3: 24 to 149, none certified). Failure tracks the cluster count.
- A trivial-language control (accept everything) certified 4/4 with 2 to 4 clusters.
- **Tightness caveat.** Only one net has a confirmed break (Tomita 4, penalty arm, seed 105,
  at radius 0.0263, ratio 1.21 to the certified radius). For the other 8 the break search
  found nothing up to 1/2, and **that is a limit of the search, not evidence the nets are
  robust**: the clip saturates, so the gradient-sign attack sees no gradient on the recurrent
  weights. Certified radii are therefore not shown to be near-tight. No bar depends on this.
- **The pipeline-check net** (`RNNC_L3_ORD_d4_s2`: Tomita 4, ordinary, width 4, seed 2) was
  trained to check the pipeline and is outside the dev and test sets; it is not counted above.
  Its certified radius is 0.0062 and its smallest exactly confirmed break 0.0107 (ratio 1.72).

*What it does not show.* Nothing about transformers, or about languages beyond three small
regular ones; nothing about nets that were not trained with this recipe; and the 9
certificates are for nets that passed a sampled gate and then a certificate, so they say
"these nets are certified", not "trained RNNs are generally certifiable". The registered design allowed one revision (A1);
there is none left.

Pre-registration: `docs/PREREG_RNN.md` (amendments A1 and A2) (the earlier scope note is not included). Dev results: `results/rnncert_dev*.jsonl`. Test rows:
`results/rnncert_test_*.jsonl`, `results/rnncert_breaks.jsonl`. Code: `rnn/` (training, gate,
cluster search, Lean export, break search; run order in `rnn/rnncert.py`). Lean:
`bridge/lean/Bridge/RNN.lean`, `RNNClust.lean`, `Nets/RNNC_*.lean` (the nine test
certificates and the pipeline-check net). `rnn/nets/` holds only those ten nets of the 116
the study trained. *Release note:* the frozen sha256 list of the pre-registration covers the
original files; the copies here differ from them only in a docstring line each (internal
wording removed) and a usage-path line, so their hashes differ.

## How to check

Set up as in `../proofs/README.md`, then, from the repository root:

```bash
python reading/bridge/recheck_bridge.py            # stage 1, float weights and one n = 8 net: about 50 minutes; --set stage1 for the 16 main certificates
```

Each net file prints `#print axioms` for its certificate; the script requires them within
`propext`, `Classical.choice`, `Quot.sound`. In the release re-check 27 of 27 of these (16 stage-1 nets, 8 float-weight nets, 1 n = 8 net, plus the two framework files) passed; the one n = 10 majority region file that was tried (`--set region`) did **not** finish within 1,500 s, in line with the study's own report that the first full region certificate hit its 15-minute stop. Rows are written to
`proofs/results/recheck-bridge.json`. Unit 4:

```bash
python reading/bridge/recheck_bridge.py --set rnn --out proofs/results/recheck-rnn.json   # 9 certificates, about 12 s each (build of the two RNN framework files first)
```

 The Python scripts (`xf/`, `bridge/`) need numpy and
PyTorch; they were not re-run for this release. `xf/` also needs Tracr (Apache-2.0) to
rebuild compiled networks; the compiled networks themselves are included.

## Notes and licence

Third-party code is not redistributed. `xf/rasp.py` is a small RASP interpreter written for
the study; whether any part resembles Tracr code was not checked line by line. Code and Lean
files: Apache-2.0; text: proposed CC-BY-4.0 (see the top-level README). Doctor audit
excerpts in `results/xf_*audit*.csv` are short code snippets from agent tool calls kept as
audit evidence; full transcripts are not included.
