# proofs/: kernel-checked transformers: proofs, checker and data

Personal work. Views are my own.

Status: flagship folder of the weight-space lab repository (version 0.5). Nothing here has been peer reviewed. The full technical report is `REPORT.md` (living, with a claims table, a changelog and a "how to correct us" section); this README is the short version. All commands below run inside this folder (`proofs/`).

This repository holds the Lean 4 proofs, the checker, the specification pools, the
pre-registrations and the per-case results behind a study of LLM-written networks with
Lean-kernel-checked correctness proofs ("rungs" 2 to 8 below; rung 1 is background).
Every claim below is copied from the results files in `docs/` (`RESULTS*.md`) and the claims
table of `REPORT.md`, which state the same limits.

## Claims (exact wording)

**Rung 4 (main result).** 11 of 12 written transformers kernel-checked correct at every
length for every weight setting within 0.5% (relative), and under a modelled rounded
forward pass up to 65,535 positions; non-counting tasks only. Written and proved by LLM
agents (Sonnet family), one fresh agent per case. Plain-code control: 12 of 12, with
proofs about a tenth the length (median 54 against 559 lines).

The theorem for each network (`Spec.lean` `Statement`, `Final.lean` `final`): for every
rounding function `fl` with `Rounding u fl`, `0 ≤ u ≤ 2^-24`, every relative perturbation
of every weight by at most 1/200, every input whose length satisfies
`u·(length+1) ≤ 1/256`, and every position: `|output − target| ≤ 1/4`. With `u = 0` this is
exact arithmetic at **every input length**; with `u = 2^-24` it covers up to 65,535 input
tokens.

**Rung 3.** 12 of 12 ReLU networks (Sonnet) proved to stay within a stated tolerance of an
exact specification for every weight and bias within 1/1000 (absolute, zeros included) on
the whole input box. Control 12 of 12.

**Rung 2.** 10 of 10 hard-attention transformers (3 parity, 3 Dyck, 2 sort, 2 addition)
proved correct at every input length in exact arithmetic about the written weights only.
Control 10 of 10.

**Fragility measurement (from rung 3, "Part B").** For all 10 rung-2 transformers, moving a
single weight by an absolute 1/1000 makes the network wrong at some length of at most 20;
8 of 10 still break at 1e-6 (the two addition networks at 1e-4, not 1e-5). The proved
sort network `s00` gives wrong outputs in float32 from length 300 and is correct in float64.

**Rung 5.** 12 of 12 written softmax transformers kernel-checked within 1/4 of the target at
every position for every relative weight change within 1/200, with two corollaries:
exact real arithmetic at every length, and a binary32 model (underflow term and range bound,
with the accuracy of the float exponential as an assumed hypothesis, checked numerically on a
sample) for up to 65,535 tokens. Non-counting tasks only. A lemma kit and a worked example
carry the softmax and float analysis. Plain-code control 12 of 12 (median proof 43.5 lines
against 810). One pre-registered numeric check failed (bit-identity of two float32
implementations on `c04`) and is reported as failed. `docs/RESULTS_R5.md`.

**Rungs 6b and 6c (necessary radius for counting tasks).** For the three proved parity
networks p05, p10, p29, no relative ball of radius 1/(2L-1) or more is correct up to length
L, so no positive radius is correct at every length (rung 6b); for every "token-blind"
network, which includes the two proved sort networks, the same holds for parity and sort
rank (rung 6c). The general phenomenon is known (Hahn and Rofin); the classes are narrow;
whether it holds for the whole architecture is open (`Lane4/Conjectures.lean`, statements
type-check, nothing proved). `docs/RESULTS_R6B.md`, `docs/RESULTS_R6C.md`.

**Rung 6a (an additive ball, with a non-standard gate).** 12 of 12 written gated softmax
transformers (softmax attention with a relative-position slope and one gate neuron per head,
`Lane4/AGate.lean`) kernel-checked within 1/4 of the target for every additive change of every
weight by at most 1/1000, at every length in exact arithmetic and up to 65,535 tokens in the
binary32 model; non-counting tasks only. The kit was amended once after the development pilot
(7 of the 12 proofs use the added lemma). `docs/RESULTS_R6A.md`.

**Rung 7 (a checker with one soundness theorem, trained networks).** One Lean theorem
(`Lane4.R7K5.sound`) for a computable checker; a generated file per network, with no proof work.
For gradient-trained gated one-block width-8 networks: 4 of 9 screened reserve networks
(4 of 20 seeds) are accepted; 0 of 18 on the standard ungated architecture. The held-out
figure is the one to quote. `docs/RESULTS_R7.md`.

**Rung 8 (the same method on standard softmax attention, at a small ball).** One Lean theorem
(`Lane4.R8K.sound8`); for 19 of 20 fresh seeds of gradient-trained one-block width-8 softmax
networks without a gate, a generated file proves the task at every length for the weights as
trained, and for every additive weight change of at most 2^-14 around those weights rounded to
multiples of 2^-14 (exact arithmetic at every length; binary32 model up to 65,535 tokens). The
radius was chosen on the tuning set, the checker was fitted to earlier networks of the same
recipe, the task is local and the position slope is fixed. `docs/RESULTS_R8.md`;
`../writeup/NOVELTY_R8.md` (what is and is not new).

**Mechanism row (b) for rung 8.** For the 19 accepted fresh networks, a finder that is never given the
task reads a 5-state, 25-row program off the weights and the kernel checks the network equals it
at every length over the same ball; the program is proved equal to the task. The outcome was
fixed in advance and the program is trivial because the task is. `docs/RESULTS_MECH.md`,
`runs/mech/`, `REPORT.md` Section 6.11. **Row (a):** on the same 19 networks, each head puts all but
2^-21 of its softmax weight on a short window of its latest positions (head 0: the previous position
alone), kernel-checked; head 1's weight can be shared inside its window.

**Rung 9-LN15 (LayerNorm; a post-hoc rung).** The registered LayerNorm rung at ball 2^-14 stopped at its
kill rule (5 of 18 tuning networks accepted; the line was 6) and stays recorded as a failure
(`docs/PREREG_R9LN.md`, `docs/RESULTS_R9LN.md`). A new rung then chose the radius 2^-15, the enclosure design,
the symbol layout and fixed-point arithmetic after seeing that table, on the same 18 tuning networks
(`docs/PREREG_R9LN15.md`, Amendment 1). One soundness theorem `Lane4.LNC.SoundLN` (`Lane4/LNCert.lean`,
proof modules `Lane4/LNK*.lean`) covers a checker of a one-block width-8 softmax network with three
LayerNorms; a generated file set per network proves it. On fresh seeds 400 to 419: 20 trained, 19 compute
the task and pass the screen, **13 of 19 proved**, 6 screened networks computed the task and are not
proved; bar 3 of 3; 7 of 7 controls rejected. The ball is the smallest around the rounded weights that
contains the trained network; the exponential and square root are assumed accurate; five tokens, a local
task. `docs/RESULTS_R9LN15.md`, `runs/r9ln15-nets/`, `REPORT.md` Sections 6.12 and 6.13.

**Perturbation 2x2 and witnesses.** Additive versus relative perturbation for rung-2 and
rung-4 networks, as finite searches, with three Lean-checked witnesses in `runs/witness/`.
The earlier "fragile versus robust" framing is withdrawn. `REPORT.md`, Section 3.

## Limits (read before citing)

1. **Non-counting tasks only** at rung 4. Parity, Dyck and sort are excluded: they need a
   ball that shrinks like 1/n (analysis, not proved), and no agent was run on them.
2. **The ball is relative; zeros stay exactly zero.** Weaker than rung 3's absolute ball;
   it does not cover additive noise or pruning. The rung-2 fragility test perturbs
   absolutely (zeros included), so the fragility numbers and the rung-4 ball are **not
   like-for-like**.
3. **The rounding statement is about a model, not IEEE arithmetic.** Not modelled:
   overflow, underflow, subnormals, fused multiply-add, reordered or vectorised sums,
   softmax. A real float32 run is linked to the theorem only by numeric checks that found
   no failure. The rounded statement is length-bounded (65,535 tokens).
4. Hard attention with ties averaged, not softmax. Hand-written weights, not trained.
   Width at most 15. One model family, one radius, one tolerance, 12 cases.
5. **The transformers add nothing practical over a verified program**: the plain-code
   control solved every case with much shorter proofs. The two arms prove different
   statements.
6. **Tasks were chosen knowing which mechanism works**; the tasks were easy for the model
   with the supplied lemma kit and worked example (11 of 12 at a median of 2 submissions).
7. **The one rung-4 miss (`i03`) is an agent crash** (API output-limit error, no
   submission), counted as a fail. A rerun died the same way and is not counted.
8. **Novelty rests on a web search over abstracts** (`docs/NOVELTY.md`); "not found" is
   weaker than "does not exist". Related work is not summarised in this README.
9. The theorems are only as good as the files `Spec.lean`, `Final.lean` and
   `Lane4/RSeq.lean`, which the authors wrote; the kernel does not check them against
   intent.

## Layout

```
lean-toolchain, lakefile.toml, lake-manifest.json   Lean 4 + Mathlib pin
Lane4/                 frameworks: Basic, Seq (rung 2), Robust (rung 3), RSeq (rung 4), RSoft* and Bin32 (rung 5), AGate* (rung 6a), R7* (rung 7), R8* (rung 8), LN* (rung 9-LN15, 20 modules); Export*.lean.txt templates
tools/check.py         the checker (one command checks one case)
tools/recheck_all.py   re-check every case folder under runs/
tools/*                case builders, pools, draws, export and numeric-check scripts, result collectors
pool/                  specification pools and the seeded draws
examples/, prompts/    worked examples and the agent prompt files
runs/r7-nets, r8-nets/<tag>/Net.lean   generated per-network files of rungs 7 and 8 (and their controls), with a recorded Lean log
runs/r8-fresh/{A,B}/<recipe>/s<seed>/   the trained networks of rung 8 (T.json, W.json, W14.json, screens)
runs/r6-kit, r7-kit, r8-kit/<id>/   framework lemmas proved by agents (kit cases)
runs/rungN-test|dev/{net,prog,twin}/<id>/
                       case.json, Spec.lean, Final.lean, Solution.lean, TASK.md,
                       attempts/NN.json + NN.lean (every submission with the checker's verdict),
                       net.json (exported network), r3_checks.json / r4_checks.json
results/               per-case result JSONs (the sources of the write-up's tables)
REPORT.md              the living technical report (claims table, known weaknesses, changelog, responses to two reviews)
writeup/               notes cited by the report (2x2 version 2, open problems, token-blind usage)
scratch/               statement files and sanity scripts named in the freeze lists
docs/                  PREREG*.md (pre-registrations, with dated amendments), RESULTS*.md, NOVELTY.md, freeze_*.sha256
smoke/                 negative controls (wrong weight, sorry, native_decide, banned token) for the checker
VERIFY.md              what was re-run from this folder, with times
```

`runs/rung4-test/net/i03` has no `Solution.lean` (no submission); `runs/rung4-test/net-rerun/i03`
is the untouched rerun (also no submission). Rung 1 is included only as
`runs/rung1-test/{net,prog}`; its trained-twin arm is summarised in `results/twins-test.json`
but its model files are not included. Rung 0 is not part of this release. The per-network files of rungs 7 and 8 are `runs/r7-nets/*/Net.lean` and `runs/r8-nets/*/Net.lean` (with the trained and rounded weights in `runs/r8-fresh/`); they are checked with `tools/build_net.py` or `tools/recheck_r678.py`, not through `check.py`.

## Setup

Tested versions: Lean `leanprover/lean4:v4.35.0-rc3` (file `lean-toolchain`), Mathlib
`v4.35.0-rc3` = commit `c55e6e786f49471c72fbddbec5415808896aec1e` (see `lake-manifest.json`
for all dependency commits). Python 3.10 or newer; numpy only for the numeric scripts.
The checker's memory guard (a kill if one Lean process passes 4.5 GB) works on Windows
only; on other systems the guard is inactive. In the recorded re-check (`VERIFY.md`) one Lean process peaked at 2.8 GB working set
at most; plan for 4 to 8 GB free.

```bash
elan toolchain install leanprover/lean4:v4.35.0-rc3
lake update            # fetches Mathlib at the pinned revision
lake exe cache get     # downloads Mathlib's prebuilt .olean files (large); or `lake build Mathlib`
```

The checker does not call `lake`. It needs a folder `P` containing
`.lake/packages/*/.lake/build/lib/lean` (the result of the two commands above, with `P` the
repository root), and the `lean` executable:

```bash
export LANE4_LEAN=$(elan which lean)        # path of the toolchain's lean
export LANE4_MATHLIB_PROJECT=$PWD           # default; set it if Mathlib lives elsewhere
```

## Reproduction

Check one proof (builds `build/Lane4/*.olean` the first time, a few minutes):

```bash
python tools/check.py runs/rung4-test/net/c14
```

A pass prints `PASS  c14  kernel-checked` and the axioms of the final theorems, which must
be a subset of `propext`, `Classical.choice`, `Quot.sound`. Any `sorry`, error, time-out
(600 s), memory kill, banned token (`native_decide`, `axiom`, `sorry`, macros, ...) or other
axiom prints FAIL with the reason. Read `runs/rung4-test/net/c14/Spec.lean` and
`Final.lean` for the statement and `Lane4/RSeq.lean` for the definitions it rests on (the
trusted base is those files plus the Lean kernel).

Re-check everything (every case folder with a `Solution.lean`; see `VERIFY.md` for time):

```bash
python tools/recheck_all.py --out results/recheck.json          # rungs 2 to 4 (the original 67)
python tools/recheck_release.py                                  # every Lean file of rungs 2 to 6c: frameworks, all cases, standalone files, token audit
python tools/recheck_r678.py --set frameworks,kits,r6a           # rungs 6a to 8: frameworks, kit cases, rung-6a cases (add nets-r7,nets-r8 for the generated per-network files; hours, about 5 GB per Lean process)
python tools/build_net.py runs/r8-nets/A-u3-s140/Net.lean        # one per-network file of rung 8 (about 5 GB of memory)
python tools/recheck_ln15.py --set frameworks,kits                # rung 9-LN15: the LN framework and the ten kit cases (add --set nets for the 36 network file sets, about 4 hours, about 5 GB per Lean process)
python tools/build_ln_net.py f400                                 # one per-network file set of rung 9-LN15 (two files, about 400 s, about 5 GB)
```

The case-local `Spec.lean`/`Final.lean`/`Solution.lean` of rungs 5, 6b and 6c are checked the
same way (`python tools/check.py runs/rung5-test/net/c04`). The three superseded or failed
attempts kept on purpose (`runs/r5-kit/kA`, `runs/r5-kit/kC`, `runs/r6b/kColl`) are expected to FAIL.

Negative controls (these should FAIL or PASS as their folder names say):

```bash
for d in smoke/s*/; do python tools/check.py $d | head -1; done
```

Numeric checks (numpy, no Lean needed except for export, which re-runs the framework on the
passing solution): `tools/export_r4.py` then `tools/r4_checks.py` for rung 4; `tools/export_nets.py`
and `tools/r3_transformers.py`, `tools/float_probe.py` for the fragility tables;
`tools/collect*.py` assemble `results/*.json`. These scripts read `runs/` and write next to
it; run them on a copy. Their memory needs are not measured.

## What was changed for release

- Local absolute paths and the machine's user name were replaced by `<repo>`, `<home>` or `<path>`
  in `attempts/*.json` (the checker's recorded `lean_output`), `TASK.md` and the text
  results. Only text in the recorded Lean output changed, not any `pass` verdict.
- `tools/check.py` was edited: the two hard-coded machine paths became the environment
  variables above, a non-Windows kill path was added, and its module table
  was extended for the rung-5 and rational-mirror modules.
- Scheduling, memory-reservation and run-log references in `docs/` were generalised
  ("compute scheduler", "memory reservation", "run log (not released)"). The scientific
  content of the pre-registrations and results files is unchanged.
- Not included: agent transcripts, internal run logs, per-case scratch folders, generated
  `_Full.lean` / `_Export.lean` files, copies of framework files inside case folders (the
  checker uses `Lane4/`; the copies were byte-identical to it), service and scheduling
  scripts, trained-model files of the twin arms.
- Git history: this repository starts fresh. The pre-registration commit ids quoted in
  `docs/PREREG_R4.md` (5fdefc9, f905339), `RESULTS_R2.md` (6fdeeca) and rung 1 (6cd7ebd)
  refer to the authors' private development repository, where they are timestamped before
  the runs they precede; they cannot be checked from this copy. The frozen-file hash lists
  `docs/freeze_r4.sha256`, `freeze_r5.sha256`, `freeze_r6b.sha256`, `freeze_r6c.sha256` can be
  checked with `sha256sum -c`, **but only in part**: a file listed there matches only if it was
  not edited afterwards. Files edited for release (`tools/check.py`, which gained environment
  variables and a longer module table; scripts whose paths were scrubbed) no longer match,
  `Lane4/Collision.lean` was extended at rung 6c, and service scripts are not included.
  `results/freeze-check.txt` records the outcome (r4: 8 of 13 match; r5: 14 of 21; r6b: 8 of 9; r6c: 12 of 12).
- Added for release: `case.json` for the three witness cases, `tools/recheck_release.py`, and
  `scratch/` holding only the statement files and sanity scripts that the freeze lists name.

## Licence and citation

Code, Lean files and scripts: Apache-2.0 (`../LICENSE`). Proposed, for the owner to confirm: text and documents (this README, `docs/`) under CC-BY-4.0. Citation: see `../CITATION.cff` (owner handle `LeeMarshall1113`; display name, repository name and DOI are placeholders).
