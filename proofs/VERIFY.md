# VERIFY: what was re-run from a clean clone

Date: 2026-11-14. Machine: a shared Windows 11 desktop (31 GB RAM); one Lean process at a
time under a memory reservation of 6 to 7 GB (the whole job tree peaked at 5.0 to 5.6 GB of
commit; no single Lean process passed 3.2 GB working set). Lean `leanprover/lean4:v4.35.0-rc3`;
Mathlib `v4.35.0-rc3`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`.

Personal work. Views are my own.

## What "from a clean clone" means, and one caveat

Each re-check below was run in a fresh `git clone` of this repository (no `build/` directory,
no `_Full.lean` files). The framework `.olean` files are rebuilt from `Lane4/*.lean` by the
checker, in dependency order. **Caveat:** Mathlib itself was not re-downloaded or rebuilt. The
checker was pointed (`LANE4_MATHLIB_PROJECT`) at an existing local Mathlib build at the commit
above. A reader on a clean machine runs `lake update && lake exe cache get` first (README,
"Setup"); that step was not exercised here.

## Results

### 1. Everything, in the layout before the last tidy-up (3,628 s)

`python tools/recheck_release.py` (frameworks, every case folder with a `Solution.lean`, the
standalone files, and a token audit). Rows: `results/recheck-release-flat.json`, log
`results/recheck-release-flat.log`. **183 of 187 units passed; the 4 that did not are the
expected failures below, so nothing unexpected failed.**

| group | passed / checked | Lean seconds |
|---|---|---|
| framework files (`Basic`, `Seq`, `Robust`, `RSeq`, `RSoft`, `RSoftKit`, `Bin32`, `RSoftAll`, `QRSeq`; `Collision`, `TokenBlind`, `Conjectures` compiled as statement files) | 12 / 12 | 149 |
| rung 1 (background) `runs/rung1-test` | 40 / 40 | 990 |
| rung 2 `runs/rung2-test` (10 net + 10 control) and `rung2-dev` | 20 / 20 and 4 / 4 | 241 and 48 |
| rung 3 `runs/rung3-test` (25 case folders) and `rung3-dev` | 25 / 25 and 4 / 4 | 694 and 125 |
| rung 4 `runs/rung4-test` (11 net + 12 control) and `rung4-dev` | 23 / 23 and 4 / 4 | 359 and 66 |
| rung 5 `runs/rung5-test` (12 net + 12 control) and `rung5-dev` | 24 / 24 and 3 / 4 | 472 and 107 |
| rung-5 kit `runs/r5-kit` (8 folders) | 6 / 8 | 122 |
| rung 6b `runs/r6b` (5 folders) | 4 / 5 | 63 |
| rung 6c `runs/r6c` (5 folders) | 5 / 5 | 63 |
| witnesses `runs/witness` (3) | 3 / 3 | 48 |
| standalone files (3 corollary files `r6b/m*/_Corollary.lean`, `r6c/members`, `r6c/final`, `r6c/example`) | 6 / 6 | 74 |

The rung-4 net arm has 12 cases but 11 have a `Solution.lean`: `i03` has none (the agent
crashed before submitting; counted as a fail in the report).

**Expected failures (kept on purpose, 4):**
- `runs/r5-kit/kA` and `runs/r5-kit/kC`: early kit lemmas whose recorded attempts passed
  against an earlier version of `Lane4/RSoft.lean`; against the current file they fail
  (superseded by `kA2` and `kC2`).
- `runs/r6b/kColl`: the failed first attempt at the collision bound (the registered statement
  was false, see `docs/PREREG_R6.md` amendment 1); superseded by `kColl2`.
- `runs/rung5-dev/net/i13`: a development case whose agent failed after 7 submissions
  (reported in `docs/RESULTS_R5.md`).

### 2. Final layout, sample plus bridge files (clean clone of the final tree)

After duplicate framework copies and per-case scratch folders were removed, a fresh clone was
re-checked with `python tools/recheck_release.py --match <31 cases>`: **49 units, 45 passed,
the same 4 expected failures** (788 s). The sample: all 12 framework files, the 6 standalone
files, rung 1 `p019`; rung 2 net and control `a00`, `p05`, `s01`; rung 3 `p001`; rung 4 `c14`,
`i09`; rung 5 `c04` (net and control) and `i02`; `kR`, `kConj`, `kQ`, `kA2`; `kColl2`, `m05`;
`iNet`, `cBounds`; the three witnesses; and the four expected-failure cases. Rows:
`results/recheck-sample-final-layout-v2.json`.

The bridge files of `reading/` (unit 3 there) were re-checked in the same clone with
`python reading/bridge/recheck_bridge.py`: **27 of 27** (the two framework files `IBP.lean`,
`Region.lean`, 16 stage-1 nets at 6 inputs, 8 float-weight nets, one 8-input net), 3,766 s
including one more file that did **not** finish: `R_MAJ10_w32_s104_maj.lean` (a 10-input
majority region certificate) hit the script's 1,500 s limit and is recorded as a failure
(`results/recheck-bridge.json`, `results/recheck-final-layout-and-bridge.log`). That matches the
study's own report that the first full region certificate at 10 inputs hit its stop. It is not
in the default set of the script.

The RNN unit (`reading/` unit 4) was re-checked in a further clean clone of the tree after
this version's changes (2026-11-15; one Lean process at a time, memory reservation 7 GB, whole
job tree peaked at 4.3 GB of commit, no single Lean process above 2.2 GB working set):
`python reading/bridge/recheck_bridge.py --set rnn,rnnpipe`: **14 of 14 passed in 202 s**: the
four framework files (`IBP`, `Region`, `RNN`, `RNNClust`), the **nine test certificates**
(`RNNC_L1_ORD_d8_s100/s106/s107`, `RNNC_L1_SAT_d8_s106`, `RNNC_L3_ORD_d8_s100`,
`RNNC_L3_SAT_d8_s103/s104/s105/s107`; 13.5 to 16.3 s each), and the pipeline-check net
`RNNC_L3_ORD_d4_s2` (outside dev and test). Every certificate's axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`. Rows: `results/recheck-rnn.json`. **Totals now: the main recheck 183 of 187 (4 expected failures), the bridge files 27 of 27, the RNN unit 14 of 14 (9 test certificates, the pipeline-check net and 4 framework files).** The four expected failures above are unchanged. No `native_decide`,
`ofReduceBool`, `sorry` or `axiom` in any of the RNN files.

### 3. Axioms and `native_decide`

Every passing check reports the final theorems' axioms as a subset of `propext`,
`Classical.choice`, `Quot.sound` (the union over all passing units is exactly that set). The
checker refuses any other axiom. Token audit over the 1,189 Lean files under `Lane4/` and
`runs/` (comments stripped, generated `_Full.lean` excluded): `native_decide` 0,
`ofReduceBool` 0, `sorry` 0, `axiom` 0, both in the submitted and final files and in every
recorded attempt. The bridge nets use `decide +kernel` (kernel reduction), not
`native_decide`.

### 4. Negative controls (from the earlier check; not re-run on 2026-11-14)

`smoke/` (rung-0/1-era cases through the same checker), observed: `s1_xor_simp` PASS,
`s1b_xor_decide` FAIL (Lean errors), `s2_xor_wrong` FAIL (Lean errors), `s3_sorry` FAIL
(banned token `sorry`), `s4_native` FAIL (banned token `native_decide`), `s5_max_real` PASS,
`s6_prog` PASS, `s7_prog_cheat` FAIL (program part uses `max`), `s8_twin` PASS. Which outcome
each case was designed to give is not written down in the case folders; the observed ones are
listed as they are. The earlier recheck of rungs 2 to 4 (67 of 67 passed, 1,278 s) is
`results/recheck-flat-layout.json`.

### 5. Frozen-file hashes

`results/freeze-check.txt`: of the files listed in the freeze lists, `docs/freeze_r6c.sha256`
matches 12 of 12, `freeze_r6b.sha256` 8 of 9 (`Lane4/Collision.lean` was extended at rung 6c),
`freeze_r5.sha256` 14 of 21 and `freeze_r4.sha256` 8 of 13; the rest were edited for release
(`tools/check.py`, scrubbed scripts) or are service scripts that are not included.

### 6. Rungs 6a, 7, 8 and the mechanism rows (version 0.4; run 2026-11-21)

Same machine and toolchain as above (Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`, Mathlib not rebuilt). Run
from a clean clone of the draft branch, one Lean process at a time, with `tools/recheck_r678.py`
(`--set frameworks,kits,r6a,nets-r7,nets-r8`, then `nets-mech`, then `frameworks,kit-mech,attn`, then
`nets-mech --match ctl`). A per-network file passes when Lean exits 0 with no error and no `sorry`,
every `#print axioms` is within `propext`, `Classical.choice`, `Quot.sound`, it proves `accept` or
`reject`, **and that verdict equals the one recorded in the folder's log**, and its commit stays
at or under 6 GB (the limit of `PREREG_R8.md` Amendment 1). Rows and logs are in `results/`.

| Run | Rows | Passed | Notes |
|---|---|---|---|
| Frameworks, kit cases, rung 6a cases, rung 7 and 8 per-network files and controls (`recheck-r678.json`, `.log`; 6,479 s) | 179 | **178** | 1 framework build, 47 kit and rung-6a cases, 131 per-network files: 48 accept, 82 reject, 1 not a net file (below). Largest file 648 s, 5.45 GB commit. |
| Mechanism row (b) (`recheck-r678-mech.json`; 2,664 s) | 23 | 23 | framework build plus 22 files (21 accept; fresh seed 153 proves `reject`, as in rung 8). |
| Mechanism row (a) (`recheck-r678-attn.json`; 2,371 s) | 21 | 21 | framework build plus 20 files, each carries the row (b) theorems as well; largest 591 s, 4.89 GB. |
| Row (a) kit case and the swapped-embedding control (`recheck-r678-attn-ctl.log`, `recheck-r678-ctl.json`) | 2 | 2 | kit case `runs/mech-kit/ma` (axioms `propext`, `Classical.choice`, `Quot.sound`); the control file proves `accept` (kernel-checked, no trained-network theorems). |

**The one non-pass:** `runs/r8-nets/probe116/Net.lean`. It is a development probe on a tuning-set
network, containing only the first six case theorems; it compiles cleanly (exit 0, no error, no
`sorry`, 29 s) but states no `accept` or `reject` theorem, so the script's rule marks it. It is kept
so that nothing is quietly removed; no result in `RESULTS_R8.md` rests on it.

**A first attempt that did not count.** The first run of the row (a) files (`recheck-r678-attn-run1.json`)
shows 20 failures: every file compiled and proved its theorems with the standard axioms, but the
script compared the file's verdict with the wrong recorded one (a bug in `tools/recheck_r678.py`, fixed
afterwards). The table above is the rerun with the fixed script. An earlier launch also stopped within
a minute for a missing dependency in the module table of `tools/check.py` (fixed; nothing else ran).

**Token audit** over the 522 Lean files of these rungs: `native_decide` 0, `ofReduceBool` 0, `sorry` 0, `axiom` 0
in the final files and in every recorded attempt.

**Freeze lists** (`results/freeze-check-r678.txt`): the rung-8 checker's Lean files match their listed
hashes; many Python tools differ because the release copies were scrubbed of internal wording or
because they are shared files edited later.

**What this does not show.** Not re-run: the Python mirrors and numeric checks, the training of the
networks, the extraction step (only its generated Lean files are checked), the agent runs. Mathlib was not
rebuilt. No external checker (nanoda, lean4lean, `lake comparator`) has been run on these files; see
`writeup/LEAN_VERSION.md` for the version check and why that is the natural next
step. The toolchain is a release candidate.

### 7. Rung 9-LN15 (LayerNorm; version 0.5; run 2026-11-22)

Same toolchain (Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`, not rebuilt), a copy of the draft tree, one Lean
process at a time, with `tools/recheck_ln15.py`. A network's file set passes when every file compiles (exit 0, no
error, no `sorry`, within 900 s and 6 GB commit), every `#print axioms` is within `propext`, `Classical.choice`,
`Quot.sound`, the kernel's decision (accept or reject) equals the one recorded in the folder's `kernel.json`, and an
accepted network proves all five theorems (`accept`, `skeleton_ok`, `binary32`, `trained_exact_all_lengths`,
`trained_binary32`). Kit cases go through `tools/check.py`. Rows and logs are in `results/`.

| Run | Rows | Passed | Notes |
|---|---|---|---|
| Run 1: framework `LNAll` (20 LN modules), ten kit cases (`runs/r9ln15-kit`), 36 network file sets (`recheck-ln15.json`, `.log`; 15,227 s) | 47 | **44** | 1 framework build, 10 kit cases (10 pass), 36 file sets: 19 fresh (13 accept, 6 reject), 11 tuning (9 accept, 2 reject), 6 controls (6 reject). **The 3 non-passes are timeouts, below.** |
| Run 2: the three non-passes of run 1, with a per-file limit of 1500 s (`recheck-ln15-rerun.json`, `.log`; 7,716 s) | 3 | **3** | `f402`, `f409`, `t113`: all five theorems, standard axioms, four files each, at most 5.07 GB commit. |

**The three non-passes of run 1 were timeouts, not wrong results.** The three networks are the 780-case ones
(fresh seeds 402 and 409, tuning seed 113). In run 1 `f402` file C took 904.1 s, `f409` file A 900.6 s and
`t113` file A 900.7 s, against the registered 900 s per file (`PREREG_R9LN15.md`, rule KK); each file finished with
exit 0 and no error, and the runner stopped the network at that file, so those three have no verdict in run 1. They
were re-run with `--limit 1500`. **The registered 900 s per-file limit was not met on this machine for two of
them in run 2**: `f402` files took 961, 1,014, 968 and 14 s, `f409` 911, 873, 908 and 11 s; `t113` stayed under it
(708, 667, 668, 11 s). The lab's own runs of the same files took 674, 666, 667 and 11 s (`f402`); this machine was
shared with other jobs and was slower. Read the counts as "all 36 file sets pass at 1500 s per file; 33 of 36 passed
at the registered 900 s on the first run on this machine". The lab's own runs (`kernel.json` in each folder) recorded
every file within 900 s, so rule KK is met in those runs and not reproduced to the second here. Memory stayed at or under 5.07 GB
commit throughout.

**Largest files that passed in run 1:** 642 s and 5.0 GB (a 155-case network's file); the 155-case networks take 380
to 545 s here in two files.

**Token audit** over the 158 new Lean files (the 20 LN modules, the kit and every network file; `Final`/`Solution`
and attempt files counted separately): `native_decide` 0, `ofReduceBool` 0, `sorry` 0, `axiom` 0 in the final files and
in every recorded attempt.

**Freeze lists** (`results/freeze-check-ln15.txt`): all 20 `Lane4/LN*.lean` modules match the hashes listed before any
fresh seed was trained; the Python tools and documents that differ were changed by the release scrub or are shared
tools edited later.

**What this does not show.** Not re-run: the Python mirror, the generator, the training and screen of the networks
and the sampled numeric checks (`tools/ln15_checks.py`); the pre-check files of the tuning stage (`A-n1-s*`, `h-A-n1-s*`) and the text-model experiment (E3) are not in this release. The kit cases' attempt records are verdicts, not transcripts. Mathlib was
not rebuilt, no external checker has been run on these files (see `writeup/LEAN_VERSION.md`), and the toolchain is a
release candidate. The model, its relative rounding form and the square-root and exponential assumptions are part of
the statement (`Lane4/LNNet.lean`) and the kernel does not check that they describe IEEE binary32.

### 8. Rung 9-LN-M (LayerNorm, second task; version 0.6; run 2026-11-22 to 2026-11-23)

Same toolchain (Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`, not rebuilt), a copy of the draft tree, one Lean
process at a time, `tools/recheck_ln15.py --set frameworks,nets --match "^(m8|mc_)"` (the rules of Section 7: every
file compiles with exit 0, no error, no `sorry`, within 900 s and 6 GB commit; every `#print axioms` within `propext`,
`Classical.choice`, `Quot.sound`; the kernel's decision equals the one recorded in the folder's `kernel.json`; an
accepted network proves all five theorems). Rows and log: `results/recheck-lnm.json`, `results/recheck-lnm.log`
(12,724 s in all).

| Rows | Passed | Notes |
|---|---|---|
| 28 | **28** | 1 framework build (`LNAll`, unchanged from Section 7), 20 fresh network file sets (19 accept, 1 reject: seed 805), 7 control file sets (all 7 reject). |

**The registered 900 s per-file limit was met on this machine for every file.** The largest file took 759 s (`m803`,
file A); the two 780-case networks (803, 816) used all four allowed files (2,280 s and 2,217 s in all); the 155-case
networks took 418 to 470 s in two files and the 30-case network (811) 106 s; at most 5.06 GB commit. (In rung 9-LN15's
re-check, Section 7, three files exceeded 900 s on this shared machine; none did here.) Two earlier attempts of this
re-check stopped within seconds because the Mathlib search path was not set, before any Lean proof ran; they are not
counted.

**Token audit** over all new Lean files in the tree (208 files: the 20 LN modules, the rung 9-LN15 kit and networks, and
the 27 new network file sets): `native_decide` 0, `ofReduceBool` 0, `sorry` 0, `axiom` 0.

**What this does not show.** Not re-run: the training and screen of the networks, the Python mirror, the generator
(`tools/r9m.py`) and the numeric checks (`tools/ln15_checks.py`). The hashes in `docs/freeze_r9m.sha256` are of the
original files and do not match the scrubbed copies in this release; the 20 `Lane4/LN*.lean` modules are unchanged
from version 0.5. No external checker has been run on these files.

## What this does not show

- It re-checks that the recorded solutions are accepted by the Lean kernel against the
  recorded statements. It does not check that the statements say what the report says; that is
  for a reader (`README.md`, "Reproduction"; `REPORT.md`, Section 8).
- Times here are shorter than those in the original attempt logs (the logs were taken on a
  busier machine).
- The numeric scripts (`tools/r4_checks.py`, `r5_checks.py`, `r3_2x2_v2.py` and so on), the
  export step, the agent runs and the `reading/` Python scripts were not re-run.
- `runs/*-dev` of rungs 2 to 5 were re-checked only in the flat run; rungs 6a to 8 and the mechanism rows are in Section 6.
- Not tested on Linux or macOS; the memory guard in `tools/check.py` works on Windows only.
- Mathlib was not rebuilt (see the caveat above).
