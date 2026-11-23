# Weight-space lab

Personal work. Views are my own.

Maintainer: `LeeMarshall1113`. First public version: v0.2, 2026-11-15.

This is a living, correctable lab notebook, not a finished publication. **Please try to
break it** (see `CONTRIBUTING.md`). Corrections are logged in `CHANGELOG.md` with credit,
and claims that do not survive are downgraded in the table below, not quietly edited.

A lab-style repository of experiments on **LLMs writing, reading and editing neural-network
weights**, with pre-registrations, negative results kept, and where possible machine-checked
proofs. Each result lives in its own folder with its own README, pre-registration and
instructions to check it. `proofs/` and `reading/` are included; other results are listed in the index as
"not yet included". The full technical report is
`proofs/REPORT.md` (a living document with a claims table, a changelog and a "how to
correct us" section).

## What this is

- **Strongest result.** An LLM wrote the weights of small transformers *and* Lean proofs, checked by the Lean kernel, that each one is correct at every input length for every weight change within a stated range (for example 0.5% relative; exact arithmetic at every length in one rung, a rounding model up to 65,535 tokens in another). Eleven of twelve and twelve of twelve in the two main rungs; counting tasks are excluded.
- **Impossibility result.** For parity networks and every "token-blind" network, the correct radius shrinks like 1/n, so no positive radius works at every length. The effect is known (Hahn and Rofin); here it is machine-checked with explicit constants, for narrow classes only.
- **Latest (rung 9-LN-M, LayerNorm, a prospective rung on a second task).** Limits first: the Lean statement of the target is the task automaton run on the prefix (so it equals the task's own definition by `rfl`), not a closed form, and a reader checks one fold; the task is local, like the first task (windows of at most four keys), so this says nothing about long-range tasks; the ball is only the distance to the rounding grid, with no margin beyond rounding; five tokens, one block, width 8, the study's own recipe; the exponential and the square root are assumed in the binary32 statement; 19 of 20, not 20 of 20; the registration's first line carries a wrong time (the registration was committed before any network of the task was trained, and the commit time, 1:50 pm EST, is the true one; the commit log is private, so the order is not independently verifiable). Result: the rung 9-LN15 model, checker, soundness theorem and proofs, frozen and unchanged, were run on a new task (the output is the larger of the digits of the current and the previous token) with everything registered before any network of the task was trained: **19 of 20 fresh one-block width-8 softmax networks with LayerNorm (seeds 800 to 819; all 20 pass the screen) are proved, by the same soundness theorem and a kernel-checked certificate each, to compute the task at every position of every input length, for every weight setting within 2^-15 of the rounded weights, in a binary32 rounding model; the one other network is rejected by the kernel; 7 of 7 controls were rejected; the kernel and the mirror agree on all 27 objects.** This rung is prospective; rung 9-LN15, below, remains post hoc. Seen beforehand: rung 9-LN15 itself and a probe of a sibling task (9 of 10 accepted by the Python mirror, no kernel run), which is why a pass was expected. Read caveat 13 below.
- **Before that (rung 9-LN15, LayerNorm; a post-hoc rung).** One soundness theorem for a checker that bounds three LayerNorms, then a generated Lean proof per gradient-trained network: **13 of 19 screened fresh one-block width-8 softmax networks with LayerNorm (20 trained) are proved, by one soundness theorem and a kernel-checked certificate each, to compute a local task at every position of every input length, for every weight setting within 2^-15 of the rounded weights, in a binary32 rounding model; 7 of 7 controls were rejected; six screened networks compute the task and are not proved.** The registered rung at 2^-14 failed its kill rule (5 of 18 tuning networks accepted; the line was 6) and is published as a failure; the radius 2^-15, the enclosure design and the arithmetic were chosen afterwards on the same tuning networks. Read caveat 12 below.
- **Before that again (rungs 6a to 8).** One soundness theorem for a checker, then a generated Lean proof per gradient-trained network: 19 of 20 fresh one-block width-8 softmax networks accepted at an additive weight radius of 2^-14, for a local task. The radius was chosen on a tuning set, the checker was fitted to earlier networks of the same recipe, and a kernel-checked all-length theorem for a trained threshold RNN (teal-sea) came earlier; read caveat 11 below.
- **Boundary.** For gradient-trained networks the results mark where methods stop: the one LLM tried read trained transformers from weights at 0 of 20, and kernel-checked weight-ball certificates for small trained ReLU nets and RNNs reach only small input spaces or a minority of networks.
- **Read the [weaknesses](#known-weaknesses-read-before-citing) before citing anything here.**

Check one proof yourself (after the setup in `proofs/README.md`):

```bash
cd proofs && lake update && lake exe cache get
export LANE4_LEAN=$(elan which lean) LANE4_MATHLIB_PROJECT=$PWD
python tools/check.py runs/rung4-test/net/c14
```

## Index of results

Status words: **confirmed** (the pre-registered claim was met and the Lean files were
re-checked from this folder), **measured** (a numeric screen, not a proof), **negative**
(the pre-registered test was not met or a kill criterion triggered), **boundary** (a result
that marks where a method stops), **in progress**. "Not yet included" rows say what the
lab's own notes report; they have not been independently re-checked.

| Claim | Status | Where to look | How to check |
|---|---|---|---|
| 11 of 12 LLM-written hard-attention transformers kernel-checked correct at every input length for every relative weight change within 0.5%, under a rounding model up to 65,535 tokens (non-counting tasks only; a plain verified program does the same tasks with proofs about a tenth as long) | confirmed | `proofs/` (rung 4), `proofs/docs/RESULTS_R4.md` | `python tools/check.py runs/rung4-test/net/c14` inside `proofs/`; or `tools/recheck_release.py`. See `proofs/VERIFY.md` |
| 12 of 12 LLM-written softmax transformers kernel-checked within 1/4 of the target at every length for every relative weight change within 1/200, with exact arithmetic at every length and a binary32 model up to 65,535 tokens (non-counting tasks only; the kit carries the float analysis; one pre-registered numeric check failed) | confirmed | `proofs/` (rung 5), `proofs/docs/RESULTS_R5.md` | `runs/rung5-test/net/*`, same checker |
| 12 of 12 LLM-written ReLU networks proved within tolerance of an exact spec for every weight and bias within 1/1000 (absolute) | confirmed | `proofs/` (rung 3), `proofs/docs/RESULTS_R3.md` | same checker, `runs/rung3-test/` |
| 10 of 10 LLM-written hard-attention transformers proved correct at every input length, exact arithmetic, written weights only | confirmed | `proofs/` (rung 2), `proofs/docs/RESULTS_R2.md` | same checker, `runs/rung2-test/` |
| Perturbation 2x2 (additive versus relative; rung 2 versus rung 4): additive 1/1000 breaks all ten rung-2 networks and, at length 1,000, all eleven rung-4 networks; no break found under relative noise inside the rung-4 ball. The earlier "fragile versus robust" framing is withdrawn | measured (finite searches); three witnesses kernel-checked | `proofs/REPORT.md` (Section 3), `proofs/results/r3-2x2-v2.json`, `proofs/runs/witness/` | `proofs/tools/r3_2x2_v2.py`; the witnesses through the same checker |
| For three proved parity networks (and every "token-blind" network, including two sort networks) no relative ball of radius 1/(2L-1) or more is correct up to length L, so no positive radius is correct at every length; the general phenomenon is known | confirmed (narrow classes) | `proofs/` (rungs 6b, 6c), `proofs/docs/RESULTS_R6B.md`, `RESULTS_R6C.md` | `runs/r6b/`, `runs/r6c/` |
| Three open statements (no length-independent ball for parity; none absolute for a non-counting task) | conjecture (statements type-check; nothing proved) | `proofs/Lane4/Conjectures.lean` | `proofs/runs/r5-kit/kConj` |
| Compiled versus trained transformers: an LLM reads small compiled (Tracr) transformers from weights alone at 20/20 functional, trained ones at 0/20 (0/41 when trained for discreteness) | negative on trained nets; compiled is the easy case | `reading/` unit 1 | not re-run; data in `reading/results/` |
| A decay curve from compiled networks toward trained-like weights could not be built under the pre-registered rule (corrected: the first write-up overclaimed) | negative (stopped by kill rule) | `reading/` unit 2 | not re-run |
| One checker with one soundness theorem, then a generated Lean file per gradient-trained network, standard softmax attention (one block, width 8, no gate, no LayerNorm, fixed position slope): 19 of 20 fresh seeds accepted for every additive weight change of at most 2^-14 around the rounded trained weights and for the task at every length (exact arithmetic; binary32 model up to 65,535 tokens); eight controls rejected; one network rejected. The radius was chosen on the tuning set; local task; nearest prior work is a trained threshold RNN (teal-sea) | confirmed (for this recipe and task; caveats 11) | `proofs/` (rung 8), `proofs/docs/RESULTS_R8.md`, `proofs/writeup/NOVELTY_R8.md` | `python tools/build_net.py runs/r8-nets/A-u3-s140/Net.lean` inside `proofs/`; `tools/recheck_r678.py`. See `proofs/VERIFY.md` |
| Mechanism rows for the 19 accepted rung 8 networks: (b) a finder never given the task reads a 5-state, 25-row program off the weights and the kernel checks the network equals it at every length over the same ball, and the program equals the task (the outcome was fixed in advance, and the program is trivial because the task is); (a) each head puts all but 2^-21 of its softmax weight on a short window of its latest positions (head 0: the previous position alone; head 1's weight can be shared inside its window). A control with swapped embedding rows returns a different program, on a network we altered ourselves | confirmed (the Lean files re-checked; see the caveats) | `proofs/` (`runs/mech`), `proofs/docs/RESULTS_MECH.md`, `proofs/REPORT.md` Section 6.11 | `python tools/recheck_r678.py --set nets-mech` and `--set frameworks,kit-mech,attn` inside `proofs/`. See `proofs/VERIFY.md` |
| Rung 9-LN15 (LayerNorm; a NEW post-hoc rung, after the registered rung at 2^-14 failed its kill rule). One soundness theorem `Lane4.LNC.SoundLN` for a checker of a one-block width-8 softmax transformer with three LayerNorms (pre-LN places, final LayerNorm), then a generated Lean file set per gradient-trained network: 13 of 19 screened fresh networks (20 trained, seeds 400 to 419) proved, for every additive weight change of at most 2^-15 around the weights rounded to the 2^-14 grid, to be within 1/4 of the task target at every position and every input length (exact arithmetic) and up to 65,535 tokens (binary32 model; exponential and square root assumed accurate); bar 3 of 3 (needed 2); 7 of 7 controls rejected; six screened networks compute the task and are not proved. The radius, enclosure design, symbol layout and arithmetic were chosen after the 2^-14 failure, on the same 18 tuning networks | confirmed for this recipe and task (post-hoc rung; read caveat 12) | `proofs/` (`Lane4/LN*.lean`, `runs/r9ln15-nets`), `proofs/docs/RESULTS_R9LN15.md`, `proofs/docs/RESULTS_R9LN.md`, `proofs/REPORT.md` Sections 6.12 and 6.13 | `python tools/recheck_ln15.py --set frameworks,kits` and `--set nets` inside `proofs/`. See `proofs/VERIFY.md` |
| Rung 9-LN-M (LayerNorm; a PROSPECTIVE rung on a second task, frozen checker and theorem). Limits first: the Lean statement of the target is the task automaton run on the prefix (so it equals the task's own definition by `rfl`), not a closed form, and a reader checks one fold; the task is local, like the first task (windows of at most four keys), so this says nothing about long-range tasks; the ball is only the distance to the rounding grid, with no margin beyond rounding; five tokens, one block, width 8, the study's own recipe; the exponential and the square root are assumed in the binary32 statement; 19 of 20, not 20 of 20; the registration's first line carries a wrong time (the registration was committed before any network of the task was trained, and the commit time, 1:50 pm EST, is the true one; the commit log is private, so the order is not independently verifiable). The frozen rung 9-LN15 theorem `Lane4.LNC.SoundLN` and its checker, unchanged, on the task "the output is the larger of the digits of the current and the previous token": 19 of 20 fresh networks (seeds 800 to 819, all 20 screened) proved, for every additive weight change of at most 2^-15 around the weights rounded to the 2^-14 grid, to be within 1/4 of the task target at every position and every input length (exact arithmetic) and up to 65,535 tokens (binary32 model; exponential and square root assumed accurate); bar 3 of 3 (needed 2); network 805 rejected by the kernel; 7 of 7 controls rejected; kernel equals mirror on all 27 objects. | confirmed for this recipe and two local tasks (prospective on the second; read caveat 13) | `proofs/` (`runs/r9ln15-nets/m8*`, `runs/r9m-*`), `proofs/docs/PREREG_R9M.md`, `proofs/docs/RESULTS_R9M.md`, `proofs/REPORT.md` Section 6.14 | `python tools/recheck_ln15.py --set nets --match \"^(m8|mc_)\"` inside `proofs/`. See `proofs/VERIFY.md` Section 8 |
| Same method on a gated block (rung 7), trained networks: 4 of 9 screened reserve networks accepted (4 of 20 seeds); 0 of 18 on the standard ungated architecture | confirmed on the gated block; negative on the standard one | `proofs/` (rung 7), `proofs/docs/RESULTS_R7.md` | `tools/recheck_r678.py --set nets-r7` |
| 12 of 12 LLM-written gated softmax transformers (a non-standard gate) kernel-checked within 1/4 for every additive weight change of at most 1/1000, every length (binary32 model up to 65,535 tokens); the kit was amended once | confirmed (amended kit; non-standard gate) | `proofs/` (rung 6a), `proofs/docs/RESULTS_R6A.md` | `tools/recheck_r678.py --set r6a` |
| Kernel-checked weight-ball certificates (1/1000) for tiny trained ReLU networks: 8/8 and 8/8 at 6 inputs, near-tight, on float weights too; the certified fraction falls to 0/8 by 12 inputs and cost tracks 2^n | boundary (known method; finite inputs only) | `reading/` unit 3 | `python reading/bridge/recheck_bridge.py` |
| Kernel-checked all-lengths weight-ball certificates (1/1000) for ordinarily trained clipped-ReLU RNNs: 9 certificates; registered pass bar **not met** (parity 3/8 ordinary and 1/8 with the penalty, mod-3 0/8 in both arms, Tomita 4 1/8 and 4/8, p = 0.14); the nets use 5 to 20 state clusters, not the 2 to 4 of the minimal automaton; the one confirmed break is at ratio 1.21 and the other 8 are not shown tight | boundary (known method; the pass bar was not met) | `reading/` unit 4, `reading/docs/PREREG_RNN.md` | `python reading/bridge/recheck_bridge.py --set rnn` |
| Injecting a new skill into a pretrained network without gradients | mixed per lab notes: positive on small nets, not shown at the prose rung; not yet included | folder not yet included | |
| Detecting planted behaviours from weights | negative per lab notes (kill criterion met for a zero-shot doctor); not yet included | folder not yet included | |
| Self-improvement levers (data, recipe, weights) | in progress; not yet included | folder not yet included | |
| A typed-decision method: reproduction and gate | negative per lab notes (gate not met, shelved); not yet included | folder not yet included | |
| The doctor harness: an agent loop that edits weights under a forward-pass budget | tool; not yet included | folder not yet included | |

## Known weaknesses (read before citing)

These are the weak points we know of; each is repeated, with detail, in `proofs/REPORT.md`
("Known weaknesses") and `proofs/README.md` ("Limits"). If you find another, that is exactly
what we want to hear.

1. **The earlier "fragile versus robust" framing is withdrawn.** An additive perturbation
   (zeros included) and a relative one (zeros fixed) are different tests; a 2x2 measurement
   showed the contrast was not like-for-like. What remains are finite search outcomes
   ("a break was found" / "no break found"), with three individual Lean-checked witnesses.
2. **The theorems are about tailored models.** Hand-written weights, width at most 15 (hard
   attention, rungs 2 to 4) or a softmax model (rung 5); the rounding models are not full
   IEEE arithmetic (rung 4: no overflow, underflow or subnormals; rung 5: an underflow term
   and a range bound, with an assumed accuracy for the float exponential); lengths up to
   65,535 tokens for the rounded statements.
3. **Counting tasks are excluded** from the all-length relative-ball theorems (parity,
   Dyck, sort). For the three written parity networks, and for every "token-blind" network,
   the radius provably shrinks like 1/n (rungs 6b and 6c). That phenomenon is known
   (Hahn and Rofin), the classes are narrow, and the conjecture for the whole architecture
   is open (type-checked statements only).
4. **No practical advantage over a plain verified program:** the control arm solved every
   task with proofs a tenth to a twentieth as long. The arms prove different statements.
5. **Tasks were chosen knowing which mechanism works**, with a lemma kit and a worked
   example supplied; the rung-5 kit carries the softmax and float analysis. The result is
   about proof automation as much as about transformers.
6. **A pre-registered rung-5 check failed** (bit-identity of two float32 implementations on
   one of 12 networks); it is reported as failed, not replaced.
7. **The statements are only as good as `Spec.lean`, `Final.lean` and the framework files**,
   which we wrote; the kernel checks proofs against them, not against intent.
8. **Novelty is a search over abstracts**, not a literature review; "not found" is weaker
   than "does not exist". Pre-registration commits are in a private repository and are not
   independently verifiable.
9. **Small samples:** 11 of 12, 12 of 12, 10 of 10; one model family (the exact version
   string was not recorded); the one rung-4 miss is an agent crash, counted as a failure.
10. **`reading/` units are negatives and boundaries.** Units 1 and 2 are from n = 20 runs
    with one agent model, not re-run for this release; units 3 and 4 are certificates, with
    their Lean files re-checked. Unit 4's registered pass bar was **not** met (3/8, 0/8, 1/8).
11. **Rungs 6a to 8 have their own caveats** (`proofs/REPORT.md`, "Caveats for rungs 6a, 7 and 8"): the rung-8 radius 2^-14 was chosen on the tuning set to make the task pass and is about 16 times smaller than rung 7's; the checker was fitted to 18 to 20 earlier networks of the same recipe; the task depends on the last two tokens only; rung 7 gives 4 of 9 and 0 of 18 on the standard architecture; rung 6a uses a non-standard gate and an amended kit; a kernel-checked all-length theorem for a trained network (a threshold RNN, teal-sea) existed before ours.
12. **Rung 9-LN15 (LayerNorm) is a post-hoc rung, and its count is smaller than it looks** (`proofs/REPORT.md`, Sections 6.12 and 6.13): the registered rung at 2^-14 failed its kill rule (5 of 18 tuning networks accepted, the line was 6) and is published as a failure with its own documents; the radius 2^-15, the enclosure design, the symbol layout and the fixed-point arithmetic were chosen afterwards on the same 18 tuning networks, with five checker variants tried, so the tuning counts are fitted and are not evidence; only the fresh-seed count is a result, and it is 13 of 19, not 19 of 19: six screened networks compute the task and are not proved; 2^-15 is the smallest ball around the rounded weights that contains the trained network, so there is no margin beyond rounding to the 2^-14 grid; the exponential and the square root are assumed to meet their models; five tokens, one block, width 8, a local task; an enclosure test on a small trained two-block text model failed by a wide margin, so the method did not carry to real text; the two 780-case networks used all four allowed files; on the release re-check machine, three 780-case file sets (two of the 13 proved fresh networks and one tuning network) each had one file exceed the registered 900 s limit by under 5 s in the first run (the machine was shared); on a second run two of them again exceeded 900 s per file (up to 1,014 s) and all three passed at a 1500 s limit, while the lab's own runs were inside 900 s; a missing charge for the rounding of stored biases was found and fixed before any proof work (a slip in a guard the proof does not use would not be caught by the kernel); no new literature search was made for this rung.
13. **Rung 9-LN-M (LayerNorm, second task) is prospective, and limited** (`proofs/REPORT.md`, Section 6.14): the checker, theorem and proofs were frozen by hash and not changed; the task, seeds, bar, kill rules and controls were registered before any network of the task was trained. Seen beforehand: rung 9-LN15 itself (post hoc, caveat 12) and a probe of a sibling task ("equals the previous token", 10 networks, 9 of 10 accepted by the mirror, no kernel run), which is why a pass was expected. The limits: the Lean target is the task automaton run on the prefix, so `task.target = target` holds by `rfl` and a reader checks one fold, not a closed form; the task is local like the first (the checker's windows hold at most four keys), so nothing is shown for long-range tasks; the ball is only the distance to the rounding grid (no margin beyond rounding); toy scale (five tokens, one block, width 8, the study's own recipe); the exponential and the square root are assumed; 19 of 20, not 20 of 20 (network 805 computes the task and the checker's bound is too wide at one case); the first line of the registration states a wrong time (the commit time of 1:50 pm EST is the true one; the original file is frozen and the copy here carries a note); the order of registration and training is not independently verifiable (the commit log is private); one run-control script in the freeze list was edited and reverted within the minute before any job of the rung ran with it; Lean re-check on the release machine: 28 of 28 rows pass (framework, 20 fresh, 7 controls), every file within the registered 900 s limit (largest 759 s); `proofs/VERIFY.md` Section 8.

## Repository layout

```
proofs/            Lean proofs, checker, pools, pre-registrations, per-case results, REPORT.md   (included)
reading/           four finished units on reading and certifying networks from their weights (Lean files included)   (included)
LICENSE            Apache-2.0 (code, Lean files, scripts)
NOTICE, CITATION.cff
CONTRIBUTING.md, CHANGELOG.md, .github/ISSUE_TEMPLATE/   (how to report; corrections log)
```

## Licence

Code, Lean files and scripts: Apache-2.0 (`LICENSE`, `NOTICE`). Text and documents
(READMEs, `docs/`, any write-up): CC-BY-4.0. Third-party models and datasets
are not redistributed here; each folder will say what it needs and under what licence.

## Status of this copy

Public since 2026-11-15 (v0.2). No DOI yet: one will be assigned when a version is
archived (placeholder in `CITATION.cff`).
