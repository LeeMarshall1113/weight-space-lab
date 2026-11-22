# Changelog

Corrections, downgrades and additions, newest first. Reporters are credited unless they
ask otherwise. A claim that is narrowed or retracted is also downgraded in the index table
in `README.md`; it is not silently edited.

## v0.5 (2026-11-22)

- `proofs/` extended with rung 9-LN15 (LayerNorm), with the report at version 0.11
  (`proofs/REPORT.md`, Sections 6.12 and 6.13, claims rows 38 to 41, a new list of caveats after the
  rung 6a to 8 caveats). **It is a post-hoc rung.**
  - Rung 9-LN, registered at ball 2^-14, **failed its kill rule** (5 of 18 tuning networks accepted by the
    exact-rational prototype, the line was 6). It is published as a failure with its own documents
    (`proofs/docs/PREREG_R9LN.md`, `RESULTS_R9LN.md`) and no Lean was written for it.
  - Rung 9-LN15: radius 2^-15, the enclosure design, the symbol layout and fixed-point arithmetic were
    chosen after the failure on the same 18 tuning networks (five checker variants tried). One soundness
    theorem `Lane4.LNC.SoundLN` (20 new modules `Lane4/LN*.lean`, ten kit cases proved by agents or by
    text-substitution ports of rung 8), then a generated Lean file set per network. Fresh seeds 400 to 419:
    20 trained, 19 compute the task and pass the screen, **13 of 19 proved**, 6 screened networks compute the
    task and are not proved; bar 3 of 3; 7 of 7 controls rejected. The method did not carry to real text.
  - New tools: `tools/recheck_ln15.py`, `build_ln_net.py`, `make_r9ln15_net.py`, `r9ln15_cert.py` and the
    prototype and diagnostic scripts of the failed rung. `tools/check.py`: module table extended.
  - `proofs/VERIFY.md` Section 7: the re-check of all new Lean files. 44 of 47 passed in the first run; the other three (the 780-case file sets `f402`, `f409`, `t113`) each had one file exceed the registered 900 s limit by under 5 s on a shared machine, and passed on a re-run at a 1500 s limit (two of them again exceeded 900 s per file, up to 1,014 s). The lab's own runs were inside 900 s.
  - README: a new "Latest" bullet, a claims row and caveat 12.
- `proofs/writeup/NOVELTY_R8.md`: new section on related work for the mechanism rows. Three works
  on extracting programs from transformers were not cited in v0.4 (BlockCert, arXiv 2511.17645;
  Zhang et al., arXiv 2406.05564; Adriaensen and Maene, IDA 2025). No claim or number changes; the
  section says the extraction idea is not new. (Committed after v0.4.)

## v0.4 (2026-11-21)

- `proofs/` extended with rungs 6a, 7 and 8, with the report at version 0.10
  (`proofs/REPORT.md`, Sections 6.8 to 6.10, claims rows 29 to 35, and a new list of caveats
  that leads "Known weaknesses"):
  - rung 6a: 12 of 12 written gated softmax transformers, additive 1/1000 ball, every length
    (a non-standard gate; the kit was amended once);
  - rung 7: one soundness theorem for a checker and a generated Lean file per gradient-trained
    network (4 of 9 screened reserve networks; 0 of 18 on the standard architecture);
  - rung 8: the same method on standard softmax attention, 19 of 20 fresh seeds at an additive
    radius of 2^-14 (chosen on the tuning set), eight controls rejected.
  - mechanism row (b): a finder reads a trivial 5-state program off the weights of the 19 accepted rung 8
    networks and the kernel checks equality at every length (outcome fixed in advance; `runs/mech`).
  - mechanism row (a): on the same networks, each head puts all but 2^-21 of its softmax weight on a
    window of its latest positions, kernel-checked (`runs/mech/*/Attn.lean`).
- New in `proofs/`: Lean frameworks `Lane4/AGate*`, `R7*`, `R8*`; agent-proved kit cases
  (`runs/r6-kit`, `r7-kit`, `r8-kit`); the rung-6a cases; the generated per-network files and
  controls (`runs/r7-nets`, `runs/r8-nets`) with the trained networks of rung 8
  (`runs/r8-fresh`); pre-registrations, results and freeze lists (`docs/`); tools; results rows;
  `writeup/NOVELTY_R8.md` (what is and is not new against prior work, including a
  kernel-checked all-length theorem for a trained threshold RNN that came earlier).
- Checker: module table extended; `tools/recheck_r678.py` and `tools/build_net.py` re-check
  the new Lean files; results in `proofs/VERIFY.md`.
- Report: three leftover internal phrases in the v0.9 text were reworded; no claim, number or
  status changed.
- No external corrections yet.

## v0.3 (2026-11-15)

- `reading/` unit 4 added: kernel-checked all-lengths weight-ball certificates (1/1000) for
  nine trained clipped-ReLU RNNs, with the pre-registration (`reading/docs/PREREG_RNN.md`,
  amendments A1 and A2), the Lean framework and files, scripts and rows. Registered status:
  **no pass** (parity 3/8 ordinary and 1/8 penalty, mod-3 0/8 in both arms, Tomita 4 1/8 and
  4/8, p = 0.14), boundary; the cluster-count explanation and the tightness caveat are in
  the unit. Re-checked in `proofs/VERIFY.md`.
- README: a short "What this is" at the top; "Known weaknesses" moved below the index and
  linked from the opening; the five empty folders removed (their index rows stay, marked
  "not yet included").
- `proofs/REPORT.md`: an abstract added; no claim, number or status changed.
- No external corrections yet.

## v0.2 (2026-11-15, first public version)

- `proofs/` synced to the technical report version 0.9 (`proofs/REPORT.md`): rung 5 (softmax and a
  binary32 model), the rung-4 rounding witness and kit lemmas, Lean witnesses for three cells
  of the perturbation 2x2 (version 2), rung 6b (collision bound, memberships) and rung 6c
  (token-blind class), the open conjectures (statements only), the matching pre-registrations
  and results files, tools and data. Rung 6a (registered, parked) is not included.
- `reading/`: three finished units, all negatives or boundaries (compiled versus trained
  transformers; a decay curve that could not be built, with its correction; kernel-checked
  weight-ball certificates for tiny trained ReLU nets and where they stop), with the bridge
  Lean files.
- Checker: module table extended; `tools/recheck_release.py` and `reading/bridge/recheck_bridge.py`
  re-check every Lean file; results in `proofs/VERIFY.md`.
- Known weaknesses block rewritten to match the report; the "fragile versus robust"
  framing of v0.1 is withdrawn (see the report's 2x2 section).
- No external corrections yet.

## v0.1 (private, never released)

- First private pre-release copy: `proofs/` (rungs 2 to 4), re-checked from this
  folder (`proofs/VERIFY.md`: 67 of 67 recorded solutions pass). Other folders are empty
  slots.
- No external corrections yet.
