"""Rung-6a draw and doctor-facing case folders (PREREG_R6A.md).

    python tools/make_r6a_cases.py draw              # pool/draw6a.json; prints dev ids only
    python tools/make_r6a_cases.py dev|test net|prog

Same four task families and pool as rungs 4 and 5 (tools/r4pool.py). The draw excludes
every setting drawn at rungs 4 and 5 (dev, test, reserve) and the feasibility settings.
Folders: runs/rung6a-<split>/<arm>/<id>/.
"""
import json, os, random, shutil, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r4pool as P
import make_r4_cases as M4

HERE = P.HERE
DRAW_SEED = 4047
DELTA = "1 / 1000"


def draw():
    pool = json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))
    used = set(P.FEASIBILITY_IDS)
    for f, pre in (("draw4.json", "rung4_"), ("draw5.json", "rung5_")):
        d = json.load(open(os.path.join(HERE, "pool", f)))
        for k in ("dev", "test", "reserve"):
            used |= set(d[pre + k])
    rng = random.Random(DRAW_SEED)
    dev, test, reserve = [], [], []
    for name in P.FAMILIES:
        ids = [c["id"] for c in pool if c["family"] == name and c["id"] not in used]
        rng.shuffle(ids)
        dev += ids[:1]; test += ids[1:4]; reserve += ids[4:6]
    out = {"pool_sha256": P.sha(pool), "draw_seed": DRAW_SEED, "excluded": sorted(used),
           "rung6a_dev": dev, "rung6a_test": test, "rung6a_reserve": reserve}
    json.dump(out, open(os.path.join(HERE, "pool", "draw6a.json"), "w"), indent=1)
    print("draw6a written; test-set sha256", P.sha(test), "| %d dev, %d test, %d reserve" % (len(dev), len(test), len(reserve)))
    print("dev ids:", dev, "(test ids are in pool/draw6a.json; not read before the freeze)")


def spec_net(c):
    defs, _ = M4.spec_parts(c)
    V = c["V"]
    return "\n".join(
        ["namespace Lane4.Case", "open Lane4.RSeq (Vec)", "open Lane4.RSoft Lane4.AGate",
         "open Lane4.Seq (Mask cand tokAt)", ""] + defs + ["",
         "def Statement (N : ANet) : Prop :=",
         "  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →",
         "  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →",
         "  ∀ p : APert, p.Within (%s) →" % DELTA,
         "  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ %d) →" % V,
         "  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →",
         "  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →",
         "  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4",
         "", "end Lane4.Case", ""])


def final_net(V):
    t = open(os.path.join(HERE, "runs", "r6-kit", "kX", "Final.lean"), encoding="utf-8").read()
    assert t.count("shapeOK Lane4.Case.net 2") == 1 and t.count("1 ≤ t ∧ t ≤ 2") == 2 and t.count("p.Within (1 / 1000)") == 2
    return (t.replace("shapeOK Lane4.Case.net 2", "shapeOK Lane4.Case.net %d" % V)
             .replace("1 ≤ t ∧ t ≤ 2", "1 ≤ t ∧ t ≤ %d" % V).replace("p.Within (1 / 1000)", "p.Within (%s)" % DELTA))


TASK_NET = """# Task: write a GATED softmax transformer's weights and prove it correct for every length under ADDITIVE perturbation of every weight

Write the weights of a small transformer in the fixed architecture of `AGate.lean` that
solves the task below, and a Lean 4 proof of `Statement` in `Spec.lean`.

**Task.** {text}

**What the statement says.** For every rounding function `fl` with `Rnd u η M fl`, every
float exponential `ex` with `ExpM u η ex`, every ADDITIVE perturbation of every weight by
at most {delta} (a written weight `w` is used as `asw fl w d = fl (w + d)`, `|d| ≤ {delta}`,
one `d` per weight, INCLUDING weights written as 0, gate weights, gate biases and slopes),
and every input whose number of positions `n = length + 1` satisfies `u * n ≤ 1/256`,
`η * n ≤ 1/2^100` and `2^40 * n^2 ≤ M`: at every position `i` in 1..length the output is
within 1/4 of the target. `Final.lean` then derives two corollaries (you do not prove
them): exact arithmetic at EVERY length, and IEEE binary32 up to 65,535 tokens.

**Architecture (fixed; read the header of `AGate.lean`).** Written weights are rationals.
A BOS token (token 0) is put at position 0. The state at a position is ONLY the stored
embedding row of its token: there are NO position features. Positions enter through a
score bias `fl (m' * (j - i))` with one slope `m` per head. Each head has a gate neuron
on the keys: key `j` is a candidate for query `i` iff the mask allows it (all, causal
`j ≤ i`, strict `j < i`) and `relu (fl (g' · x_j + gb')) = 0` exactly. Attention is softmax
over the candidates. Each block is heads plus a one-hidden-layer ReLU MLP, both residual.
With no candidate a head's output is 0. Limits: at most 4 blocks, 4 heads per block,
state width at most 24, MLP hidden width at most 32, slopes between 1 and 1024.

**Method: an ideal value plus an error bound.** Nothing is exactly zero here, so closed
forms by `simp` are not available. Reason about each quantity as an IDEAL value (written
weights, no perturbation, no rounding) plus an error:
- `AGateKit.lean`: `ardot_near_abs` and `ardot_near` (a stored-weight dot product is close
  to the ideal dot product `dotQ`; `Close x xh e X` says a vector is within `e` of its
  ideal), `pdot_near` (the same for two real vectors), `bias_gap` (an earlier key is
  behind a later one by at least `(m - δ)` per position, up to a small slack).
- `AGateKitW.lean` (end of file): `ardot_near_w`, the per-coordinate form: each
  coordinate has its own entry error and bound (`CloseL`, `wErr`). Use it when the
  state is wide: the uniform lemmas charge `len * δ * (X + e)` with the largest `X`
  and `e` and can exceed the 1/4 budget on their own.
- `AGate.lean`: `asw_near`, `asw_bound`, `fl_asw`, `relu_fl_zero` (a gate with a
  non-positive pre-activation is exactly 0), `AHead.mem_cands`, `AHead.cands_nodup`.
- `RSoftKit.lean` (end of file): `soft_near` (a candidate that beats every other
  candidate by a score gap of at least `16 * |j - k|` gets its value returned within
  `B/100 + 1/2^90`), `soft_zeros`.
- `RSoft.lean`: `Rnd.abs`, `Rnd.near`, `Rnd.bound`, `Rnd.gap`, `mul_near`, `range_const`,
  `range_lin`, `range_quad`, `eta_tiny`, `ndist_cast`.

**What your proof must cover.**
1. The gate: after perturbing the embedding and ALL gate parameters, every key you want
   as a candidate has a non-positive pre-activation (gate exactly 0), and every key you
   want removed has a positive gate.
2. BOS and the empty case: say whether the candidate list can be empty for a position
   `i ≥ 1`, and prove the output in that case.
3. The content part of the score (score matrix times states) is bounded by a small
   constant, uniformly in length.
4. The winner beats every other candidate by at least `16 * |j - k|` after the slope
   perturbation, the content noise and the rounding.
5. Every argument of `fl` is within the range `M` (each kit lemma asks for it).
6. The final error is at most 1/4.

**Advice.** A gate that is exactly 0 on the wanted keys survives additive noise only if
its pre-activation has a margin (for example a bias of -1/2 against a flag of 0 or 1).
A state entry produced by an earlier layer is only approximately its ideal value; if a
later gate must be exactly 0 on it, give that gate a margin too. Keep written weights
and state values small: every bound scales with them. Read `EXAMPLE.lean` closely.
The checker is your only compiler: submit early and in parts (helper lemmas first; a
partial file FAILS at `Final.lean` but shows Lean's errors for your part). Stopping
with unused submissions counts as a FAIL, the same as using all of them.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case` (with
`open Lane4.RSeq (Vec)`, `open Lane4.RSoft Lane4.AGate` and
`open Lane4.Seq (Mask cand tokAt)`):

- `def net : ANet` with {V} real tokens, so `{V1}` embedding rows (row 0 is BOS).
- `theorem net_ok : Statement net`.
""" + M4.COMMON.replace(
    "`import Lane4.RSeq` (which imports Lane4.Seq and Lane4.Basic), then `Spec.lean`, then",
    "`import Lane4.AGateAll` (AGateKitW, AGateKit, AGate, RSoftKit, RSoft, RSeq, Seq, Basic, and the\n  binary32 file used only by `Final.lean`), then `Spec.lean`, then").replace(
    "Read `RSeq.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first; `Seq.lean` holds the\n"
    "  mask, candidate-list and token lemmas that `RSeq.lean` reuses.",
    "Read `AGate.lean`, `AGateKit.lean`, the end of `AGateKitW.lean`, the end of `RSoftKit.lean`, `Spec.lean`, `Final.lean`\n"
    "  and `EXAMPLE.lean` first. Long linter warnings can push errors out of the shown\n"
    "  output; put `set_option linter.unusedVariables false`, `linter.unusedSimpArgs false`\n"
    "  and `linter.deprecated false` at the top of your file.")
assert "AGateAll" in TASK_NET and "end of `RSoftKit.lean`" in TASK_NET


def build(split, arm, cap=12):
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
    ids = json.load(open(os.path.join(HERE, "pool", "draw6a.json")))["rung6a_" + split]
    made = 0
    for cid in ids:
        c = pool[cid]
        d = os.path.join(HERE, "runs", "rung6a-" + split, arm, cid)
        if os.path.exists(os.path.join(d, "case.json")):
            continue
        _, text = M4.spec_parts(c)
        fmt = dict(text=text, V=c["V"], V1=c["V"] + 1, py=M4.PY, submit=M4.SUBMIT, delta=DELTA.replace(" ", ""),
                   casedir=d.replace("\\", "/"), cap=cap)
        os.makedirs(os.path.join(d, "scratch"), exist_ok=True)
        if arm == "net":
            files = {"TASK.md": TASK_NET.format(**fmt), "Spec.lean": spec_net(c), "Final.lean": final_net(c["V"]),
                     "EXAMPLE.lean": open(os.path.join(HERE, "examples", "EXAMPLE_r6a_net.lean"), encoding="utf-8").read()}
            mods = ("Basic", "Seq", "RSeq", "RSoft", "RSoftKit", "AGate", "AGateKit", "AGateKitW")
            meta_final = ["Lane4Final.final", "Lane4Final.shape", "Lane4Final.exact_all_lengths", "Lane4Final.binary32"]
            imp = "AGateAll"
        else:
            files = {"TASK.md": M4.TASK_PROG.format(**fmt), "Spec.lean": M4.spec_lean(c, "prog"), "Final.lean": M4.FINAL_PROG,
                     "EXAMPLE.lean": open(os.path.join(HERE, "examples", "EXAMPLE_r4_prog.lean"), encoding="utf-8").read()}
            mods = ("Basic", "Seq", "RSeq")
            meta_final = ["Lane4Final.final"]
            imp = "RSeq"
        for name, txt in files.items():
            open(os.path.join(d, name), "w", encoding="utf-8", newline="\n").write(txt)
        meta = {"id": cid, "arm": arm, "rung": "6a", "split": split, "family": c["family"], "import": imp,
                "delta": DELTA.replace(" ", ""), "final_theorems": meta_final, "max_attempts": cap, "lean_timeout": 600}
        if arm == "prog":
            meta["prog_banned"] = M4.PROG_BANNED
        json.dump(meta, open(os.path.join(d, "case.json"), "w", encoding="utf-8"), indent=1)
        for f in mods:
            shutil.copyfile(os.path.join(HERE, "Lane4", f + ".lean"), os.path.join(d, f + ".lean"))
        made += 1
    print("built %d rung6a %s/%s cases" % (made, split, arm))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if sys.argv[1] == "draw":
        draw()
    else:
        build(sys.argv[1], sys.argv[2])
