"""Rung-5 draw and doctor-facing case folders (PREREG_R5.md).

    python tools/make_r5_cases.py draw              # pool/draw5.json; prints dev ids only
    python tools/make_r5_cases.py dev|test net|prog

Same four task families and pool as rung 4 (tools/r4pool.py). The draw excludes every
setting drawn at rung 4 (dev, test, reserve) and the lane's feasibility settings.
Folders: runs/rung5-<split>/<arm>/<id>/.
"""
import json, os, random, shutil, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r4pool as P
import make_r4_cases as M4

HERE = P.HERE
DRAW_SEED = 4046
TAU = "1 / 200"


def draw():
    pool = json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))
    d4 = json.load(open(os.path.join(HERE, "pool", "draw4.json")))
    used = set(d4["rung4_dev"]) | set(d4["rung4_test"]) | set(d4["rung4_reserve"]) | P.FEASIBILITY_IDS
    rng = random.Random(DRAW_SEED)
    dev, test, reserve = [], [], []
    for name in P.FAMILIES:
        ids = [c["id"] for c in pool if c["family"] == name and c["id"] not in used]
        rng.shuffle(ids)
        dev += ids[:1]; test += ids[1:4]; reserve += ids[4:6]
    out = {"pool_sha256": P.sha(pool), "draw_seed": DRAW_SEED, "excluded": sorted(used),
           "rung5_dev": dev, "rung5_test": test, "rung5_reserve": reserve}
    json.dump(out, open(os.path.join(HERE, "pool", "draw5.json"), "w"), indent=1)
    print("draw5 written; test-set sha256", P.sha(test), "| %d dev, %d test, %d reserve" % (len(dev), len(test), len(reserve)))
    print("dev ids:", dev, "(test ids are in pool/draw5.json; not read before the freeze)")


def spec_net(c):
    defs, _ = M4.spec_parts(c)
    V = c["V"]
    return "\n".join(
        ["namespace Lane4.Case", "open Lane4.RSeq Lane4.RSoft", "open Lane4.Seq (Mask cand tokAt)", ""] + defs + ["",
         "def Statement (N : TNet) : Prop :=",
         "  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →",
         "  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →",
         "  ∀ p : Pert, p.Within (%s) →" % TAU,
         "  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ %d) →" % V,
         "  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →",
         "  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →",
         "  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |sout N fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4",
         "", "end Lane4.Case", ""])


FINAL_NET = open(os.path.join(HERE, "examples", "FINAL_r5_net.lean.txt"), encoding="utf-8").read() \
    if os.path.exists(os.path.join(HERE, "examples", "FINAL_r5_net.lean.txt")) else None

TASK_NET = """# Task: write a SOFTMAX transformer's weights and prove it correct for every length, every nearby weight setting and floating-point arithmetic

Write the weights of a small softmax-attention transformer, in the fixed architecture of
`RSoft.lean`, that solves the task below, and a Lean 4 proof of `Statement` in `Spec.lean`.

**Task.** {text}

**What the statement says.** For every rounding function `fl` satisfying `Rnd u η M fl`
(relative error `u ≤ 2^-24` plus an underflow term `η ≤ 2^-149`, guaranteed ONLY for
arguments of absolute value at most `M`), every float exponential `ex` satisfying
`ExpM u η ex`, every relative perturbation of every weight by at most {tau} (weight `w`
becomes `fl (w * (1 + d))`, `|d| ≤ {tau}`), and every input `w` whose number of positions
`n = length + 1` satisfies `u * n ≤ 1/256`, `η * n ≤ 1/2^100` and `2^40 * n^2 ≤ M`: at
every position `i` in 1..length the output is within 1/4 of the target. `Final.lean`
then derives two corollaries from your theorem (you do not prove them): exact arithmetic
at EVERY length, and IEEE binary32 arithmetic up to 65,535 tokens. One proof must cover
both, so it has to work from the `Rnd` and `ExpM` axioms.

**Architecture (fixed; read the header of `RSoft.lean`, and `RSeq.lean` for the parts it
reuses).** Written weights are rationals. A BOS token (token 0) is put at position 0, so
your input occupies positions 1..length. Each position starts with its token's stored
embedding row followed by three position features `[1, fl i, fl n]`. Attention is
SOFTMAX over the candidate positions (masks: all, causal `j ≤ i`, strict `j < i`), computed
as `ex (fl (score - max score))`, summed and divided, every step rounded. Each block is
heads plus a one-hidden-layer ReLU MLP, both residual. Limits: at most 4 blocks, 4 heads
per block, state width (embedding width + 3) at most 24, MLP hidden width at most 32.

**The two softmax lemmas** (end of `RSoftKit.lean`):

- `soft_near`: if one candidate `j` beats every other candidate `k` by a score gap of at
  least `16 * |j - k|` (`ndist j k`), the head's output is within `B / 100 + 1/2^90` of
  `j`'s value, where `B` bounds the values. So a selecting score needs a slope of at
  least 16 per position, after perturbation and rounding.
- `soft_zeros`: if every candidate's value is exactly 0, the output is exactly 0.

**Advice.** A weight written as 0 stays exactly 0, and sums and products of exact zeros
are exactly 0; nothing else is exact. Two stored weights written with the same value are
in general NOT equal. A score that must separate positions has to do so with a margin
that the perturbation (relative size {tau}, and it multiplies large position features)
cannot close. `Rnd` gives nothing outside `[-M, M]`: every kit lemma that touches `fl x`
asks for `|x| ≤ B` and `B ≤ M`, and `fl (fl x) = fl x` (`Rnd.idem`) needs `|x| ≤ M`; get
these from `range_const`, `range_lin`, `range_quad`. Small target values and few layers
keep the error bounds easy. Read `EXAMPLE.lean` closely: it shows the whole pattern on a
one-head network.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case` (with
`open Lane4.RSeq Lane4.RSoft` and `open Lane4.Seq (Mask cand tokAt)`):

- `def net : TNet` with {V} real tokens, so `{V1}` embedding rows (row 0 is BOS).
- `theorem net_ok : Statement net`.
""" + M4.COMMON.replace(
    "`import Lane4.RSeq` (which imports Lane4.Seq and Lane4.Basic), then `Spec.lean`, then",
    "`import Lane4.RSoftAll` (RSoftKit, RSoft, RSeq, Seq, Basic, and the binary32 file\n  used only by `Final.lean`), then `Spec.lean`, then").replace(
    "Read `RSeq.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first; `Seq.lean` holds the\n"
    "  mask, candidate-list and token lemmas that `RSeq.lean` reuses.",
    "Read `RSoft.lean`, the end of `RSoftKit.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean`\n"
    "  first; `RSeq.lean` and `Seq.lean` hold the definitions and the mask, candidate-list and\n"
    "  token lemmas that `RSoft.lean` reuses. Long linter warnings can push errors out of the\n"
    "  shown output; `set_option linter.unusedVariables false` and similar at the top help.")
assert "RSoftAll" in TASK_NET and "end of `RSoftKit.lean`" in TASK_NET


def final_net(V):
    t = open(os.path.join(HERE, "scratch", "FinalR5Test.lean"), encoding="utf-8").read()
    assert t.count("shapeOK Lane4.Case.net 2") == 1 and t.count("1 ≤ t ∧ t ≤ 2") == 2
    return t.replace("shapeOK Lane4.Case.net 2", "shapeOK Lane4.Case.net %d" % V).replace("1 ≤ t ∧ t ≤ 2", "1 ≤ t ∧ t ≤ %d" % V)


def build(split, arm, cap=12):
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
    ids = json.load(open(os.path.join(HERE, "pool", "draw5.json")))["rung5_" + split]
    made = 0
    for cid in ids:
        c = pool[cid]
        d = os.path.join(HERE, "runs", "rung5-" + split, arm, cid)
        if os.path.exists(os.path.join(d, "case.json")):
            continue
        _, text = M4.spec_parts(c)
        fmt = dict(text=text, V=c["V"], V1=c["V"] + 1, py=M4.PY, submit=M4.SUBMIT, tau=TAU.replace(" ", ""),
                   casedir=d.replace("\\", "/"), cap=cap)
        os.makedirs(os.path.join(d, "scratch"), exist_ok=True)
        if arm == "net":
            files = {"TASK.md": TASK_NET.format(**fmt), "Spec.lean": spec_net(c), "Final.lean": final_net(c["V"])}
            mods = ("Basic", "Seq", "RSeq", "RSoft", "RSoftKit")
            meta_final = ["Lane4Final.final", "Lane4Final.shape", "Lane4Final.exact_all_lengths", "Lane4Final.binary32"]
            imp = "RSoftAll"
        else:
            files = {"TASK.md": M4.TASK_PROG.format(**fmt), "Spec.lean": M4.spec_lean(c, "prog"), "Final.lean": M4.FINAL_PROG}
            mods = ("Basic", "Seq", "RSeq")
            meta_final = ["Lane4Final.final"]
            imp = "RSeq"
        files["EXAMPLE.lean"] = open(os.path.join(HERE, "examples", "EXAMPLE_r%s_%s.lean" % ("5" if arm == "net" else "4", arm)),
                                     encoding="utf-8").read()
        for name, txt in files.items():
            open(os.path.join(d, name), "w", encoding="utf-8", newline="\n").write(txt)
        meta = {"id": cid, "arm": arm, "rung": 5, "split": split, "family": c["family"], "import": imp,
                "tau": TAU.replace(" ", ""), "final_theorems": meta_final, "max_attempts": cap, "lean_timeout": 600}
        if arm == "prog":
            meta["prog_banned"] = M4.PROG_BANNED
        json.dump(meta, open(os.path.join(d, "case.json"), "w", encoding="utf-8"), indent=1)
        for f in mods:
            shutil.copyfile(os.path.join(HERE, "Lane4", f + ".lean"), os.path.join(d, f + ".lean"))
        made += 1
    print("built %d rung5 %s/%s cases" % (made, split, arm))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if sys.argv[1] == "draw":
        draw()
    else:
        build(sys.argv[1], sys.argv[2])
