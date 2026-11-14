"""Trained twins (PREREG, twin arm). numpy only, CPU, 2 threads.

    python tools/train_twin.py dev|test

For each spec: take the architecture of the net-arm solution (hidden widths
parsed from its passing Solution.lean; 16,16 if the net arm did not pass),
train seeds 0,1,2 with Adam on MSE, round weights to multiples of 1/1024, then
measure the rounded network exactly (Fractions) on 20,000 random rational box
points. Seed 0 becomes the doctor's twin case with
    eps = ceil(4 * max_exact_error * 100) / 100.
Writes runs/rung1-<split>/twin/<id>/ and results/twins-<split>.json.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")
import glob, json, math, random, re, sys
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import specpool as SP
import make_cases as MC

HERE = SP.HERE
STEPS, BATCH, LR, DEN, N_EVAL = 20000, 256, 1e-2, 1024, 20000


def spec_np(e, X):
    t = e[0]
    if t == "aff":
        return sum(float(c) * X[:, i] for i, c in e[1].items()) + float(e[2])
    if t == "lin":
        return float(e[1]) * spec_np(e[2], X) + float(e[3]) * spec_np(e[4], X)
    if t == "clamp":
        return np.minimum(np.maximum(spec_np(e[1], X), float(e[2])), float(e[3]))
    v = [spec_np(k, X) for k in e[1:]]
    if t == "max":
        return np.maximum(v[0], v[1])
    if t == "min":
        return np.minimum(v[0], v[1])
    if t == "abs":
        return np.abs(v[0])
    if t == "relu":
        return np.maximum(v[0], 0)
    if t == "med3":
        return np.maximum(np.minimum(v[0], v[1]), np.minimum(np.maximum(v[0], v[1]), v[2]))


def train(e, box, widths, seed):
    rng = np.random.default_rng(seed)
    sizes = [len(box)] + widths + [1]
    Ws = [rng.normal(0, math.sqrt(2.0 / sizes[i]), (sizes[i + 1], sizes[i])) for i in range(len(sizes) - 1)]
    bs = [np.zeros(sizes[i + 1]) for i in range(len(sizes) - 1)]
    params = Ws + bs
    m = [np.zeros_like(p) for p in params]
    v = [np.zeros_like(p) for p in params]
    lo = np.array([b[0] for b in box], float)
    hi = np.array([b[1] for b in box], float)
    L = len(Ws)
    for step in range(1, STEPS + 1):
        X = rng.uniform(lo, hi, (BATCH, len(box)))
        y = spec_np(e, X)
        acts, h = [X], X
        for i in range(L):
            z = h @ Ws[i].T + bs[i]
            h = np.maximum(z, 0) if i < L - 1 else z
            acts.append(h)
        g = 2 * (h[:, 0] - y)[:, None] / BATCH
        gW, gb = [None] * L, [None] * L
        for i in reversed(range(L)):
            if i < L - 1:
                g = g * (acts[i + 1] > 0)
            gW[i] = g.T @ acts[i]
            gb[i] = g.sum(0)
            g = g @ Ws[i]
        lr = LR * 0.5 * (1 + math.cos(math.pi * step / STEPS))
        for j, gr in enumerate(gW + gb):
            m[j] = 0.9 * m[j] + 0.1 * gr
            v[j] = 0.999 * v[j] + 0.001 * gr * gr
            params[j] -= lr * (m[j] / (1 - 0.9 ** step)) / (np.sqrt(v[j] / (1 - 0.999 ** step)) + 1e-8)
    return Ws, bs


def rationalise(Ws, bs):
    r = lambda a: [[F(int(round(float(x) * DEN)), DEN) for x in row] for row in a]
    return [r(W) for W in Ws], [r([b])[0] for b in bs]


def eval_exact(Wq, bq, x):
    h = x
    for i, (W, b) in enumerate(zip(Wq, bq)):
        h = [sum(w * a for w, a in zip(row, h)) + c for row, c in zip(W, b)]
        if i < len(Wq) - 1:
            h = [max(a, F(0)) for a in h]
    return h[0]


def exact_error(e, box, Wq, bq, seed):
    rng = random.Random(1000 + seed)
    worst, n_equal = F(0), 0
    for _ in range(N_EVAL):
        x = [F(rng.randint(lo * 64, hi * 64), 64) for lo, hi in box]
        d = abs(eval_exact(Wq, bq, x) - SP.ev(e, x))
        n_equal += d == 0
        worst = max(worst, d)
    return worst, n_equal


def widths_from_solution(path):
    """Hidden widths from the bias lists of a doctor's net literal, in file order."""
    s = MC_strip(open(path, encoding="utf-8").read())
    bl = re.findall(r"\bb\s*:=\s*\[([^\]]*)\]", s)
    if len(bl) < 2:
        return None
    w = [len([t for t in b.split(",") if t.strip()]) for b in bl]
    return w[:-1] if w[-1] == 1 and all(1 <= k <= 32 for k in w) else None


def MC_strip(s):
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    return re.sub(r"--.*", " ", s)


def qlit(c):
    return str(c.numerator) if c.denominator == 1 else "%d/%d" % (c.numerator, c.denominator)


def net_lean(Wq, bq, name="twin"):
    # one layer per line: Lean rejects a `b :=` field indented left of its `W :=`
    def layer(W, b):
        rows = ", ".join("[" + ", ".join(qlit(x) for x in row) + "]" for row in W)
        return "{ W := [%s], b := [%s] }" % (rows, ", ".join(qlit(x) for x in b))
    hid = ",\n      ".join(layer(W, b) for W, b in zip(Wq[:-1], bq[:-1]))
    return "def %s : Lane4.Net :=\n  { hidden := [\n      %s],\n    out := %s }" % (name, hid, layer(Wq[-1], bq[-1]))


TASK_TWIN = """# Task: prove an error bound for a given ReLU network

`Spec.lean` contains a ReLU multi-layer perceptron `twin` with fixed rational weights and a
target function `spec`. Prove in Lean 4 that, at every real point of the box, the network's
output is within ε of the target.

**Target** ({n} input{s}):

    spec({args}) = {text}

**Box:** {box}

**ε:** {eps}

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `theorem twin_correct : StatementTwin`, where `StatementTwin` is in `Spec.lean`. You do
  not write any weights; the network is given and must not be changed.
""" + MC.COMMON

FINAL_TWIN = """namespace Lane4Final
theorem shape : Lane4.Net.shapeOK Lane4.Case.twin {n} 1 = true := by decide
theorem final : Lane4.Case.StatementTwin := Lane4.Case.twin_correct
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
"""


def main(split, cap=12):
    pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))}
    draw = json.load(open(os.path.join(HERE, "pool", "draw.json")))
    out_path = os.path.join(HERE, "results", "twins-%s.json" % split)
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    results = json.load(open(out_path)) if os.path.exists(out_path) else {}
    for sid in draw["rung1_" + split]:
        if sid in results:
            continue
        s = pool[sid]
        e = SP.from_json(s["expr"])
        box = [tuple(b) for b in s["box"]]
        net_dir = os.path.join(HERE, "runs", "rung1-" + split, "net", sid)
        widths, src = None, "default 16,16"
        passed = [p for p in sorted(glob.glob(os.path.join(net_dir, "attempts", "*.json")))
                  if json.load(open(p, encoding="utf-8")).get("pass")]
        if passed:
            widths = widths_from_solution(passed[0][:-5] + ".lean")
            src = "net-arm solution" if widths else "default 16,16 (could not parse the solution)"
        widths = widths or [16, 16]
        rec = {"widths": widths, "arch_source": src, "seeds": {}}
        for seed in (0, 1, 2):
            Ws, bs = train(e, box, widths, seed)
            Wq, bq = rationalise(Ws, bs)
            worst, n_eq = exact_error(e, box, Wq, bq, seed)
            rec["seeds"][seed] = {"max_exact_err": float(worst), "max_exact_err_q": qlit(worst),
                                  "points_exactly_equal": n_eq, "points": N_EVAL}
            if seed == 0:
                eps = F(math.ceil(4 * worst * 100), 100)
                rec["eps"] = qlit(eps)
                n = s["n_in"]
                args = " ".join("x%d" % i for i in range(n))
                d = os.path.join(HERE, "runs", "rung1-" + split, "twin", sid)
                spec = "\n".join([
                    "namespace Lane4.Case", "",
                    "noncomputable def spec (%s : ℝ) : ℝ :=\n  %s" % (args, s["text"]), "",
                    net_lean(Wq, bq), "",
                    "def StatementTwin : Prop :=",
                    "  ∀ %s : ℝ, %s →" % (args, MC.box_hyps(s["box"])),
                    "    ∃ y : ℝ, twin.eval [%s] = [y] ∧ |y - spec %s| ≤ (%s)" % (", ".join(args.split()), args, qlit(eps)),
                    "", "end Lane4.Case", ""])
                fmt = dict(n=n, s="" if n == 1 else "s", args=", ".join(args.split()), text=s["text"],
                           box=", ".join("%s ≤ x%d ≤ %s" % (lo, i, hi) for i, (lo, hi) in enumerate(s["box"])),
                           eps=qlit(eps), py=MC.PY, submit=MC.SUBMIT, casedir=d.replace("\\", "/"), cap=cap)
                MC.write_case(d, {"TASK.md": TASK_TWIN.format(**fmt), "Spec.lean": spec,
                                  "Final.lean": FINAL_TWIN.format(n=n), "EXAMPLE.lean": MC.example("twin")},
                              {"id": sid, "arm": "twin", "rung": 1, "split": split,
                               "final_theorems": ["Lane4Final.final", "Lane4Final.shape"],
                               "max_attempts": cap, "lean_timeout": 600, "eps": qlit(eps), "widths": widths})
        results[sid] = rec
        json.dump(results, open(out_path, "w"), indent=1)  # save as each case finishes
        print(sid, widths, src, {k: v["max_exact_err"] for k, v in rec["seeds"].items()}, "eps", rec["eps"], flush=True)


if __name__ == "__main__":
    main(sys.argv[1])
