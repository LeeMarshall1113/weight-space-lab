"""PREREG_RNN non-vacuity: smallest weight radius at which a wrong output is found, confirmed exactly.

    python reading/rnn/breaks.py <net-name> [...]
For a certified net: candidate strings = all strings of length <= 10 plus 300 random strings of
length 11-50 (seed 11); the 64 with the smallest unperturbed |margin| are attacked by 40 steps of
sign-gradient on every weight and bias within an L-inf radius r (the certificate's perturbation
set). A break at r = a found (weights, string) with the wrong sign, re-run in exact rationals.
The smallest breaking r is found by bisection over [max certified tau, 1/2]; tightness ratio =
break r / max certified tau. Writes results/rnncert_breaks.jsonl (appends).
"""
import json
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import rnncert as R  # noqa: E402


def candidates(seed=11):
    import itertools
    ws = [list(w) for L in range(0, 11) for w in itertools.product([0, 1], repeat=L)]
    rng = np.random.default_rng(seed)
    ws += [[int(v) for v in rng.integers(0, 2, int(rng.integers(11, 51)))] for _ in range(300)]
    return ws


def exact_out(qp, dp, w):
    Q = R.Q
    W = [[F(int(x), Q) + F(float(e)) for x, e in zip(r, er)] for r, er in zip(qp["W"], dp["W"])]
    U = [[F(int(x), Q) + F(float(e)) for x, e in zip(r, er)] for r, er in zip(qp["U"], dp["U"])]
    b = [F(int(x), Q) + F(float(e)) for x, e in zip(qp["b"], dp["b"])]
    v = [F(int(x), Q) + F(float(e)) for x, e in zip(qp["v"], dp["v"])]
    c = F(int(qp["c"][0]), Q) + F(float(dp["c"][0]))
    h = [F(0)] * len(b)
    for a in w:
        h = [R.clipF(sum(Wi[j] * h[j] for j in range(len(h))) + U[i][a] + b[i]) for i, Wi in enumerate(W)]
    return sum(vi * hi for vi, hi in zip(v, h)) + c


def attack(qp, lang, r, ws):
    import torch
    torch.set_num_threads(2)
    fp = {k: torch.tensor(np.asarray(v, dtype=np.float64) / R.Q) for k, v in qp.items()}
    ys = torch.tensor([1.0 if R.accepts(lang, w) else -1.0 for w in ws], dtype=torch.float64)
    T = max(len(w) for w in ws)
    X = torch.zeros(len(ws), T, 2, dtype=torch.float64)
    M = torch.zeros(len(ws), T, dtype=torch.float64)
    for i, w in enumerate(ws):
        for t, a in enumerate(w):
            X[i, t, a] = 1; M[i, t] = 1
    d = {k: torch.zeros_like(v, requires_grad=True) for k, v in fp.items()}

    def margins():
        h = torch.zeros(len(ws), fp["W"].shape[0], dtype=torch.float64)
        for t in range(T):
            hn = torch.clamp(h @ (fp["W"] + d["W"]).T + X[:, t] @ (fp["U"] + d["U"]).T + fp["b"] + d["b"], 0, 1)
            m = M[:, t:t + 1]
            h = m * hn + (1 - m) * h
        return (h @ (fp["v"] + d["v"]) + fp["c"] + d["c"]) * ys

    for _ in range(40):
        mg = margins()
        loss = mg.min()
        g = torch.autograd.grad(loss, list(d.values()))
        with torch.no_grad():
            for v, gv in zip(d.values(), g):
                v -= r / 8 * torch.sign(gv)
                v.clamp_(-r, r)
    with torch.no_grad():
        mg = margins()
    i = int(mg.argmin())
    if mg[i] > 0:
        return None
    dp = {k: v.detach().numpy() for k, v in d.items()}
    ex = exact_out(qp, dp, ws[i])
    ok = (ex > 0) == R.accepts(lang, ws[i]) and ex != 0
    return None if ok else ws[i]


def run(name, out):
    dat = json.loads((R.NETS / f"{name}.json").read_text())
    rec = dat["rec"]
    qp = {k: np.array(v) for k, v in dat["qp"].items()}
    lang = rec["lang"]
    lo = rec.get("max_tau")
    if not rec.get("cert_py") or lo is None:
        return
    ws = candidates()
    fp = R.floats(qp)
    outs = R.run_float(fp, ws)
    frag = sorted(range(len(ws)), key=lambda i: abs(outs[i]))[:64]
    ws = [ws[i] for i in frag]
    hi = 0.5
    if attack(qp, lang, hi, ws) is None:
        res = {"net": name, "max_tau": lo, "break_r": None, "note": "no break found up to 1/2"}
    else:
        lo_b = lo
        for _ in range(14):
            mid = (lo_b + hi) / 2
            if attack(qp, lang, mid, ws) is not None:
                hi = mid
            else:
                lo_b = mid
        res = {"net": name, "max_tau": lo, "break_r": hi, "ratio": hi / lo if lo else None}
    out.write(json.dumps(res) + "\n"); out.flush()
    print(res, flush=True)


if __name__ == "__main__":
    with open(R.OUT / "rnncert_breaks.jsonl", "a") as f:
        for n in sys.argv[1:]:
            run(n, f)
