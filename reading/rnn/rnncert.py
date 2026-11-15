"""PREREG_RNN: train clipped-ReLU Elman RNNs on regular languages, quantize, gate, find a box
invariant (exact rationals), export a Lean certificate for Bridge/RNN.lean.

    python reading/rnn/rnncert.py dev                     # width per language + dev diagnostics
    python reading/rnn/rnncert.py test --lang L1 --d 8    # blind test seeds (ORD, SAT, RND)
    python reading/rnn/rnncert.py export <name>           # Lean file for a net with a certificate
"""
import argparse
import itertools
import json
import math
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
NETS = HERE / "nets"
OUT = HERE.parent / "results"
LEAN = HERE.parent / "bridge" / "lean" / "Bridge" / "Nets"
Q = 256          # weight grid
G = 1 << 16      # box grid (outward rounding)
TAU = F(1, 1000)
MARGINS = (F(0), F(1, 100), F(3, 100), F(1, 10))

# ---------- DFAs over {0, 1}: (delta table [q][a], q0, accepting set) ----------
DFAS = {
    "L1": ([[0, 1], [1, 0]], 0, {0}),                          # parity of 1s, accept even
    "L2": ([[0, 1], [1, 2], [2, 0]], 0, {0}),                  # count of 1s mod 3 == 0
    "L3": ([[1, 0], [2, 0], [3, 0], [3, 3]], 0, {0, 1, 2}),    # Tomita 4: no 000
    "TRIV": ([[0, 0]], 0, {0}),                                # constant accept (control)
}


def run_dfa(lang, w):
    d, q, _ = DFAS[lang]
    for a in w:
        q = d[q][a]
    return q


def accepts(lang, w):
    return run_dfa(lang, w) in DFAS[lang][2]


# ---------- training ----------
def batch(lang, rng, n=128, lmax=20):
    ws, ys = [], []
    want_pos = n // 2
    while len(ws) < n:
        L = int(rng.integers(0, lmax + 1))
        w = [int(v) for v in rng.integers(0, 2, L)]
        y = accepts(lang, w)
        if (y and sum(ys) < want_pos) or (not y and len(ys) - sum(ys) < n - want_pos) or lang == "TRIV":
            ws.append(w); ys.append(y)
    return ws, ys


def train(lang, arm, d, seed, steps=4000):
    import torch
    torch.set_num_threads(2)
    torch.manual_seed(seed)
    rng = np.random.default_rng(seed + 7)
    W = torch.nn.Parameter(torch.randn(d, d, dtype=torch.float64) / math.sqrt(d))
    U = torch.nn.Parameter(torch.randn(d, 2, dtype=torch.float64))
    b = torch.nn.Parameter(torch.zeros(d, dtype=torch.float64))
    v = torch.nn.Parameter(torch.randn(d, dtype=torch.float64) / math.sqrt(d))
    c = torch.nn.Parameter(torch.zeros(1, dtype=torch.float64))
    P = [W, U, b, v, c]
    if arm == "RND":
        return {k: t.detach().numpy() for k, t in zip("WUbvc", P)}
    opt = torch.optim.Adam(P, lr=3e-3)
    mu = 0.1
    for _ in range(steps):
        ws, ys = batch(lang, rng)
        T = max(len(w) for w in ws)
        X = torch.zeros(len(ws), T, 2, dtype=torch.float64)
        M = torch.zeros(len(ws), T, dtype=torch.bool)
        for i, w in enumerate(ws):
            for t, a in enumerate(w):
                X[i, t, a] = 1
                M[i, t] = True
        h = torch.zeros(len(ws), d, dtype=torch.float64)
        lens = torch.tensor([len(w) for w in ws])
        H = [h]
        pen = 0.0
        for t in range(T):
            z = h @ W.T + X[:, t] @ U.T + b
            hn = torch.clamp(z, 0, 1)
            m = M[:, t].unsqueeze(1).double()
            h = m * hn + (1 - m) * h
            H.append(h)
            if arm == "SAT":
                pen = pen + (torch.relu(torch.minimum(z + mu, 1 + mu - z)) * m).sum()
        hT = torch.stack(H, 1)[torch.arange(len(ws)), lens]
        y = hT @ v + c
        loss = torch.nn.functional.binary_cross_entropy_with_logits(y, torch.tensor(ys, dtype=torch.float64))
        if arm == "SAT":
            loss = loss + 0.1 * pen / (M.sum() * d)
        opt.zero_grad(); loss.backward(); opt.step()
    return {k: t.detach().numpy() for k, t in zip("WUbvc", P)}


def quantize(p):
    return {k: np.rint(np.asarray(v, dtype=np.float64) * Q).astype(int) for k, v in p.items()}


def floats(qp):
    return {k: v.astype(np.float64) / Q for k, v in qp.items()}


# ---------- gate (float64 on the quantized weights) ----------
def gate_strings(seed=7):
    ws = [list(w) for L in range(0, 13) for w in itertools.product([0, 1], repeat=L)]
    rng = np.random.default_rng(seed)
    ws += [[int(v) for v in rng.integers(0, 2, 200)] for _ in range(1000)]
    return ws


def run_float(fp, ws, collect=None, lang=None):
    """Final read-outs for strings ws; optionally collect (dfa state, hidden) pairs."""
    W, U, b, v, c = fp["W"], fp["U"], fp["b"], fp["v"], fp["c"]
    d = W.shape[0]
    outs = []
    for w in ws:
        h = np.zeros(d)
        q = DFAS[lang][1] if lang else None
        if collect is not None:
            collect.setdefault(q, []).append(h.copy())
        for a in w:
            h = np.clip(W @ h + U[:, a] + b, 0, 1)
            if collect is not None:
                q = DFAS[lang][0][q][a]
                collect.setdefault(q, []).append(h.copy())
        outs.append(float(v @ h + c[0]))
    return outs


def gate(qp, lang, ws):
    outs = run_float(floats(qp), ws)
    return sum((o > 0) == accepts(lang, w) and o != 0 for o, w in zip(outs, ws)), len(ws)


# ---------- exact interval arithmetic (mirrors Bridge.IBP ibpRows) ----------
def ibp_rows(Wrows, brow, tau, lo, hi):
    L_out, U_out = [], []
    for row, bi in zip(Wrows, brow):
        L = F(int(bi), Q) - tau
        U = F(int(bi), Q) + tau
        for wij, l, u in zip(row, lo, hi):
            a, cc = F(int(wij), Q) - tau, F(int(wij), Q) + tau
            cs = (a * l, a * u, cc * l, cc * u)
            L += min(cs)
            U += max(cs)
        L_out.append(L); U_out.append(U)
    return L_out, U_out


def clipF(x):
    return min(max(x, F(0)), F(1))


def cell_rows(qp):
    """Cell layer rows over [h ; onehot]: W | U."""
    return [list(qp["W"][i]) + list(qp["U"][i]) for i in range(qp["W"].shape[0])], list(qp["b"])


def cell_img(qp, tau, lo, hi, a):
    Wr, br = cell_rows(qp)
    oh = [F(1) if i == a else F(0) for i in range(2)]
    L, U = ibp_rows(Wr, br, tau, lo + oh, hi + oh)
    return [clipF(x) for x in L], [clipF(x) for x in U]


def read_ok(qp, tau, lo, hi, acc):
    L, U = ibp_rows([list(qp["v"])], [int(qp["c"][0])], tau, lo, hi)
    return (L[0] > 0) if acc else (U[0] < 0)


def down(x):
    return F(math.floor(x * G), G)


def up(x):
    return F(math.ceil(x * G), G)


def box_search(qp, lang, tau, states, max_rounds=200):
    delta, q0, accset = DFAS[lang]
    nQ, d = len(delta), qp["W"].shape[0]
    for m in MARGINS:
        B = {}
        for q in range(nQ):
            if q in states:
                S = np.array(states[q])
                B[q] = ([max(F(0), down(F(float(x)) - m)) for x in S.min(0)],
                        [min(F(1), up(F(float(x)) + m)) for x in S.max(0)])
        if q0 not in B:
            B[q0] = ([F(0)] * d, [F(0)] * d)
        B[q0] = ([min(x, F(0)) for x in B[q0][0]], B[q0][1])  # h0 = 0 inside
        ok = False
        for _ in range(max_rounds):
            changed = False
            for q in list(range(nQ)):
                if q not in B:
                    continue
                for a in (0, 1):
                    t = delta[q][a]
                    lo, hi = cell_img(qp, tau, B[q][0], B[q][1], a)
                    if t not in B:
                        B[t] = ([down(x) for x in lo], [up(x) for x in hi]); changed = True
                    elif any(l < bl for l, bl in zip(lo, B[t][0])) or any(u > bu for u, bu in zip(hi, B[t][1])):
                        B[t] = ([down(min(l, bl)) for l, bl in zip(lo, B[t][0])],
                                [up(max(u, bu)) for u, bu in zip(hi, B[t][1])]); changed = True
            if any(not read_ok(qp, tau, B[q][0], B[q][1], q in accset) for q in B):
                break
            if not changed:
                ok = len(B) == nQ
                break
        if ok:
            return B, m
    return None, None


def max_tau(qp, lang, states, hi=F(1, 20), iters=12):
    lo = F(0)
    if box_search(qp, lang, F(0), states)[0] is None:
        return F(0)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if box_search(qp, lang, mid, states)[0] is not None:
            lo = mid
        else:
            hi = mid
    return lo


# ---------- A1: cluster invariant ----------
EPS = 0.05
CAP = 256


def leader_clusters(states):
    """Greedy leader clustering in L-inf, eps = 0.05, within each DFA state, in recorded order."""
    cl = []
    for q in sorted(states):
        mine = []
        for h in states[q]:
            for c in mine:
                if np.max(np.abs(h - c["leader"])) <= EPS:
                    c["members"].append(h)
                    break
            else:
                mine.append({"pi": q, "leader": h, "members": [h]})
        cl += mine
    return cl


def contains(lo, hi, BL, BH):
    return all(bl <= l for l, bl in zip(lo, BL)) and all(u <= bh for u, bh in zip(hi, BH))


def cluster_search(qp, lang, tau, states, max_rounds=200):
    delta, q0, accset = DFAS[lang]
    cl = leader_clusters(states)
    nC = len(cl)
    if nC > CAP:
        return {"fail": True, "nC": nC, "over_cap": True}
    d = qp["W"].shape[0]
    c0 = next(i for i, c in enumerate(cl) if c["pi"] == q0 and np.max(np.abs(c["leader"])) <= EPS)
    for m in MARGINS:
        B = []
        for c in cl:
            S = np.array(c["members"])
            B.append(([max(F(0), down(F(float(x)) - m)) for x in S.min(0)],
                      [min(F(1), up(F(float(x)) + m)) for x in S.max(0)]))
        B[c0] = ([min(x, F(0)) for x in B[c0][0]], B[c0][1])
        T = {}
        ok = False
        for _ in range(max_rounds):
            changed = False
            for i in range(nC):
                for a in (0, 1):
                    t = delta[cl[i]["pi"]][a]
                    lo, hi = cell_img(qp, tau, B[i][0], B[i][1], a)
                    cands = [j for j in range(nC) if cl[j]["pi"] == t]
                    inside = [j for j in cands if contains(lo, hi, B[j][0], B[j][1])]
                    if inside:
                        T[(i, a)] = inside[0]
                        continue
                    ctr = [float(l + u) / 2 for l, u in zip(lo, hi)]
                    j = min(cands, key=lambda j: max(abs(ctr[k] - float(B[j][0][k] + B[j][1][k]) / 2)
                                                     for k in range(d)))
                    B[j] = ([down(min(l, bl)) for l, bl in zip(lo, B[j][0])],
                            [up(max(u, bu)) for u, bu in zip(hi, B[j][1])])
                    T[(i, a)] = j
                    changed = True
            if any(not read_ok(qp, tau, B[i][0], B[i][1], cl[i]["pi"] in accset) for i in range(nC)):
                break
            if not changed:
                ok = True
                break
        if ok:
            return {"B": B, "T": T, "pi": [c["pi"] for c in cl], "c0": c0, "nC": nC, "m": m}
    return {"fail": True, "nC": nC}


def cluster_max_tau(qp, lang, states, hi=F(1, 20), iters=12):
    lo = F(0)
    if cluster_search(qp, lang, F(0), states).get("fail"):
        return F(0)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if not cluster_search(qp, lang, mid, states).get("fail"):
            lo = mid
        else:
            hi = mid
    return lo


# ---------- one net ----------
def one(lang, arm, d, seed, ws, do_tau=True):
    t0 = time.time()
    qp = quantize(train(lang, arm, d, seed))
    ok, n = gate(qp, lang, ws)
    rec = {"lang": lang, "arm": arm, "d": d, "seed": seed, "gate": ok, "gate_n": n, "exact": ok == n}
    states = {}
    run_float(floats(qp), ws, collect=states, lang=lang)
    if rec["exact"] or arm == "RND":
        r = cluster_search(qp, lang, TAU, states)
        rec["n_clusters"] = r["nC"]
        rec["cert_py"] = not r.get("fail")
        if r.get("over_cap"):
            rec["over_cap"] = True
        if rec["cert_py"]:
            rec["margin"] = str(r["m"])
            rec["cert_size"] = {"boxes": r["nC"], "step_checks": 2 * r["nC"], "read_checks": r["nC"]}
            rec["clust"] = {"B": [([str(x) for x in lo], [str(x) for x in hi]) for lo, hi in r["B"]],
                            "T": [[r["T"][(i, a)] for a in (0, 1)] for i in range(r["nC"])],
                            "pi": r["pi"], "c0": r["c0"]}
            if do_tau:
                rec["max_tau"] = float(cluster_max_tau(qp, lang, states))
    rec["sec"] = round(time.time() - t0, 1)
    NETS.mkdir(exist_ok=True)
    name = f"{lang}_{arm}_d{d}_s{seed}"
    (NETS / f"{name}.json").write_text(json.dumps({"qp": {k: v.tolist() for k, v in qp.items()}, "rec": rec}))
    return rec


def dev(a):
    OUT.mkdir(exist_ok=True)
    ws = gate_strings()
    with open(OUT / "rnncert_dev.jsonl", "w") as f:
        for lang in ("L1", "L2", "L3"):
            chosen = None
            for d in (4, 8, 16):
                recs = [one(lang, "ORD", d, s, ws, do_tau=False) for s in range(4)]
                for r in recs:
                    f.write(json.dumps({k: v for k, v in r.items() if k not in ("boxes", "clust")}) + "\n"); f.flush()
                    print({k: v for k, v in r.items() if k not in ("boxes", "clust")}, flush=True)
                if sum(r["exact"] for r in recs) >= 3:
                    chosen = d
                    break
            f.write(json.dumps({"lang": lang, "chosen_d": chosen}) + "\n"); f.flush()
            print(lang, "CHOSEN d", chosen, flush=True)
            if chosen:
                for s in range(4):
                    r = one(lang, "SAT", chosen, s, ws, do_tau=False)
                    f.write(json.dumps({k: v for k, v in r.items() if k not in ("boxes", "clust")}) + "\n"); f.flush()
                    print({k: v for k, v in r.items() if k not in ("boxes", "clust")}, flush=True)


def dev2(a):
    """Second dev run under A1: same dev seeds, widths fixed from the first dev run."""
    ws = gate_strings()
    with open(OUT / "rnncert_dev2.jsonl", "w") as f:
        for lang, d in (("L1", 8), ("L2", 16), ("L3", 8)):
            for arm in ("ORD", "SAT"):
                for s in range(4):
                    r = one(lang, arm, d, s, ws, do_tau=False)
                    r = {k: v for k, v in r.items() if k not in ("boxes", "clust")}
                    f.write(json.dumps(r) + "\n"); f.flush()
                    print(r, flush=True)


def test(a):
    ws = gate_strings()
    with open(OUT / f"rnncert_test_{a.lang}.jsonl", "w") as f:
        for arm in ("ORD", "SAT", "RND"):
            for s in range(100, 108):
                r = one(a.lang, arm, a.d, s, ws, do_tau=arm != "RND")
                f.write(json.dumps({k: v for k, v in r.items() if k not in ("boxes", "clust")}) + "\n"); f.flush()
                print({k: v for k, v in r.items() if k not in ("boxes", "clust")}, flush=True)


# ---------- Lean export ----------
def qs(x):
    x = F(x)
    return f"({x.numerator}/{x.denominator} : ℚ)" if x >= 0 else f"(-{-x.numerator}/{x.denominator} : ℚ)"


def export(a):
    dat = json.loads((NETS / f"{a.name}.json").read_text())
    qp = {k: np.array(v) for k, v in dat["qp"].items()}
    rec = dat["rec"]
    lang, d = rec["lang"], rec["d"]
    delta, q0, accset = DFAS[lang]
    nQ = len(delta)
    Wr, br = cell_rows(qp)
    lay = lambda rows, bs: "⟨[" + ", ".join("[" + ", ".join(qs(F(int(x), Q)) for x in r) + "]" for r in rows) + \
        "], [" + ", ".join(qs(F(int(x), Q)) for x in bs) + "]⟩"
    boxes = rec["boxes"]
    Bl = "[" + ", ".join("([" + ", ".join(qs(F(x)) for x in boxes[str(q)][0]) + "], [" +
                         ", ".join(qs(F(x)) for x in boxes[str(q)][1]) + "])" for q in range(nQ)) + "]"
    ident = a.name.replace("-", "_")
    tau = f"({TAU.numerator}/{TAU.denominator} : ℚ)"
    src = f"""import Bridge.RNN
open Lane4 Bridge

def C_{ident} : Layer := {lay(Wr, br)}
def R_{ident} : Layer := {lay([list(qp['v'])], [int(qp['c'][0])])}
def δ_{ident} (q a : ℕ) : ℕ := ({json.dumps(delta)} : List (List ℕ)).getD q [] |>.getD a 0
def acc_{ident} (q : ℕ) : Bool := ({json.dumps([q in accset for q in range(nQ)]).lower()} : List Bool).getD q false
def B_{ident} : List (List ℚ × List ℚ) := {Bl}

theorem cert_{ident} : RSpec C_{ident} R_{ident} 2 {d} δ_{ident} {q0} acc_{ident} {tau} :=
  certR C_{ident} R_{ident} 2 {d} {nQ} δ_{ident} {q0} acc_{ident} {tau} B_{ident} (by decide +kernel)

#print axioms cert_{ident}
"""
    LEAN.mkdir(parents=True, exist_ok=True)
    out = LEAN / f"RNN_{ident}.lean"
    out.write_text(src, encoding="utf-8")
    print(out)


def export_clust(a):
    dat = json.loads((NETS / f"{a.name}.json").read_text())
    qp = {k: np.array(v) for k, v in dat["qp"].items()}
    rec = dat["rec"]
    cl = rec["clust"]
    lang, d = rec["lang"], rec["d"]
    delta, q0, accset = DFAS[lang]
    nQ, nC = len(delta), len(cl["pi"])
    Wr, br = cell_rows(qp)

    def lay(rows, bs):
        return ("⟨[" + ", ".join("[" + ", ".join(qs(F(int(x), Q)) for x in r) + "]" for r in rows) +
                "], [" + ", ".join(qs(F(int(x), Q)) for x in bs) + "]⟩")
    Bl = "[" + ", ".join("([" + ", ".join(qs(F(x)) for x in lo) + "], [" + ", ".join(qs(F(x)) for x in hi) + "])"
                         for lo, hi in cl["B"]) + "]"
    ident = a.name.replace("-", "_")
    tau = f"({TAU.numerator}/{TAU.denominator} : ℚ)"
    acc_l = json.dumps([q in accset for q in range(nQ)]).lower()
    lines = [
        "import Bridge.RNNClust",
        "open Lane4 Bridge",
        "",
        f"def C_{ident} : Layer := {lay(Wr, br)}",
        f"def R_{ident} : Layer := {lay([list(qp['v'])], [int(qp['c'][0])])}",
        f"def δ_{ident} (q a : ℕ) : ℕ := ({json.dumps(delta)} : List (List ℕ)).getD q [] |>.getD a 0",
        f"def acc_{ident} (q : ℕ) : Bool := ({acc_l} : List Bool).getD q false",
        f"def T_{ident} (c a : ℕ) : ℕ := ({json.dumps(cl['T'])} : List (List ℕ)).getD c [] |>.getD a 0",
        f"def π_{ident} (c : ℕ) : ℕ := ({json.dumps(cl['pi'])} : List ℕ).getD c 0",
        f"def B_{ident} : List (List ℚ × List ℚ) := {Bl}",
        "",
        f"theorem cert_{ident} : RSpec C_{ident} R_{ident} 2 {d} δ_{ident} {q0} acc_{ident} {tau} :=",
        f"  certClust C_{ident} R_{ident} 2 {d} {nC} T_{ident} {cl['c0']} π_{ident} δ_{ident} {q0} acc_{ident} {tau} B_{ident}",
        "    (by decide +kernel) (by decide +kernel)",
        "",
        f"#print axioms cert_{ident}",
        "",
    ]
    LEAN.mkdir(parents=True, exist_ok=True)
    out = LEAN / f"RNNC_{ident}.lean"
    out.write_text("\n".join(lines), encoding="utf-8")
    print(out)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["dev", "dev2", "test", "export", "export_clust"])
    ap.add_argument("name", nargs="?")
    ap.add_argument("--lang", default="L1")
    ap.add_argument("--d", type=int, default=8)
    a = ap.parse_args()
    {"dev": dev, "dev2": dev2, "test": test, "export": export, "export_clust": export_clust}[a.cmd](a)
