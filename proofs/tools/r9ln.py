"""Rung 9-LN: train and screen ONE-block ungated softmax transformers WITH LayerNorm (pre-LN block and a final
LayerNorm) on rung 8's task A (PREREG_R9LN.md). CPU, torch float32, 2 threads.
Edits no frozen file; imports the frozen tools/r7.py for the task, base hyper-parameters,
export helpers and tolerance, and tools/r6net.py for the attention evaluator.

    python tools/r9ln.py sweep <recipe> <seed0> <seed1> [--out runs/r9ln-tune]
    python tools/r9ln.py selftest        60 steps on dev seed 0 into scratch/ (code check; result discarded)

Network (to be formalised in Lean after K2): state width 8, two heads (strict, causal), every earlier position a
candidate key, relative-position slope 24, MLP hidden 12, scalar read-out.
    h   = LN1(x)                                   x = token embedding (no position embedding)
    y   = x + sum over heads of attention(h)       scores, keys and values all read h
    z   = y + W2 relu(W1 LN2(y) + b1) + b2
    out = oW . LNf(z) + oB
LN(v) = (v - mean v) / sqrt(mean (v - mean v)^2 + 1e-5) * gain + bias, with a learned gain and bias per
coordinate. Stated float order (run()): mean = left-to-right sum / D; centred; mean square the same way; add
eps; square root; divide; times gain; plus bias; every operation rounded to the dtype.
"""
import json, math, os, sys, time
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r7, r6net as R, r4_checks as C4, r5_checks as C5

HERE = r7.HERE
MASKS, TOL, D, H, G = r7.MASKS, r7.TOL, 8, 12, 14
EPS = 1e-5
C = r7.task("A")
target = lambda w: r7.target(C, w)
LNS = ("ln1", "ln2", "lnf")

U3 = dict(grid=None, snap=1 / 1024, l1=3e-4, l1_all=True, learn_slope=False, band_w=1.0)   # = r7.RECIPES["u3"]
RECIPES = {
    "n1": dict(U3, steps=6000),
    "n2": dict(U3, steps=6000, l1=1e-4),
    "n3": dict(U3, steps=12000, l1=1e-4),
}


def train(rname, seed, out, steps=None):
    import torch
    torch.set_num_threads(2)
    hp = dict(r7.BASE, **RECIPES[rname])
    if steps: hp["steps"] = steps
    K = len(MASKS)
    g = torch.Generator().manual_seed(seed)
    par = lambda *sh, sc: torch.nn.Parameter(torch.randn(*sh, generator=g) * sc)
    zer = lambda *sh: torch.nn.Parameter(torch.zeros(*sh))
    one = lambda *sh: torch.nn.Parameter(torch.ones(*sh))
    Pm = {"E": par(C["V"] + 1, D, sc=0.5), "A": par(K, D, D, sc=0.05), "V": par(K, D, D, sc=0.3),
          "W1": par(H, D, sc=0.4), "b1": zer(H), "W2": par(D, H, sc=0.3), "b2": zer(D), "oW": par(D, sc=0.3), "oB": zer(1)}
    for n in LNS:
        Pm[n + "g"], Pm[n + "b"] = one(D), zer(D)
    opt = torch.optim.Adam(Pm.values(), lr=hp["lr"])
    rng = np.random.default_rng(10_000 + seed)

    def ln(x, n):
        c = x - x.mean(-1, keepdim=True)
        return c / torch.sqrt((c * c).mean(-1, keepdim=True) + EPS) * Pm[n + "g"] + Pm[n + "b"]

    def forward(toks, slope):
        X = Pm["E"][toks]
        n = toks.shape[1]
        idx = torch.arange(n)
        rel = (idx[None, :] - idx[:, None]).float()
        Hh = ln(X, "ln1")
        Y = X
        for k, mask in enumerate(MASKS):
            sc = slope * rel[None] + torch.einsum("bid,de,bje->bij", Hh, Pm["A"][k], Hh)
            ok = ((rel <= 0) if mask == "causal" else (rel < 0))[None].expand(toks.shape[0], n, n)
            att = torch.softmax(sc.masked_fill(~ok, -1e30), dim=-1) * ok.float()
            Y = Y + att @ (Hh @ Pm["V"][k].T)
        Z = Y + torch.relu(ln(Y, "ln2") @ Pm["W1"].T + Pm["b1"]) @ Pm["W2"].T + Pm["b2"]
        return ln(Z, "lnf") @ Pm["oW"] + Pm["oB"]

    def batch(n, B):
        ws = [C4.gen_input(C, n, rng) for _ in range(B)]
        toks = torch.tensor(np.stack([np.concatenate([[0], w]) for w in ws]), dtype=torch.long)
        tg = torch.tensor(np.array([target(w) for w in ws]), dtype=torch.float32)
        return toks, tg

    S, t0, log = hp["steps"], time.time(), []
    for step in range(S):
        f = step / S
        slope = hp["slope0"] + (hp["slope"] - hp["slope0"]) * min(1.0, f / 0.3)
        lr = hp["lr"] * (1.0 if f < 0.5 else 0.5 * (1 + math.cos(math.pi * (f - 0.5) / 0.5)) * 0.99 + 0.01)
        for gr in opt.param_groups:
            gr["lr"] = lr
        toks, tg = batch(int(rng.integers(2, hp["nmax"] + 1)), hp["batch"])
        y = forward(toks, slope)
        loss = (torch.relu((y[:, 1:] - tg).abs() - hp["hinge"]) ** 2).mean()
        opt.zero_grad(); loss.backward(); opt.step()
        if hp["l1"]:
            with torch.no_grad():
                th = lr * hp["l1"] * 100
                for k, p in Pm.items():
                    if not k.startswith("ln"):            # the LayerNorm gains and biases are not shrunk
                        p.copy_(torch.sign(p) * torch.relu(p.abs() - th))
        if step % 500 == 0 or step == S - 1:
            with torch.no_grad():
                toks, tg = batch(hp["nmax"], 64)
                log.append({"step": step, "loss": float(loss), "max_dev": float((forward(toks, slope)[:, 1:] - tg).abs().max())})
    q = lambda t: ["%d/%d" % F(float(v)).as_integer_ratio() for v in t.detach().reshape(-1).tolist()]
    M = lambda t: [q(r) for r in t.detach()]
    heads = [{"A": M(Pm["A"][k]), "V": M(Pm["V"][k]), "mask": mask, "m": "%d/1" % int(hp["slope"]), "g": ["0/1"] * D, "gb": "-1/1"}
             for k, mask in enumerate(MASKS)]
    net = {"embed": M(Pm["E"]), "blocks": [{"heads": heads, "W1": M(Pm["W1"]), "b1": q(Pm["b1"]), "W2": M(Pm["W2"]), "b2": q(Pm["b2"])}],
           "outW": q(Pm["oW"]), "outB": q(Pm["oB"])[0], "ln": {n: {"g": q(Pm[n + "g"]), "b": q(Pm[n + "b"])} for n in LNS}}
    d = os.path.join(out, "A", rname, "s%03d" % seed)
    os.makedirs(d, exist_ok=True)
    json.dump(net, open(os.path.join(d, "T.json"), "w"))
    json.dump({"task": "A", "arch": "ln", "recipe": rname, "seed": seed, "hp": hp, "log": log, "secs": time.time() - t0,
               "torch": torch.__version__}, open(os.path.join(d, "train.json"), "w"), indent=1)
    return d


def fmap(net, f):
    out = r7.fmap(net, f)
    out["ln"] = {n: {"g": [f(v) for v in net["ln"][n]["g"]], "b": [f(v) for v in net["ln"][n]["b"]]} for n in LNS}
    return out


def flat(net):
    out = []
    fmap(net, lambda v: out.append(F(v)) or v)
    return out


def lnorm(X, g, b, dt):
    """LayerNorm in the stated order, every operation rounded to dt. X: (n, D)."""
    one = dt.type
    acc = np.zeros(X.shape[0], dtype=dt)
    for k in range(X.shape[1]): acc = acc + X[:, k]
    mean = (acc / one(X.shape[1])).astype(dt)
    Cn = (X - mean[:, None]).astype(dt)
    acc = np.zeros(X.shape[0], dtype=dt)
    for k in range(X.shape[1]): acc = acc + (Cn[:, k] * Cn[:, k]).astype(dt)
    s = np.sqrt(((acc / one(X.shape[1])).astype(dt) + one(EPS)).astype(dt)).astype(dt)
    return (((Cn / s[:, None]).astype(dt) * g[None, :]).astype(dt) + b[None, :]).astype(dt)


def run(net, w, pert=None, dtype=np.float32, queries=None):
    """Forward pass in the stated order. pert: additive offsets, layout of tools/r6net.py plus pert["ln"]."""
    dt = np.dtype(dtype)
    S = R.stored(net, pert, dt)
    assert len(S["blocks"]) == 1
    pl = (pert or {}).get("ln", {})
    L = {n: tuple((np.array(net["ln"][n][k], dtype=np.float64) + (np.array(pl[n][k], dtype=np.float64) if n in pl else 0.0)).astype(dt)
                  for k in ("g", "b")) for n in LNS}
    toks = np.concatenate([[0], np.asarray(w, dtype=np.int64)])
    X = S["embed"][toks]
    Q = np.arange(1, len(toks)) if queries is None else np.asarray(queries, dtype=np.int64)
    Hh = lnorm(X, *L["ln1"], dt)
    B = S["blocks"][0]
    Y = X[Q].copy()
    for h in B["heads"]:
        Y = Y + R.attend(h, Hh, Q)
    hid = np.maximum(R.rmat(B["W1"], lnorm(Y, *L["ln2"], dt)) + B["b1"][None, :], dt.type(0))
    Z = Y + (R.rmat(B["W2"], hid) + B["b2"][None, :])
    return (R.rdot(S["outW"], lnorm(Z, *L["lnf"], dt)) + S["outB"]).astype(np.float64)


def random_pert(net, delta, rng, kind="sign"):
    p = R.random_pert(net, delta, rng, kind)
    draw = (lambda: rng.uniform(-delta, delta, D)) if kind == "uniform" else (lambda: delta * rng.choice([-1.0, 1.0], D))
    p["ln"] = {n: {"g": draw(), "b": draw()} for n in LNS}
    return p


def screen(d):
    """Screen 9-LN = s1 and s3' with the sampling plans of the frozen rung-7 s1 and the rung-8 s3'."""
    tj = json.load(open(os.path.join(d, "train.json")))
    s = F(1, 2 ** G)
    Tq = json.load(open(os.path.join(d, "T.json")))
    Wq = fmap(Tq, lambda v: "%d/%d" % (round(F(v) / s) * s).as_integer_ratio())
    json.dump(Wq, open(os.path.join(d, "W14.json"), "w"))
    T, W = fmap(Tq, lambda v: float(F(v))), fmap(Wq, lambda v: float(F(v)))
    a, b = flat(Tq), flat(Wq)
    res = {"task": "A", "arch": "ln", "recipe": tj["recipe"], "seed": tj["seed"], "weights": len(b),
           "nonzero_W14": sum(1 for y in b if y != 0), "max_abs_W14": float(max(abs(y) for y in b)),
           "delta_T": float(max(abs(x - y) for x, y in zip(a, b)))}

    def dev(net, w, pert, dtype, q):
        y = run(net, w, pert, dtype, q)
        return float(np.max(np.abs(y - np.array(target(w), dtype=np.float64)[q - 1])))
    rng = np.random.default_rng(71)
    gen = lambda n: C4.gen_input(C, n, rng)
    worst = 0.0
    for n in (6, 40, 300):
        for _ in range(10):
            w = gen(n)
            worst = max(worst, dev(T, w, None, np.float32, np.arange(1, n + 1)))
    res["T_f32_dev_to_300"] = worst
    if worst <= TOL:
        for n in (2000, 2000, 2000, 16000, 65534):
            w = gen(n)
            worst = max(worst, dev(T, w, None, np.float32, C4.queries(n, rng, cap=2000)))
        res["T_f32_dev_to_65534"] = worst
    res["T_f32_dev"] = worst
    res["s1_ok"] = bool(worst <= TOL)
    if not res["s1_ok"]:
        res["pass"] = False
        json.dump(res, open(os.path.join(d, "screen.json"), "w"), indent=1)
        return res
    rng = np.random.default_rng(72)
    rad = 2.0 ** -G
    inside = {}
    for kind in ("uniform", "sign"):
        wi = 0.0
        for _ in range(20):
            w = gen(int(rng.choice([6, 40, 300, 2000])))
            wi = max(wi, dev(W, w, random_pert(W, rad, rng, kind), np.float64, C4.queries(len(w), rng)))
        inside[kind] = wi
    res["W14_inside_ball_dev"] = inside
    res["s3_ok"] = bool(max(inside.values()) <= 0.10)
    res["W14_breaks_at_multiple"] = None
    for mult in (2, 4, 8, 16, 32, 64, 128, 256):
        wi = 0.0
        for _ in range(10):
            w = gen(int(rng.choice([6, 40, 300, 2000])))
            wi = max(wi, dev(W, w, random_pert(W, mult * rad, rng, "sign"), np.float64, C4.queries(len(w), rng)))
            if wi > TOL: break
        if wi > TOL:
            res["W14_breaks_at_multiple"] = mult
            break
    res["pass"] = bool(res["s1_ok"] and res["s3_ok"])
    json.dump(res, open(os.path.join(d, "screen.json"), "w"), indent=1)
    return res


def line(d, t0):
    r = json.load(open(os.path.join(d, "screen.json")))
    tr = json.load(open(os.path.join(d, "train.json")))
    print("A-LN %s s%03d | train dev %.3f | T f32 dev %.3f | s1 %s | W14 inside 2^-14 ball %s | breaks at x%s | nnz %d/%d | SCREEN PASS %s | %.0f s" % (
        r["recipe"], r["seed"], tr["log"][-1]["max_dev"], r["T_f32_dev"], r["s1_ok"],
        ("%.3f" % max(r["W14_inside_ball_dev"].values())) if "W14_inside_ball_dev" in r else "-",
        r.get("W14_breaks_at_multiple"), r["nonzero_W14"], r["weights"], r["pass"], time.time() - t0), flush=True)


if __name__ == "__main__":
    C5.memory_guard(2.5)
    a = sys.argv
    if a[1] == "selftest":
        t0 = time.time()
        d = train("n1", 0, os.path.join(HERE, "scratch", "r9ln-selftest"), steps=60)
        screen(d); line(d, t0)
        # the numpy evaluator against torch on one input, float32
        import torch
        Tn = fmap(json.load(open(os.path.join(d, "T.json"))), lambda v: float(F(v)))
        w = np.array([1, 3, 5, 2, 2, 4, 1])
        print("numpy evaluator output", np.round(run(Tn, w), 4))
    elif a[1] == "sweep":
        out = os.path.join(HERE, a[a.index("--out") + 1] if "--out" in a else "runs/r9ln-tune")
        for seed in range(int(a[3]), int(a[4]) + 1):
            t0 = time.time()
            d = os.path.join(out, "A", a[2], "s%03d" % seed)
            if not os.path.exists(os.path.join(d, "T.json")):
                train(a[2], seed, out)
            if not os.path.exists(os.path.join(d, "screen.json")):
                screen(d)
            line(d, t0)
