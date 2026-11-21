"""Rung 7: train tiny gated / standard softmax transformers by gradient descent and screen them
for provability (PREREG_R7.md). CPU, torch float32, 2 threads. RUN UNDER reservation wrapper.

    python tools/r7.py train  <task A|B> <recipe> <seed> [--out runs/r7-stage0]
    python tools/r7.py screen <dir with T.json>          -> screen.json next to it
    python tools/r7.py sweep  <task> <recipe,recipe,...> <seed0> <seed1> [--out ...]
                                                          train + screen for each, skipping done ones

Architecture (fixed by the study team, Lane4/AGate.lean semantics): one block, state width D = 8,
two heads (masks strict, causal), relative-position slope, MLP hidden H = 12, scalar read-out.
Task A: gate parameters are the constants g = 0, gb = -1 (every key always a candidate: the
standard architecture); task B: the gate is trained.
Nothing about any written network enters: random initialisation, task data, task-agnostic
regularisers only.
"""
import copy, json, math, os, sys, time
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r6net as R, r4pool as P, r4_checks as C4, r5_checks as C5

HERE = P.HERE
D, H, MASKS = 8, 12, ("strict", "causal")
TOL = 0.25


def task(name):
    if name == "A":       # sum of the last two tokens' digits mod 5 (token t is digit t - 1; BOS counts 0)
        return {"id": "modadd5", "family": "modadd", "V": 5, "m": 5}
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
    return pool["c01"]    # B: carry, modulus 3, 5 tokens (latest non-propagate token, any distance)


def target(c, w):
    if c["family"] == "modadd":
        w = [int(t) for t in w]
        return [((w[i] - 1) + (w[i - 1] - 1 if i else 0)) % c["m"] for i in range(len(w))]
    return P.target(c, [int(t) for t in w])


# recipes: fixed before the seeds they are used on (PREREG_R7.md)
RECIPES = {
    "r1": dict(grid=0.25, l1=1e-4, learn_slope=False),
    "r2": dict(grid=0.5, l1=1e-4, learn_slope=False),
    "r3": dict(grid=0.25, l1=1e-4, learn_slope=True),
    "r4": dict(grid=None, l1=1e-4, learn_slope=False),
    "r5": dict(grid=0.25, l1=0.0, learn_slope=False),
    "r6": dict(grid=0.5, l1=3e-4, learn_slope=False),
    # stage 0a tuning candidates (dev seeds only; PREREG_R7.md Amendment 1 fixes the final set)
    "t1": dict(grid=0.125, l1=1e-4, learn_slope=False, steps=10000, grid_ramp="geo", grid_w0=0.01, grid_w=100.0,
               hinge_grid=0.08, hard_w=1.0, band_w=1.0, lr_hold=True),
    "t2": dict(grid=0.25, l1=1e-4, learn_slope=False, steps=10000, grid_ramp="geo", grid_w0=0.01, grid_w=100.0,
               hinge_grid=0.08, hard_w=1.0, band_w=1.0, lr_hold=True),
    "t3": dict(grid=0.0625, l1=1e-4, learn_slope=False, steps=10000, grid_ramp="geo", grid_w0=0.01, grid_w=100.0,
               hinge_grid=0.08, hard_w=1.0, band_w=1.0, lr_hold=True),
    # no grid penalty; skeleton = weights rounded to 1/1024; L1 kept on to the end
    "u1": dict(grid=None, snap=1 / 1024, l1=1e-4, l1_all=True, learn_slope=False, band_w=1.0),
    "u2": dict(grid=None, snap=1 / 1024, l1=1e-4, l1_all=True, learn_slope=False, band_w=1.0, hard_w=1.0, hard_from=0.6),
    "u3": dict(grid=None, snap=1 / 1024, l1=3e-4, l1_all=True, learn_slope=False, band_w=1.0),
    # as u1 / u3, with a null key in the training softmax (value 0, score one slope below key 0), so that
    # "every key penalised" trains toward the hard gate's empty-candidate output 0
    "u4": dict(grid=None, snap=1 / 1024, l1=1e-4, l1_all=True, learn_slope=False, band_w=1.0, null_key=True),
    "u5": dict(grid=None, snap=1 / 1024, l1=3e-4, l1_all=True, learn_slope=False, band_w=1.0, null_key=True),
    # learned slope (kept in the grid at the project owner's request): u6 for task A, u7 for task B
    "u6": dict(grid=None, snap=1 / 1024, l1=3e-4, l1_all=True, learn_slope=True, band_w=1.0),
    "u7": dict(grid=None, snap=1 / 1024, l1=3e-4, l1_all=True, learn_slope=True, band_w=1.0, null_key=True),
}
BASE = dict(steps=6000, batch=64, nmax=40, lr=3e-3, slope0=2.0, slope=24.0, beta0=1.0, beta=4096.0,
            band=0.25, band_w=0.1, grid_w=30.0, hinge=0.03)


def train(tname, rname, seed, out, over=None):
    import torch
    torch.set_num_threads(2)
    c = task(tname)
    hp = dict(BASE, **RECIPES[rname])
    hp.update(over or {})
    gated = tname == "B"
    K = len(MASKS)
    g = torch.Generator().manual_seed(seed)
    par = lambda *sh, sc: torch.nn.Parameter(torch.randn(*sh, generator=g) * sc)
    zer = lambda *sh: torch.nn.Parameter(torch.zeros(*sh))
    Pm = {"E": par(c["V"] + 1, D, sc=0.5), "A": par(K, D, D, sc=0.05), "V": par(K, D, D, sc=0.3),
          "W1": par(H, D, sc=0.4), "b1": zer(H), "W2": par(D, H, sc=0.3), "b2": zer(D),
          "oW": par(D, sc=0.3), "oB": zer(1)}
    if gated:
        Pm["g"], Pm["gb"] = par(K, D, sc=0.3), zer(K)
    if hp["learn_slope"]:
        Pm["m"] = torch.nn.Parameter(torch.full((K,), hp["slope0"]))
    opt = torch.optim.Adam(Pm.values(), lr=hp["lr"])
    rng = np.random.default_rng(10_000 + seed)

    def forward(toks, slope, beta, hard):
        X = Pm["E"][toks]
        n = toks.shape[1]
        idx = torch.arange(n)
        rel = (idx[None, :] - idx[:, None]).float()
        Y, pres = X, []
        for k, mask in enumerate(MASKS):
            m = Pm["m"][k] if hp["learn_slope"] else slope
            sc = m * rel[None] + torch.einsum("bid,de,bje->bij", X, Pm["A"][k], X)
            ok = ((rel <= 0) if mask == "causal" else (rel < 0))[None].expand(toks.shape[0], n, n)
            if gated:
                pre = X @ Pm["g"][k] + Pm["gb"][k]
                pres.append(pre)
                if hard:
                    ok = ok & (torch.relu(pre) == 0)[:, None, :]
                else:
                    sc = sc - beta * torch.relu(pre)[:, None, :]
            scm = sc.masked_fill(~ok, -1e30)
            if gated and hp.get("null_key") and not hard:
                null = (m * (-(idx.float() + 1)))[None, :, None].expand(toks.shape[0], n, 1)
                att = torch.softmax(torch.cat([scm, null], dim=-1), dim=-1)[:, :, :n] * ok.float()
            else:
                att = torch.softmax(scm, dim=-1) * ok.float()
            Y = Y + att @ (X @ Pm["V"][k].T)
        Y = Y + torch.relu(Y @ Pm["W1"].T + Pm["b1"]) @ Pm["W2"].T + Pm["b2"]
        return Y @ Pm["oW"] + Pm["oB"], pres

    def batch(n, B):
        ws = [C4.gen_input(c, n, rng) for _ in range(B)]
        toks = torch.tensor(np.stack([np.concatenate([[0], w]) for w in ws]), dtype=torch.long)
        tg = torch.tensor(np.array([target(c, w) for w in ws]), dtype=torch.float32)
        return toks, tg

    def grid_dist2(s):
        tot = 0.0
        for k, p in Pm.items():
            tot = tot + ((p - torch.round(p / s) * s) ** 2).sum()
        return tot

    S, t0, log = hp["steps"], time.time(), []
    for step in range(S):
        f = step / S
        slope = hp["slope0"] + (hp["slope"] - hp["slope0"]) * min(1.0, f / 0.3)
        beta = hp["beta0"] * (hp["beta"] / hp["beta0"]) ** min(1.0, f / 0.5)
        if hp.get("lr_hold"):
            lr = hp["lr"] * (1.0 if f < 0.5 else 0.3 if f < 0.9 else 0.3 * (0.5 * (1 + math.cos(math.pi * (f - 0.9) / 0.1)) * 0.97 + 0.03))
        else:
            lr = hp["lr"] * (1.0 if f < 0.5 else 0.5 * (1 + math.cos(math.pi * (f - 0.5) / 0.5)) * 0.99 + 0.01)
        for gr in opt.param_groups:
            gr["lr"] = lr
        toks, tg = batch(int(rng.integers(2, hp["nmax"] + 1)), hp["batch"])
        y, pres = forward(toks, slope, beta, False)
        hinge = hp["hinge_grid"] if (hp.get("hinge_grid") and f >= 0.5) else hp["hinge"]
        loss = (torch.relu((y[:, 1:] - tg).abs() - hinge) ** 2).mean()
        if gated and hp.get("hard_w") and f >= hp.get("hard_from", 0.25):
            yh, _ = forward(toks, slope, beta, True)
            loss = loss + hp["hard_w"] * (torch.relu((yh[:, 1:] - tg).abs() - hinge) ** 2).mean()
        reg = 0.0
        for pre in pres:
            reg = reg + hp["band_w"] * torch.relu(hp["band"] - pre.abs()).mean()
        if hp["learn_slope"]:
            reg = reg + 0.01 * torch.relu(hp["slope"] - Pm["m"]).sum()
        if hp["grid"] and f >= 0.5:
            if hp.get("grid_ramp") == "geo":
                gw = hp["grid_w0"] * (hp["grid_w"] / hp["grid_w0"]) ** min(1.0, (f - 0.5) / 0.4)
            else:
                gw = hp["grid_w"] * min(1.0, (f - 0.5) / 0.3) * (10.0 if f >= 0.9 else 1.0)
            reg = reg + gw * grid_dist2(hp["grid"])
        opt.zero_grad()
        (loss + reg).backward()
        opt.step()
        if hp["l1"] and (f < 0.5 or hp.get("l1_all")):
            with torch.no_grad():
                th = lr * hp["l1"] * 100
                for k, p in Pm.items():
                    if k != "m":
                        p.copy_(torch.sign(p) * torch.relu(p.abs() - th))
        if step % 500 == 0 or step == S - 1:
            with torch.no_grad():
                toks, tg = batch(hp["nmax"], 64)
                yh, _ = forward(toks, slope, beta, True)
                log.append({"step": step, "loss": float(loss), "hard_max_dev": float((yh[:, 1:] - tg).abs().max())})
    # exact export of the float32 weights as trained
    q = lambda t: ["%d/%d" % F(float(v)).as_integer_ratio() for v in t.detach().reshape(-1).tolist()]
    M = lambda t: [q(r) for r in t.detach()]
    heads = []
    for k, mask in enumerate(MASKS):
        heads.append({"A": M(Pm["A"][k]), "V": M(Pm["V"][k]), "mask": mask,
                      "m": q(Pm["m"][k])[0] if hp["learn_slope"] else "%d/1" % int(hp["slope"]),
                      "g": q(Pm["g"][k]) if gated else ["0/1"] * D,
                      "gb": q(Pm["gb"][k])[0] if gated else "-1/1"})
    net = {"embed": M(Pm["E"]), "blocks": [{"heads": heads, "W1": M(Pm["W1"]), "b1": q(Pm["b1"]),
                                            "W2": M(Pm["W2"]), "b2": q(Pm["b2"])}],
           "outW": q(Pm["oW"]), "outB": q(Pm["oB"])[0]}
    d = os.path.join(out, tname, rname, "s%03d" % seed)
    os.makedirs(d, exist_ok=True)
    json.dump(net, open(os.path.join(d, "T.json"), "w"))
    json.dump({"task": tname, "recipe": rname, "seed": seed, "hp": hp, "log": log, "secs": time.time() - t0,
               "torch": torch.__version__}, open(os.path.join(d, "train.json"), "w"), indent=1)
    return d


def fmap(net, f):
    """Apply f to every numeric weight (Fraction strings); masks kept."""
    M = lambda m: [[f(v) for v in r] for r in m]
    return {"embed": M(net["embed"]), "outW": [f(v) for v in net["outW"]], "outB": f(net["outB"]),
            "blocks": [{"heads": [{"A": M(h["A"]), "V": M(h["V"]), "mask": h["mask"], "m": f(h["m"]),
                                   "g": [f(v) for v in h["g"]], "gb": f(h["gb"])} for h in B["heads"]],
                        "W1": M(B["W1"]), "b1": [f(v) for v in B["b1"]], "W2": M(B["W2"]),
                        "b2": [f(v) for v in B["b2"]]} for B in net["blocks"]]}


def flat(net):
    out = []
    fmap(net, lambda v: out.append(F(v)) or v)
    return out


def screen(d):
    """The frozen provability screen (PREREG_R7.md, 'Screen'). Writes screen.json and W.json."""
    tj = json.load(open(os.path.join(d, "train.json")))
    c = task(tj["task"])
    s = F(tj["hp"].get("snap") or tj["hp"]["grid"] or 0.25)
    Tq = json.load(open(os.path.join(d, "T.json")))
    Wq = fmap(Tq, lambda v: "%d/%d" % (round(F(v) / s) * s).as_integer_ratio())
    json.dump(Wq, open(os.path.join(d, "W.json"), "w"))
    tf = lambda net: fmap(net, lambda v: float(F(v)))
    T, W = tf(Tq), tf(Wq)
    for B in T["blocks"] + W["blocks"]:
        B["W1"] = np.array(B["W1"], float).reshape(H, D).tolist()
    a, b = flat(Tq), flat(Wq)
    delta_T = float(max(abs(x - y) for x, y in zip(a, b)))
    res = {"task": tj["task"], "recipe": tj["recipe"], "seed": tj["seed"], "delta_T": delta_T,
           "nonzero_W": sum(1 for y in b if y != 0), "weights": len(b),
           "max_abs_W": float(max(abs(y) for y in b))}
    rng = np.random.default_rng(71)
    tg = lambda w: target(c, w)

    def dev(net, w, pert, dtype, q):
        y = R.run(net, w, pert, dtype, q)
        return float(np.max(np.abs(y - np.array(tg(w), dtype=np.float64)[q - 1])))
    gen = lambda n: C4.gen_input(c, n, rng)
    # s1 (short part first: cheap exit)
    worst = 0.0
    for n in (6, 40, 300):
        for _ in range(10):
            w = gen(n)
            worst = max(worst, dev(T, w, None, np.float32, np.arange(1, n + 1)))
    res["T_f32_dev_to_300"] = worst
    res["s2_delta_ok"] = bool(delta_T <= 4 / 1000)
    if worst > TOL or not res["s2_delta_ok"]:
        res["s1_ok"], res["pass"], res["stopped_early"] = bool(worst <= TOL), False, True
        # still report how far the snapped skeleton is from working, cheaply
        res["W_f64_dev_to_300"] = max(dev(W, gen(n), None, np.float64, np.arange(1, n + 1)) for n in (6, 40, 300) for _ in range(5))
        json.dump(res, open(os.path.join(d, "screen.json"), "w"), indent=1)
        return res
    for n in (2000, 2000, 2000, 16000, 65534):
        w = gen(n)
        worst = max(worst, dev(T, w, None, np.float32, C4.queries(n, rng, cap=2000)))
    res["T_f32_dev_to_65534"] = worst
    res["s1_ok"] = bool(worst <= TOL)
    dball = next(k / 1000 for k in (1, 2, 4) if delta_T <= k / 1000)
    res["delta_ball"] = dball
    inside = {}
    for kind in ("uniform", "sign"):
        wi = 0.0
        for _ in range(20):
            w = gen(int(rng.choice([6, 40, 300, 2000])))
            wi = max(wi, dev(W, w, R.random_pert(W, dball, rng, kind), np.float64, C4.queries(len(w), rng)))
        inside[kind] = wi
    res["W_inside_ball_dev"] = inside
    res["s3_ok"] = bool(max(inside.values()) <= 0.10)
    res["W_breaks_at_multiple"] = None
    for mult in (2, 4, 8, 16, 32, 64):
        wi = 0.0
        for _ in range(10):
            w = gen(int(rng.choice([6, 40, 300, 2000])))
            wi = max(wi, dev(W, w, R.random_pert(W, mult * dball, rng, "sign"), np.float64, C4.queries(len(w), rng)))
            if wi > TOL:
                break
        if wi > TOL:
            res["W_breaks_at_multiple"] = mult
            break
    res["pass"] = bool(res["s1_ok"] and res["s2_delta_ok"] and res["s3_ok"])
    json.dump(res, open(os.path.join(d, "screen.json"), "w"), indent=1)
    return res


if __name__ == "__main__":
    C5.memory_guard(2.5)
    a = sys.argv
    out = os.path.join(HERE, a[a.index("--out") + 1] if "--out" in a else "runs/r7-stage0")
    over = json.loads(a[a.index("--hp") + 1]) if "--hp" in a else None
    if a[1] == "train":
        print(train(a[2], a[3], int(a[4]), out, over))
    elif a[1] == "screen":
        print(json.dumps(screen(os.path.abspath(a[2]))))
    elif a[1] == "sweep":
        for seed in range(int(a[4]), int(a[5]) + 1):
            for rname in a[3].split(","):
                d = os.path.join(out, a[2], rname, "s%03d" % seed)
                t0 = time.time()
                if not os.path.exists(os.path.join(d, "T.json")):
                    train(a[2], rname, seed, out, over)
                if not os.path.exists(os.path.join(d, "screen.json")):
                    screen(d)
                r = json.load(open(os.path.join(d, "screen.json")))
                tr = json.load(open(os.path.join(d, "train.json")))
                print("%s %s s%03d | train hard dev %.3f | T f32 dev %.3f | delta_T %.5f | nnz %d/%d | W inside %s | breaks %s | PASS %s | %.0f s" % (
                    a[2], rname, seed, tr["log"][-1]["hard_max_dev"], r.get("T_f32_dev_to_65534", r["T_f32_dev_to_300"]), r["delta_T"],
                    r["nonzero_W"], r["weights"], ("%.3f" % max(r["W_inside_ball_dev"].values())) if "W_inside_ball_dev" in r else
                    ("skel %.2f" % r.get("W_f64_dev_to_300", -1)), r.get("W_breaks_at_multiple"), r["pass"], time.time() - t0), flush=True)
