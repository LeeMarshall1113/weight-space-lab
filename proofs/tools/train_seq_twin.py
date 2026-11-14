"""Rung-2 trained twins (PREREG_R2.md, twin arm). numpy only, CPU, 2 threads.

    python tools/train_seq_twin.py gradcheck
    python tools/train_seq_twin.py dev|test          -> results/seq-twins-<split>.json

For each case: take the shape of the net-arm solution (embedding width, heads per block,
MLP width per block; default 2 blocks x 2 heads, embedding 8, MLP 32 if the net arm did
not pass), train a SOFTMAX-attention transformer of that shape on random inputs of length
1-10 (seeds 0,1,2), then HARDEN it (average-hard attention, weights rounded to 1/1024) and
evaluate the hardened network in float64 on 200 random inputs per length band:
1-10, 11-20, 21-40, exactly 100. Also reported: the soft network's accuracy per band, so a
failure caused by hardening can be told apart from a failure to generalise.

Correct means: classification families, the sign of the output at the last position
matches; sequence families, every position's output rounds to the right integer
(|out - target| < 1/2), which is more lenient than the exact equality asked of doctors.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")
import glob, json, math, re, sys
import numpy as np

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STEPS, BATCH, LR, DEN, TRAIN_MAX, N_EVAL = 20000, 64, 3e-3, 1024, 10, 200
BANDS = [("1-10", 1, 10), ("11-20", 11, 20), ("21-40", 21, 40), ("100", 100, 100)]
MASKS = ["all", "causal", "strict"]


# ---------- task semantics and samplers ----------

def target(c, w):
    """Classification: +1/-1. Sequence: list of ints, one per input position."""
    fam = c["family"]
    if fam == "parity":
        return 1 if sum(t in c["S"] for t in w) % 2 == c["target"] else -1
    if fam == "dyck":
        pre, ok = 0, True
        for t in w:
            pre += c["wt"][t - 1]
            ok = ok and pre >= 0
        return 1 if (ok and pre == 0) else -1
    if fam == "sort":
        return sorted(w)
    b, carry, out = c["base"], 0, []
    for t in w:
        a, d = divmod(t - 1, b)
        out.append((a + d + carry) % b)
        carry = (a + d + carry) // b
    return out


def sample(c, L, rng):
    V = c["V"]
    if c["family"] == "dyck" and rng.random() < 0.5:
        # try to draw an accepted string: a constrained random walk back to 0
        wt = c["wt"]
        w, pre = [], 0
        for k in range(L):
            rem = L - k - 1
            ok = [t for t in range(1, V + 1) if 0 <= pre + wt[t - 1] <= rem]
            if 0 not in wt:
                ok = [t for t in ok if (rem - (pre + wt[t - 1])) % 2 == 0]
            if not ok:
                return [int(t) for t in rng.integers(1, V + 1, L)]
            t = ok[int(rng.integers(len(ok)))]
            w.append(t)
            pre += wt[t - 1]
        return w
    return [int(t) for t in rng.integers(1, V + 1, L)]


def batch(c, L, B, rng):
    ws = [sample(c, L, rng) for _ in range(B)]
    toks = np.array([[0] + w for w in ws])
    ys = [target(c, w) for w in ws]
    return ws, toks, np.array(ys, float)


def posfeat(n):
    i = np.arange(n, dtype=float)
    return np.stack([np.ones(n), i, i * i, 1 / (i + 1), (-1.0) ** i, np.full(n, float(n)),
                     np.full(n, 1.0 / n), i / n], 1)


# ---------- model ----------

def init_params(shape, V, seed):
    rng = np.random.default_rng(seed)
    de, d = shape["de"], shape["de"] + 8
    P = {"E": rng.normal(0, 0.3, (V + 1, de)), "outW": rng.normal(0, 0.1, d), "outB": np.zeros(1)}
    for k, (nh, hd) in enumerate(zip(shape["heads"], shape["mlp"])):
        for h in range(nh):
            P["A%d_%d" % (k, h)] = rng.normal(0, 0.05, (d, d))
            P["V%d_%d" % (k, h)] = rng.normal(0, 0.1, (d, d))
        P["W1_%d" % k] = rng.normal(0, math.sqrt(1.0 / d), (hd, d))
        P["b1_%d" % k] = np.zeros(hd)
        P["W2_%d" % k] = rng.normal(0, 0.1 * math.sqrt(1.0 / max(hd, 1)), (d, hd))
        P["b2_%d" % k] = np.zeros(d)
    return P


def mask_matrix(mask, n):
    i, j = np.arange(n)[:, None], np.arange(n)[None, :]
    return np.ones((n, n), bool) if mask == "all" else (j <= i) if mask == "causal" else (j < i)


def forward(P, shape, toks, hard=False):
    """toks (B, n) with BOS at column 0. Returns per-position outputs (B, n) and a cache."""
    B, n = toks.shape
    X = np.concatenate([P["E"][toks], np.broadcast_to(posfeat(n), (B, n, 8))], 2)
    cache = {"toks": toks, "blocks": []}
    for k, nh in enumerate(shape["heads"]):
        Y = X.copy()
        hc = []
        for h in range(nh):
            A, Vm = P["A%d_%d" % (k, h)], P["V%d_%d" % (k, h)]
            M = mask_matrix(shape["masks"][k][h], n)
            KA = X @ A.T
            S = X @ KA.transpose(0, 2, 1)
            S = np.where(M[None], S, -np.inf)
            if hard:
                mx = S.max(2, keepdims=True)
                Pm = ((S >= mx - 1e-9 * (1 + np.abs(mx))) & M[None] & np.isfinite(mx)).astype(float)
            else:
                Sm = S - np.where(np.isfinite(S.max(2, keepdims=True)), S.max(2, keepdims=True), 0)
                Pm = np.where(M[None], np.exp(np.where(M[None], Sm, 0)), 0.0)
            Z = Pm.sum(2, keepdims=True)
            Pm = np.where(Z > 0, Pm / np.where(Z > 0, Z, 1), 0.0)
            VX = X @ Vm.T
            Y = Y + Pm @ VX
            hc.append((KA, Pm, VX))
        Hpre = Y @ P["W1_%d" % k].T + P["b1_%d" % k]
        H = np.maximum(Hpre, 0)
        Xn = Y + H @ P["W2_%d" % k].T + P["b2_%d" % k]
        cache["blocks"].append((X, Y, H, hc))
        X = Xn
    cache["final"] = X
    return X @ P["outW"] + P["outB"][0], cache


def loss_and_grad(P, shape, c, toks, ys):
    out, cache = forward(P, shape, toks)
    B, n = toks.shape
    dout = np.zeros_like(out)
    if c["family"] in ("parity", "dyck"):
        z = -ys * out[:, -1]
        loss = np.mean(np.logaddexp(0, z))
        dout[:, -1] = -ys / (1 + np.exp(-z)) / B
    else:
        diff = out[:, 1:] - ys
        loss = np.mean(diff ** 2)
        dout[:, 1:] = 2 * diff / diff.size
    G = {k: np.zeros_like(v) for k, v in P.items()}
    X = cache["final"]
    G["outW"] = np.einsum("bn,bnd->d", dout, X)
    G["outB"] = np.array([dout.sum()])
    dX = dout[:, :, None] * P["outW"][None, None, :]
    for k in reversed(range(len(shape["heads"]))):
        Xin, Y, H, hc = cache["blocks"][k]
        dY = dX.copy()
        G["b2_%d" % k] = dX.sum((0, 1))
        G["W2_%d" % k] = np.einsum("bnd,bnh->dh", dX, H)
        dH = (dX @ P["W2_%d" % k]) * (H > 0)
        G["b1_%d" % k] = dH.sum((0, 1))
        G["W1_%d" % k] = np.einsum("bnh,bnd->hd", dH, Y)
        dY = dY + dH @ P["W1_%d" % k]
        dXin = dY.copy()
        for h, (KA, Pm, VX) in enumerate(hc):
            A, Vm = P["A%d_%d" % (k, h)], P["V%d_%d" % (k, h)]
            dP = dY @ VX.transpose(0, 2, 1)
            dVX = Pm.transpose(0, 2, 1) @ dY
            G["V%d_%d" % (k, h)] = np.einsum("bnr,bnd->rd", dVX, Xin)
            dXin = dXin + dVX @ Vm
            dS = Pm * (dP - (dP * Pm).sum(2, keepdims=True))
            dXin = dXin + dS @ KA
            dKA = dS.transpose(0, 2, 1) @ Xin
            G["A%d_%d" % (k, h)] = np.einsum("bnr,bnd->rd", dKA, Xin)
            dXin = dXin + dKA @ A
        dX = dXin
    np.add.at(G["E"], cache["toks"], dX[:, :, :P["E"].shape[1]])
    return loss, G


def train(c, shape, seed):
    rng = np.random.default_rng(1000 + seed)
    P = init_params(shape, c["V"], seed)
    m = {k: np.zeros_like(v) for k, v in P.items()}
    v = {k: np.zeros_like(x) for k, x in P.items()}
    last = []
    for step in range(1, STEPS + 1):
        L = int(rng.integers(1, TRAIN_MAX + 1))
        _, toks, ys = batch(c, L, BATCH, rng)
        loss, G = loss_and_grad(P, shape, c, toks, ys)
        gn = math.sqrt(sum(float((g * g).sum()) for g in G.values()))
        scale = min(1.0, 1.0 / (gn + 1e-12))          # clip the global gradient norm at 1
        lr = LR * 0.5 * (1 + math.cos(math.pi * step / STEPS))
        for k in P:
            g = G[k] * scale
            m[k] = 0.9 * m[k] + 0.1 * g
            v[k] = 0.999 * v[k] + 0.001 * g * g
            P[k] -= lr * (m[k] / (1 - 0.9 ** step)) / (np.sqrt(v[k] / (1 - 0.999 ** step)) + 1e-8)
        if step > STEPS - 200:
            last.append(float(loss))
    return P, float(np.mean(last))


def accuracy(P, shape, c, lo, hi, rng, hard):
    good = 0
    for _ in range(N_EVAL):
        L = int(rng.integers(lo, hi + 1))
        ws, toks, ys = batch(c, L, 1, rng)
        out, _ = forward(P, shape, toks, hard=hard)
        if c["family"] in ("parity", "dyck"):
            good += (out[0, -1] > 0) == (ys[0] > 0)
        else:
            good += bool(np.all(np.abs(out[0, 1:] - ys[0]) < 0.5))
    return good / N_EVAL


def harden(P):
    return {k: np.round(v * DEN) / DEN for k, v in P.items()}


# ---------- shape of the doctor's solution ----------

def strip(s):
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    return re.sub(r"--.*", " ", s)


DEFAULT = {"de": 8, "heads": [2, 2], "mlp": [32, 32], "masks": [["all", "causal"], ["all", "causal"]]}


def shape_from_solution(path):
    """Best-effort parse of `def net : TNet`; None if it cannot be read with confidence."""
    try:
        s = strip(open(path, encoding="utf-8").read())
        masks = re.findall(r"mask\s*:=\s*(?:Mask\.|\.)(all|causal|strict)", s)
        nb1 = [len([t for t in b.split(",") if t.strip()]) for b in re.findall(r"\bb1\s*:=\s*\[([^\]]*)\]", s)]
        emb = re.search(r"embed\s*:=\s*\[\s*\[([^\]]*)\]", s)
        heads_per_block = [len(re.findall(r"\b\w+", h)) for h in re.findall(r"heads\s*:=\s*\[([^\]]*)\]", s)]
        if not (emb and nb1 and masks and heads_per_block and len(nb1) == len(heads_per_block)
                and sum(heads_per_block) == len(masks)):
            return None
        de = len([t for t in emb.group(1).split(",") if t.strip()])
        ms, k = [], 0
        for nh in heads_per_block:
            ms.append(masks[k:k + nh]); k += nh
        return {"de": de, "heads": heads_per_block, "mlp": nb1, "masks": ms}
    except Exception:
        return None


def gradcheck():
    c = {"family": "sort", "V": 3}
    shape = {"de": 3, "heads": [2, 1], "mlp": [4, 3], "masks": [["all", "strict"], ["causal"]]}
    rng = np.random.default_rng(0)
    P = init_params(shape, 3, 0)
    for k in P:
        P[k] = P[k] + rng.normal(0, 0.05, P[k].shape)
    _, toks, ys = batch(c, 5, 4, rng)
    _, G = loss_and_grad(P, shape, c, toks, ys)
    worst = 0.0
    for k in P:
        for _ in range(6):
            idx = tuple(int(rng.integers(s)) for s in P[k].shape)
            old = P[k][idx]
            P[k][idx] = old + 1e-6
            lp, _ = loss_and_grad(P, shape, c, toks, ys)
            P[k][idx] = old - 1e-6
            lm, _ = loss_and_grad(P, shape, c, toks, ys)
            P[k][idx] = old
            num = (lp - lm) / 2e-6
            worst = max(worst, abs(num - G[k][idx]) / (abs(num) + abs(G[k][idx]) + 1e-9))
    print("gradcheck worst relative error %.2e" % worst)
    c2 = {"family": "parity", "V": 2, "S": [1], "target": 1}
    _, toks, ys = batch(c2, 4, 3, rng)
    P2 = init_params(shape, 2, 1)
    _, G2 = loss_and_grad(P2, shape, c2, toks, ys)
    idx = (1, 2)
    old = P2["A0_0"][idx]
    P2["A0_0"][idx] = old + 1e-6; lp, _ = loss_and_grad(P2, shape, c2, toks, ys)
    P2["A0_0"][idx] = old - 1e-6; lm, _ = loss_and_grad(P2, shape, c2, toks, ys)
    print("classification check", (lp - lm) / 2e-6, G2["A0_0"][idx])


def main(split):
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung2_pool.json")))}
    draw = json.load(open(os.path.join(HERE, "pool", "draw2.json")))
    out_path = os.path.join(HERE, "results", "seq-twins-%s.json" % split)
    results = json.load(open(out_path)) if os.path.exists(out_path) else {}
    for cid in draw["rung2_" + split]:
        if cid in results:
            continue
        c = pool[cid]
        shape, src = None, "default"
        net_dir = os.path.join(HERE, "runs", "rung2-" + split, "net", cid)
        passed = [p for p in sorted(glob.glob(os.path.join(net_dir, "attempts", "*.json")))
                  if json.load(open(p, encoding="utf-8")).get("pass")]
        nj = os.path.join(net_dir, "net.json")
        if passed and os.path.exists(nj):       # exact export from Lean (PREREG_R2 amendment 5)
            j = json.load(open(nj))
            shape = {"de": len(j["embed"][0]), "heads": [len(b["heads"]) for b in j["blocks"]],
                     "mlp": [len(b["b1"]) for b in j["blocks"]],
                     "masks": [[h["mask"] for h in b["heads"]] for b in j["blocks"]]}
            src = "net-arm solution (Lean export)"
        elif passed:
            shape = shape_from_solution(passed[0][:-5] + ".lean")
            src = "net-arm solution" if shape else "default (could not parse the solution)"
        shape = shape or DEFAULT
        rec = {"shape": shape, "shape_source": src, "seeds": {}}
        for seed in (0, 1, 2):
            P, final_loss = train(c, shape, seed)
            Ph = harden(P)
            r = {"final_train_loss": final_loss, "soft": {}, "hard": {}}
            for name, lo, hi in BANDS:
                r["soft"][name] = accuracy(P, shape, c, lo, hi, np.random.default_rng(5000 + seed), False)
                r["hard"][name] = accuracy(Ph, shape, c, lo, hi, np.random.default_rng(5000 + seed), True)
            r["generalises_hard"] = all(a == 1.0 for a in r["hard"].values())
            rec["seeds"][seed] = r
            print(cid, c["family"], "seed", seed, "loss %.4f" % final_loss, "soft", r["soft"], "hard", r["hard"], flush=True)
        results[cid] = rec
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        json.dump(results, open(out_path, "w"), indent=1)       # save as each case finishes


if __name__ == "__main__":
    if sys.argv[1] == "gradcheck":
        gradcheck()
    else:
        main(sys.argv[1])
