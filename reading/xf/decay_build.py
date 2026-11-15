"""Build the decay arms and compute cheap metrics (PREREG_DECAY.md).

    python xf/decay_build.py build ft|ftwd|shift|noise|comp --opt adam --lr 1e-3 [--wd 1e-3] [--steps N]
    python xf/decay_build.py metrics
Writes xf/cases_tracr_decay_<arm>_p<k>/<id>/ + xf/cases_tracr_decay_<arm>_p<k>.json,
and results/decay_metrics.jsonl.
"""
import argparse
import json
import shutil
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parent), str(HERE.parent.parent / "shared" / "harness")]
from xf import decay as D  # noqa: E402
from xf.gen import sample_inputs  # noqa: E402

NOISE_EPS = (0.01, 0.10, 0.40)
COMP_RATIO = (0.9, 0.7, 0.5)


def save_point(arm, k, rows):
    name = f"tracr_decay_{arm}_p{k}"
    dst = D.HERE / f"cases_{name}"
    dst.mkdir(exist_ok=True)
    kept, dropped = [], []
    for m, rec in rows:
        if rec is None:
            dropped.append({"case_id": m["case_id"]})
            continue
        o = dst / m["case_id"]
        o.mkdir(exist_ok=True)
        np.savez(o / "weights.npz", **rec["w"])
        meta = dict(m)
        if "d_resid" in rec:
            meta["d_resid"] = rec["d_resid"]
        (o / "meta.json").write_text(json.dumps(meta, indent=1))
        shutil.copy(D.SRC / m["case_id"] / "program.txt", o / "program.txt")
        kept.append({**meta, **{k2: v for k2, v in rec.items() if k2 != "w"}})
    (D.HERE / f"cases_{name}.json").write_text(json.dumps({"arm": arm, "point": k, "cases": kept,
                                                            "dropped": dropped}, indent=1))
    print(name, len(kept), "kept,", len(dropped), "dropped", flush=True)


# ---------- COMP: learned residual compression x' = x E ----------
def compress(W, meta, E):
    out = {}
    out["token_embed__embeddings"] = W["token_embed__embeddings"] @ E
    out["pos_embed__embeddings"] = W["pos_embed__embeddings"] @ E
    out["unembed"] = E.T @ W["unembed"]
    for layer in meta["layers"]:
        p = f"transformer__{layer}"
        if layer.endswith("attn"):
            for nm in ("query", "key", "value"):
                out[f"{p}__{nm}__w"] = E.T @ W[f"{p}__{nm}__w"]
                out[f"{p}__{nm}__b"] = W[f"{p}__{nm}__b"]
            out[f"{p}__linear__w"] = W[f"{p}__linear__w"] @ E
            out[f"{p}__linear__b"] = W[f"{p}__linear__b"] @ E
        else:
            out[f"{p}__linear_1__w"] = E.T @ W[f"{p}__linear_1__w"]
            out[f"{p}__linear_1__b"] = W[f"{p}__linear_1__b"]
            out[f"{p}__linear_2__w"] = W[f"{p}__linear_2__w"] @ E
            out[f"{p}__linear_2__b"] = W[f"{p}__linear_2__b"] @ E
    return out


def comp_path(args):
    import torch
    torch.set_num_threads(1)
    m, ratio, steps, lr, seed = args
    w, _ = D.load(m)
    W0 = D.as_t(w)
    d = w["token_embed__embeddings"].shape[1]
    dp = max(1, int(round(ratio * d)))
    gb = D.encode(m, sample_inputs(np.random.default_rng(7), m["vocab"], 1000))
    ref = D.predict(W0, m, gb)
    g = np.random.default_rng(seed)
    Q, _ = np.linalg.qr(g.standard_normal((d, d)))
    E = torch.tensor(Q[:, :dp], dtype=torch.float64, requires_grad=True)
    opt = torch.optim.Adam([E], lr=lr)
    rng = np.random.default_rng(seed + 1)
    best = None
    for it in range(steps + 1):
        if it % 25 == 0:
            with torch.no_grad():
                P = compress(W0, m, E)
            a = D.agree(D.predict(P, m, gb), ref)
            if a >= D.GATE:
                best = {"step": it, "agree": a, "d_resid": dp, "ratio": dp / d,
                        "w": {n: v.detach().numpy().copy() for n, v in P.items()}}
                break
            if D.gaming():
                break
        L = int(rng.integers(4, 9))
        b = D.encode(m, sample_inputs(rng, m["vocab"], 64, L, L))[0]
        with torch.no_grad():
            y = D.fwd(W0, m, b).argmax(-1)
        loss = torch.nn.functional.cross_entropy(D.fwd(compress(W0, m, E), m, b).reshape(-1, len(m["classes"])),
                                                 y.reshape(-1))
        opt.zero_grad()
        loss.backward()
        opt.step()
    return m, ratio, best


def build(a):
    t0 = time.time()
    if a.arm == "comp":
        jobs = [(m, r, a.steps, a.lr, 1) for r in COMP_RATIO for m in D.MAN]
        with Pool(a.procs) as pool:
            res = pool.map(comp_path, jobs)
        for k, r in enumerate(COMP_RATIO, 1):
            save_point("comp", k, [(m, b) for m, rr, b in res if rr == r])
    elif a.arm == "noise":
        jobs = [(m, a.opt, a.lr, a.wd, a.steps, "ft", (), eps, 1) for eps in NOISE_EPS for m in D.MAN]
        with Pool(a.procs) as pool:
            res = pool.map(D.train_path, jobs)
        for k, eps in enumerate(NOISE_EPS, 1):
            rows = []
            for m in D.MAN:
                r = next(x for x in res if x["case_id"] == m["case_id"] and x["noise"] == eps)
                c = r["caught"].get(eps)
                rows.append((m, None if c is None else {**c, "noise": eps}))
            save_point("noise", k, rows)
    else:
        mode = "shift" if a.arm == "shift" else "ft"
        jobs = [(m, a.opt, a.lr, a.wd, a.steps, mode, D.TARGETS, 0.0, 1) for m in D.MAN]
        with Pool(a.procs) as pool:
            res = pool.map(D.train_path, jobs)
        for k, t in enumerate(D.TARGETS, 1):
            rows = []
            for m in D.MAN:
                r = next(x for x in res if x["case_id"] == m["case_id"])
                c = r["caught"].get(t)
                rows.append((m, None if c is None else {**c, "first_fail_drift": r["first_fail_drift"],
                                                         "shift": r["shift"]}))
            save_point(a.arm, k, rows)
        with open(D.OUT / f"decay_{a.arm}_paths.jsonl", "w") as f:
            for r in res:
                r.pop("caught")
                f.write(json.dumps(r) + "\n")
    print("done", f"{time.time() - t0:.0f}s", flush=True)


# ---------- cheap metrics ----------
def rows_tables(w, meta):
    """Token-space tables from single (token, position) rows, as the doctors read them.
    Returns (qk tables [rows x rows logits], write tables [rows x d_resid] from OV and MLP)."""
    E, Pz = w["token_embed__embeddings"], w["pos_embed__embeddings"]
    R = np.array([E[t] + Pz[i] for t in range(E.shape[0]) for i in range(Pz.shape[0])])
    H = meta["num_heads"]
    qk, wr = [], []
    for layer in meta["layers"]:
        p = f"transformer__{layer}"
        if layer.endswith("attn"):
            q = R @ w[p + "__query__w"] + w[p + "__query__b"]
            k = R @ w[p + "__key__w"] + w[p + "__key__b"]
            v = R @ w[p + "__value__w"] + w[p + "__value__b"]
            dk, dv = q.shape[1] // H, v.shape[1] // H
            for h in range(H):
                qk.append(q[:, h * dk:(h + 1) * dk] @ k[:, h * dk:(h + 1) * dk].T)
                wr.append(v[:, h * dv:(h + 1) * dv] @ w[p + "__linear__w"][h * dv:(h + 1) * dv])
        else:
            wr.append(np.maximum(R @ w[p + "__linear_1__w"] + w[p + "__linear_1__b"], 0) @ w[p + "__linear_2__w"])
    return qk, wr


def live(ts, ref=None):
    """Tables that are non-zero in the reference (k = 0) net; zero tables carry no reading."""
    ref = ts if ref is None else ref
    return [t for t, r in zip(ts, ref) if np.abs(r).max() > 1e-9]


def qk_discreteness(t):
    """Per query row: max over s of 1 - TV(softmax row, uniform over the top-s keys); 1 = a hard Select."""
    z = t - t.max(1, keepdims=True)
    p = np.exp(z)
    p /= p.sum(1, keepdims=True)
    ps = -np.sort(-p, 1)
    n = p.shape[1]
    best = np.zeros(p.shape[0])
    cs = np.cumsum(ps, 1)
    for s in range(1, n + 1):
        # TV(p, u_s) = sum over top-s of |p - 1/s| / 2 + (1 - cs[s-1]) / 2
        tv = 0.5 * (np.abs(ps[:, :s] - 1.0 / s).sum(1) + (1 - cs[:, s - 1]))
        best = np.maximum(best, 1 - tv)
    return best


def write_discreteness(t):
    """Fraction of row pairs that are clearly equal (< 5%) or clearly different (> 50%) of the max
    pairwise distance; 1 = a clean lookup table, lower = graded values."""
    D2 = np.sqrt(((t[:, None, :] - t[None, :, :]) ** 2).sum(-1))
    mx = D2.max()
    if mx <= 1e-12:
        return 1.0
    iu = np.triu_indices(t.shape[0], 1)
    d = D2[iu] / mx
    return float(((d < 0.05) | (d > 0.5)).mean())


def m1_parts(w, w0, meta):
    qk, wr = rows_tables(w, meta)
    qk0, wr0 = rows_tables(w0, meta)
    lq, lw = live(qk, qk0), live(wr, wr0)
    a = float(np.mean(np.concatenate([qk_discreteness(t) for t in lq]))) if lq else float("nan")
    b = float(np.mean([write_discreteness(t) for t in lw])) if lw else float("nan")
    # M3 over tables whose shapes match k = 0 (COMP changes d_resid, so only its QK tables count)
    pairs = [(t, r) for t, r in zip(lq + lw, live(qk0) + live(wr0)) if t.shape == r.shape]
    flat = np.concatenate([t.ravel() for t, _ in pairs])
    flat0 = np.concatenate([r.ravel() for _, r in pairs])
    return a, b, flat, flat0


def spearman(a, b):
    from scipy.stats import spearmanr
    return float(spearmanr(a, b).correlation)


def metrics_one(args):
    import torch
    torch.set_num_threads(1)
    name, cid = args
    d = D.HERE / f"cases_{name}" / cid
    w = dict(np.load(d / "weights.npz"))
    meta = json.loads((d / "meta.json").read_text())
    w0 = dict(np.load(D.SRC / cid / "weights.npz"))
    m1q, m1w, flat, flat0 = m1_parts(w, w0, meta)
    P = D.as_t(w)
    gb = D.encode(meta, sample_inputs(np.random.default_rng(7), meta["vocab"], 1000))
    soft = D.predict(P, meta, gb)
    m4 = D.agree(D.predict(P, meta, gb, hard=True), soft)
    # M2: mean max attention weight on 200 held-out inputs
    xs = sample_inputs(np.random.default_rng(11), meta["vocab"], 200)
    mx = []
    with torch.no_grad():
        for b in D.encode(meta, xs):
            x = P["token_embed__embeddings"][b] + P["pos_embed__embeddings"][: b.shape[1]]
            H = meta["num_heads"]
            for layer in meta["layers"]:
                p = f"transformer__{layer}"
                if layer.endswith("attn"):
                    q = x @ P[p + "__query__w"] + P[p + "__query__b"]
                    k = x @ P[p + "__key__w"] + P[p + "__key__b"]
                    v = x @ P[p + "__value__w"] + P[p + "__value__b"]
                    dk, dv = q.shape[-1] // H, v.shape[-1] // H
                    outs = []
                    for h in range(H):
                        a = torch.softmax(q[..., h * dk:(h + 1) * dk] @ k[..., h * dk:(h + 1) * dk].transpose(-1, -2), -1)
                        if P[p + "__query__w"].abs().max() > 1e-9:
                            mx.append(a.max(-1).values.mean().item())
                        outs.append(a @ v[..., h * dv:(h + 1) * dv])
                    x = x + torch.cat(outs, -1) @ P[p + "__linear__w"] + P[p + "__linear__b"]
                else:
                    x = x + torch.relu(x @ P[p + "__linear_1__w"] + P[p + "__linear_1__b"]) @ P[p + "__linear_2__w"] \
                        + P[p + "__linear_2__b"]
    mats = [v for v in w.values() if v.ndim == 2 and np.abs(v).max() > 1e-9]
    er = []
    for v in mats:
        s = np.linalg.svd(v, compute_uv=False)
        s = s / s.sum()
        s = s[s > 0]
        er.append(float(np.exp(-(s * np.log(s)).sum())))
    tot = sum(v.size for v in w.values())
    return {"set": name, "case_id": cid, "M1": (m1q + m1w) / 2, "M1_qk": m1q, "M1_write": m1w,
            "M2": float(np.mean(mx)) if mx else float("nan"),
            "M3": spearman(flat, flat0), "M4": m4, "M4_pass": m4 >= 0.99,
            "eff_rank": float(np.mean(er)),
            "near_zero": float(sum((np.abs(v) < 1e-6).sum() for v in w.values()) / tot)}


def metrics(a):
    sets = sorted(p.name[len("cases_"):-len(".json")] for p in D.HERE.glob("cases_tracr_decay_*.json"))
    jobs = []
    for s in sets:
        man = json.loads((D.HERE / f"cases_{s}.json").read_text())
        jobs += [(s, c["case_id"]) for c in man["cases"]]
    # k = 0 reference, stored as a pseudo-set
    k0 = D.HERE / "cases_tracr_decay_k0"
    if not k0.exists():
        k0.mkdir()
        for m in D.MAN:
            shutil.copytree(D.SRC / m["case_id"], k0 / m["case_id"])
    jobs += [("tracr_decay_k0", m["case_id"]) for m in D.MAN]
    with Pool(a.procs) as pool:
        res = pool.map(metrics_one, jobs)
    with open(D.OUT / "decay_metrics.jsonl", "w") as f:
        for r in res:
            f.write(json.dumps(r) + "\n")
    print(len(res), "nets measured", flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["build", "metrics"])
    ap.add_argument("arm", nargs="?")
    ap.add_argument("--opt", default="adam")
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--wd", type=float, default=0.0)
    ap.add_argument("--steps", type=int, default=20000)
    ap.add_argument("--procs", type=int, default=4)
    a = ap.parse_args()
    {"build": build, "metrics": metrics}[a.cmd](a)
