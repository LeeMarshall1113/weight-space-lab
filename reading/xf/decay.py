"""Legibility decay curve (PREREG_DECAY.md).

    python xf/decay.py pilot                      # lr grid, writes results/decay_pilot.jsonl
    python xf/decay.py build <arm> --opt sgd --lr 1e-3 [--wd 1e-3]
    python xf/decay.py metrics                    # M1-M4 on every built net
Nets are the 20 Tracr calibration cases; everything float64; every net gate-checked
(>= 0.99 agreement on 1,000 inputs, sample_inputs seed 7).
"""
import argparse
import json
import os
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parent), str(HERE.parent.parent / "shared" / "harness")]
from xf.gen import sample_inputs  # noqa: E402

SRC = HERE / "cases_tracr"
MAN = json.loads((HERE / "cases_tracr_20261112.json").read_text())["cases"]
OUT = HERE.parent / "results"
TARGETS = (0.01, 0.10, 0.40)
GATE = 0.99


def gaming():
    return False  # the original polled a machine-specific "yield" flag file; removed for release


def load(m):
    return dict(np.load(SRC / m["case_id"] / "weights.npz")), m


# ---------- batched torch forward (exact: batches share one length, Tracr has no mask) ----------
def fwd(P, meta, ids, hard=False):
    import torch
    x = P["token_embed__embeddings"][ids] + P["pos_embed__embeddings"][: ids.shape[1]]
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
                s = q[..., h * dk:(h + 1) * dk] @ k[..., h * dk:(h + 1) * dk].transpose(-1, -2)
                if hard:
                    a = (s >= s.max(-1, keepdim=True).values - 1e-9).double()
                    a = a / a.sum(-1, keepdim=True)
                else:
                    a = torch.softmax(s, -1)
                outs.append(a @ v[..., h * dv:(h + 1) * dv])
            x = x + torch.cat(outs, -1) @ P[p + "__linear__w"] + P[p + "__linear__b"]
        else:
            x = x + torch.relu(x @ P[p + "__linear_1__w"] + P[p + "__linear_1__b"]) @ P[p + "__linear_2__w"] \
                + P[p + "__linear_2__b"]
    return (x @ P["unembed"])[:, 1:]


def encode(meta, xs):
    """Group inputs by length -> list of LongTensor [B, L+1] (BOS first)."""
    import torch
    order = meta["input_order"]
    by = {}
    for x in xs:
        by.setdefault(len(x), []).append([order.index(t) for t in ["BOS"] + list(x)])
    return [torch.tensor(v) for _, v in sorted(by.items())]


def as_t(w):
    import torch
    return {n: torch.tensor(v, dtype=torch.float64) for n, v in w.items()}


def predict(P, meta, batches, hard=False):
    import torch
    with torch.no_grad():
        return [fwd(P, meta, b, hard).argmax(-1) for b in batches]


def agree(pa, pb):
    n = sum(a.shape[0] for a in pa)
    return float(sum((a == b).all(-1).sum().item() for a, b in zip(pa, pb)) / n)


def shift_spec(m, w):
    """SHIFT/EDIT target: at positions holding token t*, class c -> c' (fixed from the case seed)."""
    rng = np.random.default_rng(int(m["prog_seed"]) + 5)
    xs = sample_inputs(np.random.default_rng(7), m["vocab"], 1000)
    P = as_t(w)
    preds = predict(P, m, encode(m, xs))
    tix = m["input_order"]
    best = None
    for t in rng.permutation(m["vocab"]):
        cnt = np.zeros(len(m["classes"]))
        for b, p in zip(encode(m, xs), preds):
            mask = (b[:, 1:] == tix.index(t)).numpy()
            for c in range(len(cnt)):
                cnt[c] += ((p.numpy() == c) & mask).sum()
        c = int(cnt.argmax())
        if cnt[c] > 0:
            best = (str(t), c, int(rng.choice([k for k in range(len(cnt)) if k != c])))
            break
    return {"token": best[0], "from": best[1], "to": best[2]}


def apply_shift(meta, batches, preds, sh):
    out = []
    ti = meta["input_order"].index(sh["token"])
    for b, p in zip(batches, preds):
        p = p.clone()
        m = (b[:, 1:] == ti) & (p == sh["from"])
        p[m] = sh["to"]
        out.append(p)
    return out


def drift(P, W0):
    import torch
    with torch.no_grad():
        num = sum(((P[n] - W0[n]) ** 2).sum() for n in W0) ** 0.5
        den = sum((W0[n] ** 2).sum() for n in W0) ** 0.5
    return float(num / den)


# ---------- training along a path ----------
def train_path(args):
    """Returns dict with per-checkpoint log and captured nets at each drift target."""
    import torch
    torch.set_num_threads(1)
    (m, opt_name, lr, wd, steps, mode, targets, noise_eps, seed) = args
    w, _ = load(m)
    W0 = as_t(w)
    gate_x = sample_inputs(np.random.default_rng(7), m["vocab"], 1000)
    gb = encode(m, gate_x)
    ref = predict(W0, m, gb)
    sh = None
    if mode == "shift":
        sh = shift_spec(m, w)
        ref = apply_shift(m, gb, ref, sh)
    P = {n: v.clone() for n, v in W0.items()}
    rng = np.random.default_rng(seed)
    if noise_eps:
        g = torch.Generator().manual_seed(seed)
        for n in P:
            z = torch.randn(P[n].shape, generator=g, dtype=torch.float64)
            nz = z.norm()
            if nz > 0 and P[n].norm() > 0:
                P[n] = P[n] + noise_eps * P[n].norm() * z / nz
    for v in P.values():
        v.requires_grad_(True)
    if opt_name == "adam":
        opt = torch.optim.AdamW(P.values(), lr=lr, weight_decay=wd)
    else:
        opt = torch.optim.SGD(P.values(), lr=lr, weight_decay=wd)
    log, caught = [], {}
    pending = list(targets)
    first_fail = None
    for it in range(steps + 1):
        if it % 25 == 0:
            a = agree(predict(P, m, gb), ref)
            d = drift(P, W0)
            log.append((it, round(d, 5), round(a, 4)))
            if a < GATE and first_fail is None:
                first_fail = d
            while pending and d >= pending[0] and a >= GATE:
                t = pending.pop(0)
                caught[t] = {"step": it, "drift": d, "agree": a,
                             "w": {n: v.detach().numpy().copy() for n, v in P.items()}}
            if noise_eps and a >= GATE and not caught:  # NOISE: first gated point after repair
                caught[noise_eps] = {"step": it, "drift": d, "agree": a,
                                     "w": {n: v.detach().numpy().copy() for n, v in P.items()}}
                break
            if (not pending and not noise_eps) or gaming():  # NOISE keeps repairing until gated
                break
        if it == steps:
            break
        L = int(rng.integers(4, 9))
        xs = sample_inputs(rng, m["vocab"], 64, L, L)
        b = encode(m, xs)[0]
        with torch.no_grad():
            y = fwd(W0, m, b).argmax(-1)
            if sh:
                y = apply_shift(m, [b], [y], sh)[0]
        loss = torch.nn.functional.cross_entropy(fwd(P, m, b).reshape(-1, len(m["classes"])), y.reshape(-1))
        opt.zero_grad()
        loss.backward()
        opt.step()
    return {"case_id": m["case_id"], "opt": opt_name, "lr": lr, "wd": wd, "mode": mode,
            "noise": noise_eps, "first_fail_drift": first_fail, "log": log, "shift": sh,
            "caught": caught, "gaming_stop": gaming()}


def pilot(a):
    grid = [("sgd", lr) for lr in (1e-4, 1e-3)] + [("adam", lr) for lr in (1e-5, 1e-4, 1e-3, 1e-2)]  # A1
    jobs = [(m, o, lr, 0.0, 3000, "ft", (0.05,), 0.0, 1) for o, lr in grid for m in MAN]
    OUT.mkdir(exist_ok=True)
    t0 = time.time()
    with Pool(a.procs) as pool, open(OUT / "decay_pilot.jsonl", "w") as f:
        for r in pool.imap_unordered(train_path, jobs):
            ok = 0.05 in r["caught"]
            r.pop("caught")
            r["gated_through_0.05"] = ok
            f.write(json.dumps(r) + "\n")
            f.flush()
            print(r["opt"], r["lr"], r["case_id"], "ok" if ok else "FAIL", "last", r["log"][-1],
                  f"{time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["pilot"])
    ap.add_argument("--procs", type=int, default=4)
    a = ap.parse_args()
    {"pilot": pilot}[a.cmd](a)
