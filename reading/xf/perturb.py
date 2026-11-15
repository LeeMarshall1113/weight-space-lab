"""Perturbation variants of the Tracr calibration nets (PREREG_XF A4).

    python xf/perturb.py rot
    python xf/perturb.py ft --k 10|100|1000 --n 10|20
Writes xf/cases_tracr_<level>/<id>/ (weights.npz, meta.json, program.txt) and
xf/cases_tracr_<level>.json with drift / sparsity / agreement per case.
"""
import argparse
import json
import shutil
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parent), str(HERE.parent.parent / "shared" / "harness")]
from xf.gen import sample_inputs  # noqa: E402
from xf.task import np_forward_tracr  # noqa: E402

SRC = HERE / "cases_tracr"
MAN = json.loads((HERE / "cases_tracr_20261112.json").read_text())["cases"]


def agreement(w0, w1, meta, n=1000, seed=7):
    xs = sample_inputs(np.random.default_rng(seed), meta["vocab"], n)
    return float(np.mean([np_forward_tracr(w0, meta, x) == np_forward_tracr(w1, meta, x) for x in xs]))


def rotate(w, meta, seed):
    d = w["token_embed__embeddings"].shape[1]
    R, _ = np.linalg.qr(np.random.default_rng(seed).standard_normal((d, d)))
    out = {k: v.copy() for k, v in w.items()}
    out["token_embed__embeddings"] = w["token_embed__embeddings"] @ R
    out["pos_embed__embeddings"] = w["pos_embed__embeddings"] @ R
    out["unembed"] = R.T @ w["unembed"]
    for layer in meta["layers"]:
        p = f"transformer__{layer}"
        if layer.endswith("attn"):
            for nm in ("query", "key", "value"):
                out[f"{p}__{nm}__w"] = R.T @ w[f"{p}__{nm}__w"]
            out[f"{p}__linear__w"] = w[f"{p}__linear__w"] @ R
            out[f"{p}__linear__b"] = w[f"{p}__linear__b"] @ R
        else:
            out[f"{p}__linear_1__w"] = R.T @ w[f"{p}__linear_1__w"]
            out[f"{p}__linear_2__w"] = w[f"{p}__linear_2__w"] @ R
            out[f"{p}__linear_2__b"] = w[f"{p}__linear_2__b"] @ R
    return out


def _wellcond(rng, n):
    U, _ = np.linalg.qr(rng.standard_normal((n, n)))
    V, _ = np.linalg.qr(rng.standard_normal((n, n)))
    return U @ np.diag(np.exp(rng.uniform(np.log(0.5), np.log(2), n))) @ V


def densify(w, meta, seed, level):
    """level 2: + per-head QK/OV invertible transforms; level 3: + MLP permutation/scaling."""
    rng = np.random.default_rng(seed + 1)
    out = rotate(w, meta, seed)
    H = meta["num_heads"]
    for layer in meta["layers"]:
        p = f"transformer__{layer}"
        if layer.endswith("attn"):
            dk = out[f"{p}__query__w"].shape[1] // H
            dv = out[f"{p}__value__w"].shape[1] // H
            for h in range(H):
                sk, sv = slice(h * dk, (h + 1) * dk), slice(h * dv, (h + 1) * dv)
                A = _wellcond(rng, dk)
                Ait = np.linalg.inv(A).T
                out[f"{p}__query__w"][:, sk] = out[f"{p}__query__w"][:, sk] @ A
                out[f"{p}__query__b"][sk] = out[f"{p}__query__b"][sk] @ A
                out[f"{p}__key__w"][:, sk] = out[f"{p}__key__w"][:, sk] @ Ait
                out[f"{p}__key__b"][sk] = out[f"{p}__key__b"][sk] @ Ait
                B = _wellcond(rng, dv)
                out[f"{p}__value__w"][:, sv] = out[f"{p}__value__w"][:, sv] @ B
                out[f"{p}__value__b"][sv] = out[f"{p}__value__b"][sv] @ B
                out[f"{p}__linear__w"][sv, :] = np.linalg.inv(B) @ out[f"{p}__linear__w"][sv, :]
        elif level >= 3:
            n = out[f"{p}__linear_1__w"].shape[1]
            perm = rng.permutation(n)
            sc = np.exp(rng.uniform(np.log(0.5), np.log(2), n))
            out[f"{p}__linear_1__w"] = out[f"{p}__linear_1__w"][:, perm] * sc
            out[f"{p}__linear_1__b"] = out[f"{p}__linear_1__b"][perm] * sc
            out[f"{p}__linear_2__w"] = out[f"{p}__linear_2__w"][perm, :] / sc[:, None]
    return out


def finetune(w, meta, k, seed, lr=3e-3, batch=64, opt_name="adamw"):
    import torch
    torch.set_num_threads(1)
    torch.manual_seed(seed)
    P = {n: torch.tensor(v, dtype=torch.float64, requires_grad=True) for n, v in w.items()}  # float32 alone breaks compiled nets
    opt = (torch.optim.AdamW(P.values(), lr=lr, weight_decay=0.0) if opt_name == "adamw"
           else torch.optim.SGD(P.values(), lr=lr))
    H, order, classes = meta["num_heads"], meta["input_order"], meta["classes"]
    rng = np.random.default_rng(seed)

    def fwd(ids):  # ids: list[int] incl. BOS; returns logits [L, C]
        x = P["token_embed__embeddings"][ids] + P["pos_embed__embeddings"][: len(ids)]
        for layer in meta["layers"]:
            p = f"transformer__{layer}"
            if layer.endswith("attn"):
                q = x @ P[p + "__query__w"] + P[p + "__query__b"]
                kk = x @ P[p + "__key__w"] + P[p + "__key__b"]
                v = x @ P[p + "__value__w"] + P[p + "__value__b"]
                dk, dv = q.shape[1] // H, v.shape[1] // H
                outs = [torch.softmax(q[:, h * dk:(h + 1) * dk] @ kk[:, h * dk:(h + 1) * dk].T, -1)
                        @ v[:, h * dv:(h + 1) * dv] for h in range(H)]
                x = x + torch.cat(outs, 1) @ P[p + "__linear__w"] + P[p + "__linear__b"]
            else:
                x = x + torch.relu(x @ P[p + "__linear_1__w"] + P[p + "__linear_1__b"]) @ P[p + "__linear_2__w"] \
                    + P[p + "__linear_2__b"]
        return x @ P["unembed"]

    for _ in range(k):
        xs = sample_inputs(rng, meta["vocab"], batch)
        loss = 0
        for x in xs:
            y = torch.tensor([classes.index(v) for v in np_forward_tracr(w, meta, x)])
            loss = loss + torch.nn.functional.cross_entropy(fwd([order.index(t) for t in ["BOS"] + x])[1:], y)
        opt.zero_grad()
        (loss / batch).backward()
        opt.step()
    return {n: p.detach().numpy().astype(np.float64) for n, p in P.items()}


def _make(args):
    m, level, k = args
    w = dict(np.load(SRC / m["case_id"] / "weights.npz"))
    seed = int(m["prog_seed"]) % 100003
    if level == "rot":
        return m, w, rotate(w, m, seed)
    if level in ("head", "mlp"):
        return m, w, densify(w, m, seed, 2 if level == "head" else 3)
    return m, w, finetune(w, m, k, seed)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("level", choices=["rot", "ft", "head", "mlp"])
    ap.add_argument("--k", type=int, default=0)
    ap.add_argument("--n", type=int, default=20)
    a = ap.parse_args()
    name = {"rot": "rot", "head": "rothead", "mlp": "rotheadmlp"}.get(a.level, f"ft{a.k}")
    dst = HERE / f"cases_tracr_{name}"
    dst.mkdir(exist_ok=True)
    kept, dropped = [], []
    from multiprocessing import Pool
    todo = MAN[: min(len(MAN), a.n + 4)]
    with Pool(4) as pool:
        made = pool.map(_make, [(m, a.level, a.k) for m in todo])
    for m, w, w2 in made:
        if len(kept) == a.n:
            break
        d = SRC / m["case_id"]
        agr = agreement(w, w2, m)
        num = sum(((w2[n] - w[n]) ** 2).sum() for n in w) ** 0.5
        den = sum((w[n] ** 2).sum() for n in w) ** 0.5
        tot = sum(v.size for v in w2.values())
        row = {"case_id": m["case_id"], "agreement": agr, "rel_drift": float(num / den),
               "near_zero_frac": float(sum((np.abs(v) < 1e-6).sum() for v in w2.values()) / tot),
               "near_zero_frac_orig": float(sum((np.abs(v) < 1e-6).sum() for v in w.values()) / tot)}
        if agr < 0.99:
            dropped.append(row)
            continue
        o = dst / m["case_id"]
        o.mkdir(exist_ok=True)
        np.savez(o / "weights.npz", **w2)
        shutil.copy(d / "meta.json", o / "meta.json")
        shutil.copy(d / "program.txt", o / "program.txt")
        kept.append({**m, **row})
        print(name, m["case_id"], round(agr, 3), "drift", round(row["rel_drift"], 3), "zero", round(row["near_zero_frac"], 3))
    (HERE / f"cases_tracr_{name}.json").write_text(json.dumps({"level": name, "cases": kept, "dropped": dropped}, indent=1))
    print(len(kept), "kept,", len(dropped), "dropped")


if __name__ == "__main__":
    main()
