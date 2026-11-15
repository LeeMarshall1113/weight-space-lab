"""Small encoder-only transformer (no LayerNorm), torch training + exact numpy forward.

Named weights (what the doctor sees), d model width, H heads, L layers, V vocab, C classes:
  emb [V,d]   pos [8,d]                              x_i = emb[tok_i] + pos[i]
  for l in 0..L-1:
    Lq_Wq Lq_Wk Lq_Wv Lq_Wo [d,d] (written L0_Wq ...)  head h uses columns h*dh:(h+1)*dh
      att_h = softmax((x Wq_h)(x Wk_h)^T / sqrt(dh), keys masked to the real length)
      x = x + concat_h(att_h (x Wv_h)) Wo
    Ll_W1 [d,4d] Ll_b1 [4d] Ll_W2 [4d,d] Ll_b2 [d]
      x = x + relu(x W1 + b1) W2 + b2
  logits = x U + bU     U [d,C] bU [C]      output at position i = classes[argmax logits_i]
Attention is bidirectional over the real (unpadded) positions; there is no BOS token.
"""
from __future__ import annotations

import numpy as np

MAXLEN = 8

SPEC = __doc__


def forward_np(w: dict, toks: list[int], n_layers: int, n_heads: int) -> np.ndarray:
    x = w["emb"][toks] + w["pos"][: len(toks)]
    d = x.shape[1]
    dh = d // n_heads
    for l in range(n_layers):
        q, k, v = x @ w[f"L{l}_Wq"], x @ w[f"L{l}_Wk"], x @ w[f"L{l}_Wv"]
        heads = []
        for h in range(n_heads):
            s = slice(h * dh, (h + 1) * dh)
            a = q[:, s] @ k[:, s].T / np.sqrt(dh)
            a = np.exp(a - a.max(1, keepdims=True))
            a /= a.sum(1, keepdims=True)
            heads.append(a @ v[:, s])
        x = x + np.concatenate(heads, 1) @ w[f"L{l}_Wo"]
        x = x + np.maximum(x @ w[f"L{l}_W1"] + w[f"L{l}_b1"], 0) @ w[f"L{l}_W2"] + w[f"L{l}_b2"]
    return x @ w["U"] + w["bU"]


def train(prog, vocab, classes, n_layers=2, d=64, n_heads=4, steps=3000, batch=256, lr=1e-3,
          seed=0, lo=4, hi=MAXLEN, anneal=False, l1=0.0, t_end=0.05):
    """anneal: attention logits / T, T linear 1 -> t_end, folded into Wq at export.
    l1: penalty on mean |MLP hidden activation| (PREREG_XF A6)."""
    import torch
    from xf import rasp as R
    from xf.gen import sample_inputs
    torch.set_num_threads(1)
    torch.manual_seed(seed)
    rng = np.random.default_rng(seed + 1)
    V, C = len(vocab), len(classes)
    cidx = {c: i for i, c in enumerate(classes)}
    tix = {t: i for i, t in enumerate(vocab)}
    P = {"emb": torch.randn(V, d) * 0.3, "pos": torch.randn(MAXLEN, d) * 0.3,
         "U": torch.randn(d, C) / np.sqrt(d), "bU": torch.zeros(C)}
    for l in range(n_layers):
        for nm in ("Wq", "Wk", "Wv", "Wo"):
            P[f"L{l}_{nm}"] = torch.randn(d, d) / np.sqrt(d)
        P[f"L{l}_W1"] = torch.randn(d, 4 * d) / np.sqrt(d)
        P[f"L{l}_b1"] = torch.zeros(4 * d)
        P[f"L{l}_W2"] = torch.randn(4 * d, d) / np.sqrt(4 * d) * 0.5
        P[f"L{l}_b2"] = torch.zeros(d)
    for p in P.values():
        p.requires_grad_(True)
    opt = torch.optim.AdamW(P.values(), lr=lr, weight_decay=0.01)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, steps)
    dh = d // n_heads

    temp = [1.0]
    acts = []

    def fwd(T, mask):  # T [B,L] long, mask [B,L] bool (True = real)
        x = P["emb"][T] + P["pos"][: T.shape[1]]
        B, L, _ = x.shape
        neg = (~mask)[:, None, None, :] * -1e9
        for l in range(n_layers):
            q = (x @ P[f"L{l}_Wq"]).view(B, L, n_heads, dh).transpose(1, 2)
            k = (x @ P[f"L{l}_Wk"]).view(B, L, n_heads, dh).transpose(1, 2)
            v = (x @ P[f"L{l}_Wv"]).view(B, L, n_heads, dh).transpose(1, 2)
            a = torch.softmax(q @ k.transpose(-1, -2) / np.sqrt(dh) / temp[0] + neg, -1)
            x = x + (a @ v).transpose(1, 2).reshape(B, L, d) @ P[f"L{l}_Wo"]
            hdn = torch.relu(x @ P[f"L{l}_W1"] + P[f"L{l}_b1"])
            acts.append(hdn[mask])
            x = x + hdn @ P[f"L{l}_W2"] + P[f"L{l}_b2"]
        return x @ P["U"] + P["bU"]

    def make(n):
        xs = sample_inputs(rng, vocab, n, lo, hi)
        T = torch.zeros(n, hi, dtype=torch.long)
        Y = torch.full((n, hi), -100, dtype=torch.long)
        M = torch.zeros(n, hi, dtype=torch.bool)
        for i, x in enumerate(xs):
            y = R.evaluate(prog, x)
            T[i, : len(x)] = torch.tensor([tix[t] for t in x])
            Y[i, : len(x)] = torch.tensor([cidx[v] for v in y])
            M[i, : len(x)] = True
        return T, Y, M

    for it in range(steps):
        if anneal:
            temp[0] = 1.0 + (t_end - 1.0) * it / max(steps - 1, 1)
        T, Y, M = make(batch)
        acts.clear()
        loss = torch.nn.functional.cross_entropy(fwd(T, M).reshape(-1, C), Y.reshape(-1), ignore_index=-100)
        if l1:
            loss = loss + l1 * sum(a.abs().mean() for a in acts)
        opt.zero_grad()
        loss.backward()
        torch.nn.utils.clip_grad_norm_(P.values(), 1.0)
        opt.step()
        sched.step()
    out = {k: v.detach().numpy().astype(np.float64) for k, v in P.items()}
    if anneal:  # fold 1/T_end into Wq so the standard forward (no temperature) is exact
        for l in range(n_layers):
            out[f"L{l}_Wq"] = out[f"L{l}_Wq"] / t_end
    return out, float(loss.detach())


def predict(w, x, vocab, classes, n_layers, n_heads):
    tix = {t: i for i, t in enumerate(vocab)}
    lg = forward_np(w, [tix[t] for t in x], n_layers, n_heads)
    return [classes[i] for i in lg.argmax(1)]


def seq_accuracy(w, prog, vocab, classes, n_layers, n_heads, n=1000, seed=99):
    from xf import rasp as R
    from xf.gen import sample_inputs
    xs = sample_inputs(np.random.default_rng(seed), vocab, n)
    ok = [predict(w, x, vocab, classes, n_layers, n_heads) == R.evaluate(prog, x) for x in xs]
    return float(np.mean(ok))
