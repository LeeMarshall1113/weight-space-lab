"""Numeric evaluators for the rung-5 softmax transformer of Lane4/RSoft.lean.

Two implementations of the same forward pass, in the operation order the theorem states
(every product, sum, difference and quotient rounded to float32; sums left to right;
max-subtracted softmax; an empty candidate list gives 0):

    run(net, w, pert, dtype, queries)        numpy (float32 = binary32; float64 stands in
                                             for exact arithmetic)
    TorchSoftNet(net, pert).forward(w, q)    PyTorch float32 module, same order, built from
                                             elementwise ops and torch.cumsum
    TorchSoftNet.forward_fast(w, q)          the ordinary vectorised PyTorch forward pass
                                             (torch.softmax, matmul): NOT the order of the
                                             theorem; compared numerically only

Net and perturbation layout: as tools/r4net.py.
"""
import os, sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r4net as R4

stored, rdot, rmat, random_pert = R4.stored, R4.rdot, R4.rmat, R4.random_pert


def _mask(kind, q, n):
    j = np.arange(n)
    if kind == "causal":
        return j[None, :] <= q[:, None]
    if kind == "strict":
        return j[None, :] < q[:, None]
    return np.ones((len(q), n), dtype=bool)


def attend(h, X, Q, chunk=3_000_000):
    """Softmax head output at query positions Q given the full state X (numpy)."""
    n, D = X.shape
    dt = X.dtype
    rows = [r for r in range(D) if np.any(h["A"][r] != 0)]
    vrows = [r for r in range(D) if np.any(h["V"][r] != 0)]
    AX = {r: rdot(h["A"][r], X) for r in rows}
    VX = {r: rdot(h["V"][r], X) for r in vrows}
    out = np.zeros((len(Q), D), dtype=dt)
    step = max(1, chunk // n)
    for s in range(0, len(Q), step):
        q = Q[s:s + step]
        sc = np.zeros((len(q), n), dtype=dt)
        for r in rows:                                   # pdot: left to right over the rows of A
            sc = sc + X[q, r][:, None] * AX[r][None, :]
        ok = _mask(h["mask"], q, n)
        m = np.where(ok, sc, -np.inf).max(axis=1, keepdims=True)
        m = np.where(np.isfinite(m), m, 0).astype(dt)
        arg = np.where(ok, (sc - m).astype(dt), dt.type(0))
        with np.errstate(under="ignore"):
            e = np.where(ok, np.exp(arg).astype(dt), dt.type(0)).astype(dt)
        Z = np.cumsum(e, axis=1, dtype=dt)[:, -1]
        for r in vrows:
            with np.errstate(under="ignore"):
                t = (e * VX[r][None, :]).astype(dt)
            num = np.cumsum(t, axis=1, dtype=dt)[:, -1]
            with np.errstate(invalid="ignore", divide="ignore"):
                out[s:s + step, r] = np.where(Z > 0, (num / Z).astype(dt), dt.type(0))
    return out


def run(net, w, pert=None, dtype=np.float32, queries=None):
    dt = np.dtype(dtype)
    S = stored(net, pert, dt)
    toks = np.concatenate([[0], np.asarray(w, dtype=np.int64)])
    n = len(toks)
    pos = np.stack([np.ones(n, dtype=dt), np.arange(n).astype(dt), np.full(n, n).astype(dt)], axis=1)
    X = np.concatenate([S["embed"][toks], pos], axis=1)
    Qfinal = np.arange(1, n) if queries is None else np.asarray(queries, dtype=np.int64)
    nb = len(S["blocks"])
    Q = np.arange(n)
    for b, B in enumerate(S["blocks"]):
        if b == nb - 1:
            Q = Qfinal
        Y = X[Q].copy()
        for h in B["heads"]:
            Y = Y + attend(h, X, Q)
        if len(B["b1"]):
            hid = np.maximum(rmat(B["W1"], Y) + B["b1"][None, :], dt.type(0))
            Y = Y + (rmat(B["W2"], hid) + B["b2"][None, :])
        else:
            Y = Y + np.broadcast_to(B["b2"][None, :], Y.shape)
        X = Y
    if nb == 0:
        X = X[Qfinal]
    return (rdot(S["outW"], X) + S["outB"]).astype(np.float64)


# ----------------------------------------------------------------------------- PyTorch

def make_torch_module(net, pert=None):
    import torch

    class TorchSoftNet(torch.nn.Module):
        """The rung-5 network as a PyTorch float32 module. `forward` follows the operation
        order of Lane4/RSoft.lean; `forward_fast` is the usual vectorised computation."""

        def __init__(self):
            super().__init__()
            S = stored(net, pert, np.dtype(np.float32))
            self.embed = torch.nn.Parameter(torch.from_numpy(S["embed"].copy()), requires_grad=False)
            self.outW = torch.nn.Parameter(torch.from_numpy(S["outW"].copy()), requires_grad=False)
            self.outB = torch.nn.Parameter(torch.tensor(float(S["outB"]), dtype=torch.float32), requires_grad=False)
            self.masks = [[h["mask"] for h in B["heads"]] for B in S["blocks"]]
            self.blocks = torch.nn.ModuleList()
            for B in S["blocks"]:
                m = torch.nn.Module()
                m.A = torch.nn.ParameterList([torch.nn.Parameter(torch.from_numpy(h["A"].copy()), requires_grad=False) for h in B["heads"]])
                m.V = torch.nn.ParameterList([torch.nn.Parameter(torch.from_numpy(h["V"].copy()), requires_grad=False) for h in B["heads"]])
                for k in ("W1", "b1", "W2", "b2"):
                    setattr(m, k, torch.nn.Parameter(torch.from_numpy(np.ascontiguousarray(B[k])), requires_grad=False))
                self.blocks.append(m)

        @staticmethod
        def _rdot(row, X):                               # left to right, zero weights skipped
            acc = torch.zeros(X.shape[0], dtype=X.dtype)
            for k in torch.nonzero(row).flatten().tolist():
                acc = acc + row[k] * X[:, k]
            return acc

        def _rmat(self, M, X):
            return torch.stack([self._rdot(M[r], X) for r in range(M.shape[0])], dim=1)

        @staticmethod
        def _ok(kind, q, n):
            j = torch.arange(n)
            if kind == "causal":
                return j[None, :] <= q[:, None]
            if kind == "strict":
                return j[None, :] < q[:, None]
            return torch.ones((len(q), n), dtype=torch.bool)

        def _state0(self, w):
            toks = torch.cat([torch.zeros(1, dtype=torch.long), torch.as_tensor(w, dtype=torch.long)])
            n = len(toks)
            pos = torch.stack([torch.ones(n), torch.arange(n, dtype=torch.float32), torch.full((n,), float(n))], dim=1)
            return torch.cat([self.embed[toks], pos], dim=1), n

        def _attend(self, A, V, kind, X, Q, chunk=3_000_000):
            n, D = X.shape
            rows = [r for r in range(D) if bool(torch.any(A[r] != 0))]
            vrows = [r for r in range(D) if bool(torch.any(V[r] != 0))]
            AX = {r: self._rdot(A[r], X) for r in rows}
            VX = {r: self._rdot(V[r], X) for r in vrows}
            out = torch.zeros((len(Q), D), dtype=X.dtype)
            step = max(1, chunk // n)
            zero = torch.zeros((), dtype=X.dtype)
            for s in range(0, len(Q), step):
                q = Q[s:s + step]
                sc = torch.zeros((len(q), n), dtype=X.dtype)
                for r in rows:
                    sc = sc + X[q, r][:, None] * AX[r][None, :]
                ok = self._ok(kind, q, n)
                m = torch.where(ok, sc, torch.full_like(sc, float("-inf"))).max(dim=1, keepdim=True).values
                m = torch.where(torch.isfinite(m), m, torch.zeros_like(m))
                e = torch.where(ok, torch.exp(torch.where(ok, sc - m, zero)), zero)
                Z = torch.cumsum(e, dim=1)[:, -1]
                for r in vrows:
                    num = torch.cumsum(e * VX[r][None, :], dim=1)[:, -1]
                    out[s:s + step, r] = torch.where(Z > 0, num / torch.where(Z > 0, Z, torch.ones_like(Z)), zero)
            return out

        def _attend_fast(self, A, V, kind, X, Q, chunk=3_000_000):
            # same computation as before, in row chunks: an n x n score matrix at 65,534
            # positions is 17 GB (this took commit to 98% on 2026-11-14 and the memory guard
            # killed the check). At most `chunk` score entries are held at once.
            n = X.shape[0]
            VX = X @ V.T
            out = torch.zeros((len(Q), X.shape[1]), dtype=X.dtype)
            step = max(1, chunk // n)
            for s in range(0, len(Q), step):
                q = Q[s:s + step]
                sc = (X[q] @ A) @ X.T
                ok = self._ok(kind, q, n)
                p = torch.softmax(sc.masked_fill(~ok, float("-inf")), dim=1)
                p = torch.where(ok.any(dim=1, keepdim=True), p, torch.zeros_like(p))
                out[s:s + step] = p @ VX
            return out

        def _run(self, w, queries, fast):
            with torch.no_grad():
                X, n = self._state0(w)
                Qf = torch.arange(1, n) if queries is None else torch.as_tensor(queries, dtype=torch.long)
                Q = torch.arange(n)
                nb = len(self.blocks)
                for b, B in enumerate(self.blocks):
                    if b == nb - 1:
                        Q = Qf
                    Y = X[Q].clone()
                    for k in range(len(B.A)):
                        Y = Y + (self._attend_fast(B.A[k], B.V[k], self.masks[b][k], X, Q) if fast
                                 else self._attend(B.A[k], B.V[k], self.masks[b][k], X, Q))
                    if B.b1.numel():
                        if fast:
                            Y = Y + (torch.relu(Y @ B.W1.T + B.b1) @ B.W2.T + B.b2)
                        else:
                            hid = torch.relu(self._rmat(B.W1, Y) + B.b1[None, :])
                            Y = Y + (self._rmat(B.W2, hid) + B.b2[None, :])
                    else:
                        Y = Y + B.b2[None, :]
                    X = Y
                if nb == 0:
                    X = X[Qf]
                return (X @ self.outW + self.outB) if fast else (self._rdot(self.outW, X) + self.outB)

        def forward(self, w, queries=None):
            return self._run(w, queries, fast=False)

        def forward_fast(self, w, queries=None):
            return self._run(w, queries, fast=True)

    return TorchSoftNet()


EXAMPLE_NET = {  # worked example: output the previous token (score scale 17)
    "embed": [[0, 0], [1, 0], [2, 0]],
    "blocks": [{"heads": [{"A": [[0] * 5, [0] * 5, [0, 0, 0, 17, 0], [0] * 5, [0] * 5],
                           "V": [[0] * 5, [1, 0, 0, 0, 0], [0] * 5, [0] * 5, [0] * 5], "mask": "strict"}],
                "W1": [], "b1": [], "W2": [[]] * 5, "b2": [0] * 5}],
    "outW": [0, 1, 0, 0, 0], "outB": 0}


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for n, dt in ((50, np.float64), (5000, np.float32), (65534, np.float32)):
        w = rng.integers(1, 3, n)
        q = None if n <= 5000 else np.concatenate([np.arange(1, 200), rng.integers(1, n + 1, 300), [n]])
        tgt = np.concatenate([[0], w])[(np.arange(1, n + 1) if q is None else q) - 1]
        for tau in (0.0, 1 / 200):
            p = random_pert(EXAMPLE_NET, tau, rng, "sign") if tau else None
            y = run(EXAMPLE_NET, w, p, dt, q)
            line = "example net  n=%6d  %s  tau=%.4f  numpy max dev %.3e" % (n, np.dtype(dt).name, tau, np.max(np.abs(y - tgt)))
            if dt is np.float32:
                net_t = make_torch_module(EXAMPLE_NET, p)
                yt = net_t(w, q).numpy().astype(np.float64)
                yf = net_t.forward_fast(w, q).numpy().astype(np.float64)
                line += " | torch ref == numpy bitwise: %s | torch fast max dev %.3e" % (bool(np.array_equal(yt, y)), np.max(np.abs(yf - tgt)))
            print(line, flush=True)
