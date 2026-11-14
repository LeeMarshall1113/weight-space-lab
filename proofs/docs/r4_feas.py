"""Lane feasibility check (not a result): hand constructions for carry and induct,
tested under sign-corner relative perturbations. Numerical only, nothing proved."""
import sys, os, itertools
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
import r4net as R, r4pool as P

def Z(r, c): return [[0.0] * c for _ in range(r)]

def carry_net(c):
    V, m = c["V"], c["m"]
    D = 9
    emb = [[0] * 6] + [[c["dg"][t], (c["dg"][t] + 1) % m, 1 if c["cls"][t] == 2 else 0, 1 if c["cls"][t] == 1 else 0, 0, 0] for t in range(V)]
    A = Z(D, D); A[6][7] = 1; A[8][2] = -2
    Vm = Z(D, D); Vm[4][3] = 1
    K = m
    W1 = Z(2, D); W1[0][0] = 1; W1[0][4] = -K; W1[1][1] = 1; W1[1][4] = K
    W2 = Z(D, 2); W2[5][0] = 1; W2[5][1] = 1
    outW = [0] * D; outW[5] = 1
    return {"embed": emb, "blocks": [{"heads": [{"A": A, "V": Vm, "mask": "strict"}], "W1": W1, "b1": [0, -K], "W2": W2, "b2": [0] * D}], "outW": outW, "outB": 0}

def induct_net(c):
    V = c["V"]; de = 4 * V + 2; D = de + 3
    one, pi, pn = de, de + 1, de + 2
    IND, NOT, VAL, PN, RT, O = 0, V, 2 * V, 2 * V + 1, 3 * V + 1, 4 * V + 1
    emb = [[0] * V + [1] * V + [0] * (2 * V + 2)]
    for t in range(V):
        r = [0] * de
        r[IND + t] = 1
        for s in range(V):
            if s != t: r[NOT + s] = 1
        r[VAL] = c["h"][t]
        emb.append(r)
    A1 = Z(D, D); A1[one][pi] = 1
    V1 = Z(D, D)
    for t in range(V): V1[PN + t][NOT + t] = 1
    b1 = {"heads": [{"A": A1, "V": V1, "mask": "strict"}], "W1": [], "b1": [], "W2": [[]] * D, "b2": [0] * D}
    heads = []
    for t in range(V):
        A = Z(D, D); A[one][pi] = 1; A[pn][PN + t] = -2
        Vm = Z(D, D); Vm[RT + t][VAL] = 1
        heads.append({"A": A, "V": Vm, "mask": "causal"})
    W1 = Z(V, D)
    for t in range(V): W1[t][RT + t] = 1; W1[t][NOT + t] = -3
    W2 = Z(D, V)
    for t in range(V): W2[O][t] = 1
    outW = [0] * D; outW[O] = 1
    return {"embed": emb, "blocks": [b1, {"heads": heads, "W1": W1, "b1": [0] * V, "W2": W2, "b2": [0] * D}], "outW": outW, "outB": 0}

pool = P.make_pool()
rng = np.random.default_rng(1)
for fam, build in (("carry", carry_net), ("induct", induct_net)):
    cases = [c for c in pool if c["family"] == fam][-6:]      # tail of the pool, not the draw order
    for c in cases:
        net = build(c)
        worst = {}
        for mult in (0, 1, 2, 4, 8, 16, 32, 64):
            tau = mult / 200
            wd = 0.0
            for trial in range(12 if mult else 1):
                n = int(rng.choice([5, 40, 300, 1500]))
                w = rng.integers(1, c["V"] + 1, n)
                if trial % 3 == 1 and fam == "carry":           # long propagate run
                    pt = [t + 1 for t in range(c["V"]) if c["cls"][t] == 2][0]
                    w[2:] = pt
                p = R.random_pert(net, tau, rng, "sign") if mult else None
                y = R.run(net, w, p, np.float64)
                wd = max(wd, float(np.max(np.abs(y - np.array(P.target(c, list(w)))))))
            worst[mult] = round(wd, 3)
        print(fam, c["id"], "V", c["V"], "worst dev by multiple of tau:", worst, flush=True)
