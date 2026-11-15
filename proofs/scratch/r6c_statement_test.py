"""Numeric test of the rung-6c candidate statements BEFORE pre-registration (exact rationals).

For the ten proved rung-2 networks (exported exact weights):
 A. the decidable condition tokenBlind(N, T) exactly as it will be stated in Lean
    (shape, T inside the embedding coordinates, real tokens agree off T, every head is
    either [score matrix zero and mask all] or [score and value never touch T], MLP first
    layers never touch T, read-out never touches T), with T = the coordinates on which two
    real tokens differ;
 B. members: the INVARIANCE conclusion. Two networks that differ only in embedding
    entries on T (all other weights equal, here also randomly perturbed, the same in
    both), two inputs of the same length with equal column sums of the embedded tokens on
    T  =>  equal outputs at EVERY position. Tested on (i) permutations of one input,
    (ii) the collision pairs of the statement;
 C. members: the COLLISION statement: for a, b >= 1 and 1 <= tau*(2a+1), 1 <= tau*(2b+1),
    tau <= 1 there are N1, N2 in the relative ball with equal outputs at every position on
    s^a o^(b+1) and s^(a+1) o^b; and one of the two is then wrong for the task
    (parity: sign at the last position; sort: the value at position a+1);
 D. non-members: the unperturbed network is NOT permutation-invariant (two orderings of
    one input give different outputs), so no statement of type B can hold for it.
"""
import copy, itertools, json, os, random, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
import seqnet as S, collect2_lib as CL

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
random.seed(606)
NTOK = {"p05": 4, "p10": 3, "p29": 4, "s00": 2, "s01": 3, "d10": 4, "d15": 4, "d18": 4}
PAR = {"p05": ([1, 3, 4], 0), "p10": ([1, 2], 0), "p29": ([2, 3], 1)}


def token_coords(net):
    E = net["embed"]
    return [c for c in range(len(E[0])) if len({E[t][c] for t in range(1, len(E))}) > 1]


def token_blind(net, T, ntok):
    E = net["embed"]
    de = len(E[0])
    d = de + 8
    why = []
    if not (len(E) == ntok + 1 and all(len(r) == de for r in E) and d <= 24 and len(net["outW"]) == d):
        why.append("shape")
    if not all(c < de for c in T):
        why.append("T outside the embedding coordinates")
    if any(E[t][c] != E[1][c] for c in range(de) if c not in T for t in range(1, ntok + 1)):
        why.append("real tokens differ off T")
    for b, B in enumerate(net["blocks"]):
        for h, hd in enumerate(B["heads"]):
            A, V = hd["A"], hd["V"]
            uniform = hd["mask"] == "all" and all(v == 0 for r in A for v in r)
            blind_s = all(A[p][q] == 0 for p in range(d) for q in range(d) if p in T or q in T)
            blind_v = all(V[r][c] == 0 for r in range(d) for c in T)
            if not (uniform or (blind_s and blind_v)):
                why.append("block %d head %d (mask %s): %s" % (b + 1, h + 1, hd["mask"],
                           "score reads T" if not blind_s else "value reads T and the head is not a global uniform average"))
        if any(row[c] != 0 for row in B["W1"] for c in T):
            why.append("block %d MLP reads T" % (b + 1))
    if any(net["outW"][c] != 0 for c in T):
        why.append("read-out reads T")
    return why


def perturb_rest(net, tau):
    """Random relative perturbation of every non-embedding weight (zeros stay zero)."""
    N = copy.deepcopy(net)
    f = lambda v: v * (1 + F(random.randint(-1000, 1000), 1000) * tau)
    for B in N["blocks"]:
        for hd in B["heads"]:
            hd["A"] = [[f(v) for v in r] for r in hd["A"]]
            hd["V"] = [[f(v) for v in r] for r in hd["V"]]
        B["W1"] = [[f(v) for v in r] for r in B["W1"]]; B["b1"] = [f(v) for v in B["b1"]]
        B["W2"] = [[f(v) for v in r] for r in B["W2"]]; B["b2"] = [f(v) for v in B["b2"]]
    N["outW"] = [f(v) for v in N["outW"]]; N["outB"] = f(N["outB"])
    return N


def scale_rows(net, T, factors):
    """Embedding entries on T of token t multiplied by factors[t]."""
    N = copy.deepcopy(net)
    for t, fac in factors.items():
        for c in T:
            N["embed"][t][c] = N["embed"][t][c] * fac
    return N


res = {}
for d in sorted(os.listdir(os.path.join(HERE, "runs", "rung2-test", "net"))):
    p = os.path.join(HERE, "runs", "rung2-test", "net", d, "net.json")
    if not os.path.exists(p):
        continue
    net = CL.load_net(p)
    ntok = len(net["embed"]) - 1
    T = token_coords(net)
    why = token_blind(net, T, ntok)
    r = {"ntok": ntok, "T": T, "token_blind": not why, "why_not": why}
    toks = list(range(1, ntok + 1))
    if why:
        # D: not permutation-invariant
        found = None
        for L in (2, 3, 4):
            for w in itertools.product(toks, repeat=L):
                o1 = S.run(net, list(w))
                for w2 in set(itertools.permutations(w)):
                    if S.run(net, list(w2)) != o1:
                        found = (list(w), list(w2))
                        break
                if found:
                    break
            if found:
                break
        r["not_permutation_invariant_witness"] = found
    else:
        # B(i): permutations, with every other weight perturbed (the same in both networks)
        okB = True
        for trial in range(30):
            L = random.randint(2, 9)
            w = [random.choice(toks) for _ in range(L)]
            w2 = w[:]
            random.shuffle(w2)
            M = perturb_rest(net, F(1, 50))
            M = scale_rows(M, T, {t: 1 + F(random.randint(-20, 20), 1000) for t in toks})
            okB &= S.run(M, w) == S.run(M, w2)
        r["invariance_under_permutation_30_trials"] = okB
        # C and B(ii): collision pairs
        s, o = (PAR[d][0][0], [t for t in toks if t not in PAR[d][0]][0]) if d in PAR else (1, 2)
        okC, wrongC = True, True
        for (a, b) in ((1, 1), (2, 3), (4, 4), (5, 2)):
            tau = max(F(1, 2 * a + 1), F(1, 2 * b + 1))
            d1s, d2s = (1 - tau * (a + 1)) / a, -tau            # a(1+d1s) = (a+1)(1+d2s)
            d1o, d2o = -tau, (1 - tau * (b + 1)) / b            # (b+1)(1+d1o) = b(1+d2o)
            assert max(abs(d1s), abs(d2s), abs(d1o), abs(d2o)) <= tau <= 1
            M = perturb_rest(net, F(1, 50)) if (a, b) != (4, 4) else copy.deepcopy(net)
            N1 = scale_rows(M, T, {s: 1 + d1s, o: 1 + d1o})
            N2 = scale_rows(M, T, {s: 1 + d2s, o: 1 + d2o})
            w1, w2 = [s] * a + [o] * (b + 1), [s] * (a + 1) + [o] * b
            o1, o2 = S.run(N1, w1), S.run(N2, w2)
            okC &= o1 == o2
            if (a, b) == (4, 4):                                # only embedding moved: is one answer wrong?
                if d in PAR:
                    cnt, par = PAR[d]
                    good = lambda w: sum(t in cnt for t in w) % 2 == par
                    wrongC &= ((o1[-1] > 0) != good(w1)) or ((o2[-1] > 0) != good(w2))
                else:
                    wrongC &= (o1[a + 1] != sorted(w1)[a]) or (o2[a + 1] != sorted(w2)[a])
        r["collision_equal_outputs_all_positions"] = okC
        r["collision_one_answer_wrong"] = wrongC
        r["collision_tokens"] = [s, o]
    res[d] = r
    print(d, json.dumps(r), flush=True)
json.dump(res, open(os.path.join(HERE, "results", "r6c-statement-test.json"), "w"), indent=1)
