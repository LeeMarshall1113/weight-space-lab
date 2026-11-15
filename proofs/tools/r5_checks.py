"""Rung-5 lane checks on exported nets (PREREG_R5.md, "Checks the lane runs"). numpy + torch, CPU.

    python tools/r5_checks.py runs/rung5-test [--quick]   -> <case>/r5_checks.json per net
    python tools/r5_checks.py exp                          -> results/r5-exp-check.json
    (budget a few GB of RAM)

Fixed before any run:
  inside   : 40 uniform + 40 sign-corner relative perturbations at tau, float64 (float64 exp),
             each on a fresh input (lengths 6, 40, 300, 2000; four input patterns).
  outside  : 30 sign-corner perturbations at s*tau for s = 2, 4, ..., 64, lengths up to 20,000.
  binary32 : numpy float32 in the stated order, written weights and 5 sign-corner
             perturbations at tau, at 1,000 / 16,000 / 65,534 tokens. The PyTorch module's
             forward must agree bit for bit; forward_fast (torch.softmax, matmul) is
             compared with the target only.
  beyond   : one-block nets, 200,000 tokens, written weights, numpy float32.
  exp      : float32 exp of numpy and torch against float64 exp on 200,000 arguments in
             [-110, 0]: worst |ex x - e^x| / (4 u e^x + eta), u = 2^-24, eta = 2^-149.
A deviation is |output - target|; the tolerance is 1/4.
"""
import glob, json, os, sys, time
from fractions import Fraction as F
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r5net as R, r4pool as P, r4_checks as C4

HERE = P.HERE
TOL = 0.25


def dev(net, c, w, pert, dtype, q):
    y = R.run(net, w, pert, dtype, q)
    tgt = np.array(P.target(c, [int(t) for t in w]), dtype=np.float64)[q - 1]
    return float(np.max(np.abs(y - tgt))), y, tgt


def check(casedir, c, quick=False):
    net = C4.load_net(os.path.join(casedir, "net.json"))
    tau = float(F(json.load(open(os.path.join(casedir, "case.json")))["tau"]))
    rng = np.random.default_rng(51)
    k = 5 if quick else 1
    res = {"id": c["id"], "family": c["family"], "tau": tau, "blocks": len(net["blocks"]),
           "heads": [len(B["heads"]) for B in net["blocks"]], "width": len(net["outW"]),
           "mlp_hidden": [len(B["b1"]) for B in net["blocks"]],
           "max_abs_weight": max([abs(v) for r in net["embed"] for v in r] +
                                 [abs(v) for B in net["blocks"] for h in B["heads"] for M in (h["A"], h["V"]) for r in M for v in r])}
    res["written_exact_max_dev"] = max(dev(net, c, w, None, np.float64, C4.queries(len(w), rng))[0]
                                       for w in (C4.gen_input(c, n, rng) for n in (6, 40, 300, 2000)))
    inside = {}
    for kind in ("uniform", "sign"):
        worst = 0.0
        for t in range(40 // k):
            w = C4.gen_input(c, int(rng.choice([6, 40, 300, 2000])), rng)
            worst = max(worst, dev(net, c, w, R.random_pert(net, tau, rng, kind), np.float64, C4.queries(len(w), rng))[0])
        inside[kind] = worst
    res["inside_ball_max_dev"] = inside
    res["inside_ball_ok"] = bool(max(inside.values()) <= TOL)
    res["outside"], res["smallest_violating_multiple"] = {}, None
    for s in (2, 4, 8, 16, 32, 64):
        worst = 0.0
        for t in range(30 // k):
            w = C4.gen_input(c, int(rng.choice([6, 40, 300, 2000, 20000])), rng)
            worst = max(worst, dev(net, c, w, R.random_pert(net, s * tau, rng, "sign"), np.float64, C4.queries(len(w), rng))[0])
            if worst > TOL:
                break
        res["outside"][str(s)] = worst
        if worst > TOL:
            res["smallest_violating_multiple"] = s
            break
    f32, mism, compared, fast_worst = {}, 0, 0, 0.0
    for n in (1000, 16000, 65534):
        w = C4.gen_input(c, n, rng)
        q = C4.queries(n, rng, cap=1000)
        worst = 0.0
        for t in range(1 + (5 // k or 1)):
            p = None if t == 0 else R.random_pert(net, tau, rng, "sign")
            d, y, tgt = dev(net, c, w, p, np.float32, q)
            worst = max(worst, d)
            mod = R.make_torch_module(net, p)
            yt = mod(w, q).numpy().astype(np.float64)
            mism += int(np.sum(yt != y)); compared += len(y)
            yf = mod.forward_fast(w, q).numpy().astype(np.float64)
            fast_worst = max(fast_worst, float(np.max(np.abs(yf - tgt))))
        f32[str(n)] = worst
    res["float32_max_dev"] = f32
    res["float32_ok_in_range"] = bool(max(f32.values()) <= TOL)
    res["torch_reference_mismatches"] = mism
    res["torch_reference_outputs_compared"] = compared
    res["torch_fast_max_dev"] = fast_worst
    if len(net["blocks"]) == 1 and not quick:
        w = C4.gen_input(c, 200000, rng)
        res["float32_beyond_200000"] = dev(net, c, w, None, np.float32, C4.queries(200000, rng, cap=1000))[0]
    json.dump(res, open(os.path.join(casedir, "r5_checks.json"), "w"), indent=1)
    print(c["id"], c["family"], "blocks", res["blocks"], "width", res["width"],
          "| exact %.3g" % res["written_exact_max_dev"],
          "| inside %.3f ok=%s" % (max(inside.values()), res["inside_ball_ok"]),
          "| breaks at %s tau" % res["smallest_violating_multiple"],
          "| f32 %.3f" % max(f32.values()), "| torch mismatches %d/%d" % (mism, compared),
          "| torch fast %.3f" % fast_worst, "| beyond %s" % res.get("float32_beyond_200000"), flush=True)
    return res


def exp_check():
    import torch
    rng = np.random.default_rng(7)
    x = np.concatenate([rng.uniform(-110, 0, 180000), -np.abs(rng.normal(0, 1e-3, 5000)),
                        rng.uniform(-104.5, -86.5, 15000), [0.0]]).astype(np.float32)
    ref = np.exp(x.astype(np.float64))
    u, eta = 2.0 ** -24, 2.0 ** -149
    out = {"n": int(len(x)), "numpy": np.__version__, "torch": torch.__version__}
    for name, y in (("numpy", np.exp(x)), ("torch", torch.exp(torch.from_numpy(x)).numpy())):
        y = y.astype(np.float64)
        ratio = np.abs(y - ref) / (4 * u * ref + eta)
        normal = x > -87.0
        out[name] = {"worst_ratio": float(ratio.max()), "at_x": float(x[int(ratio.argmax())]),
                     "worst_ratio_normal_range": float(ratio[normal].max()),
                     "worst_relative_error_over_u_normal_range": float((np.abs(y - ref) / (u * ref))[normal].max()),
                     "negative_outputs": int(np.sum(y < 0)), "exp0_is_1": bool(y[-1] == 1.0),
                     "worst_ulp_estimate": float((np.abs(y - ref) / np.maximum(np.spacing(y.astype(np.float32)).astype(np.float64), eta)).max())}
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    json.dump(out, open(os.path.join(HERE, "results", "r5-exp-check.json"), "w"), indent=1)
    print(json.dumps(out, indent=1))


def memory_guard(limit_gb=2.5):
    """Exit the process if its commit charge passes the limit (added after the 2026-11-14
    kill: an unchunked n x n matrix reached 16 GB under a 3 GB reservation)."""
    import ctypes, ctypes.wintypes as wt, threading

    class PMC(ctypes.Structure):
        _fields_ = [("cb", wt.DWORD), ("PageFaultCount", wt.DWORD),
                    ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                    ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                    ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t)]
    k32, psapi = ctypes.windll.kernel32, ctypes.windll.psapi
    k32.GetCurrentProcess.restype = wt.HANDLE
    psapi.GetProcessMemoryInfo.argtypes = [wt.HANDLE, ctypes.POINTER(PMC), wt.DWORD]
    h = k32.GetCurrentProcess()

    def watch():
        while True:
            pmc = PMC(); pmc.cb = ctypes.sizeof(PMC)
            if psapi.GetProcessMemoryInfo(h, ctypes.byref(pmc), pmc.cb) and                     max(pmc.PagefileUsage, pmc.WorkingSetSize) > limit_gb * 2 ** 30:
                print("memory guard: commit %.1f GB over the %.1f GB limit, exiting" % (pmc.PagefileUsage / 2 ** 30, limit_gb), flush=True)
                os._exit(3)
            time.sleep(0.5)
    threading.Thread(target=watch, daemon=True).start()


if __name__ == "__main__":
    memory_guard()
    if sys.argv[1] == "exp":
        exp_check()
    else:
        root = os.path.abspath(sys.argv[1])
        pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
        t0 = time.time()
        for d in sorted(glob.glob(os.path.join(root, "net*", "*"))):
            if os.path.exists(os.path.join(d, "net.json")) and not os.path.exists(os.path.join(d, "r5_checks.json")):
                check(d, pool[os.path.basename(d)], "--quick" in sys.argv)
        print("done in %.0f s" % (time.time() - t0))
