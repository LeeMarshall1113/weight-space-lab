"""Lane 4 checker: one command checks one case.

    python tools/check.py <casedir> [--timeout 600] [--json out.json]

A case directory holds
    case.json      {"arm": "net" | "prog", ...}
    Spec.lean      written by the lane (spec + Statement), no imports
    Solution.lean  written by the doctor, no imports
    Final.lean     written by the lane (the theorem that must type-check)

The checker (1) scans Solution.lean for banned tokens, (2) concatenates
`import Lane4.Basic` + Spec + Solution + Final into _Full.lean, (3) runs the
Lean 4 kernel on it against a built Mathlib (see README.md, "Setup"),
(4) requires exit 0, no `sorry`, and axioms within the standard three.

It never calls lake and never downloads anything. Budget about 8 GB of RAM for the
largest proofs. Settings (environment variables, all optional):
    LANE4_LEAN             path of the lean executable (default: `lean` on PATH)
    LANE4_MATHLIB_PROJECT  folder holding .lake/packages/*/.lake/build/lib/lean
                           (default: the folder containing this repository)
    LANE4_MEM_KILL_GB      per-check memory kill threshold (default 4.5)
"""
import ctypes, ctypes.wintypes as wt, glob, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # repository root
MATHLIB_PROJECT = os.environ.get("LANE4_MATHLIB_PROJECT", HERE)
LEAN = os.environ.get("LANE4_LEAN", "lean")
BUILD = os.path.join(HERE, "build")
MEM_KILL_GB = float(os.environ.get("LANE4_MEM_KILL_GB", "4.5"))
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

BANNED = (r"sorry|admit|axiom|native_decide|ofReduceBool|macro|macro_rules|syntax|notation|"
          r"infix|infixl|infixr|prefix|postfix|elab|elab_rules|declare_syntax_cat|unsafe|"
          r"implemented_by|extern|import|run_cmd|run_elab|initialize|instance|opaque|"
          r"partial|csimp|Lane4Final")
BANNED_RE = re.compile(r"(?<![\w.])(" + BANNED + r")(?![\w])|#eval|#exit|open\s+Lean\b|\bLean\.")
# "prog" arm: the program part (above the `-- PROOF` line) must branch explicitly.
PROG_BANNED_RE = re.compile(r"(?<![\w.])(max|min|abs|relu|spec|Max\.max|Min\.min)(?![\w])|[⊔⊓|]")


def lean_path():
    libs = glob.glob(os.path.join(MATHLIB_PROJECT, ".lake", "packages", "*", ".lake", "build", "lib", "lean"))
    return os.pathsep.join([BUILD] + libs)


class PMC(ctypes.Structure):
    _fields_ = [("cb", wt.DWORD), ("PageFaultCount", wt.DWORD),
                ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t)]


def peak_mem(proc):
    """(peak working set GB, peak commit GB) of a finished subprocess."""
    try:
        pmc = PMC(); pmc.cb = ctypes.sizeof(PMC)
        f = ctypes.windll.psapi.GetProcessMemoryInfo
        f.argtypes = [wt.HANDLE, ctypes.POINTER(PMC), wt.DWORD]
        if f(int(proc._handle), ctypes.byref(pmc), pmc.cb):
            return round(pmc.PeakWorkingSetSize / 2**30, 2), round(pmc.PeakPagefileUsage / 2**30, 2)
    except Exception:
        pass
    return None, None


def run_lean(args, timeout, cwd):
    env = dict(os.environ, LEAN_PATH=lean_path())
    env.pop("LEAN_SYSROOT", None)
    t0 = time.time()
    p = subprocess.Popen([LEAN] + args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
    # Memory guard: a lean process whose working set passes MEM_KILL_GB is killed
    # (a 3,900-line generated proof reached 7.8 GB). The guard needs Windows (psapi).
    timed_out = mem_killed = False
    out = None
    while out is None:
        try:
            out, _ = p.communicate(timeout=0.5)
        except subprocess.TimeoutExpired:
            if time.time() - t0 > timeout:
                timed_out = True
            elif (peak_mem(p)[0] or 0) > MEM_KILL_GB:
                mem_killed = True
            if timed_out or mem_killed:
                (subprocess.run(["taskkill", "/F", "/T", "/PID", str(p.pid)], capture_output=True)
                 if os.name == "nt" else p.kill())
                out, _ = p.communicate()
    rss, commit = peak_mem(p)
    return {"rc": p.returncode, "out": out, "timed_out": timed_out, "mem_killed": mem_killed,
            "secs": round(time.time() - t0, 1), "peak_rss_gb": rss, "peak_commit_gb": commit}


# framework modules and what each imports
DEPS = {"Basic": [], "Seq": ["Basic"], "Robust": ["Basic"], "RSeq": ["Seq"], "RSoft": ["RSeq"],
        "RSoftKit": ["RSoft"], "Bin32": ["RSoft"], "RSoftAll": ["RSoftKit", "Bin32"],
        "QRSeq": ["RSeq"], "AGate": ["RSoftKit"], "AGateKit": ["AGate"], "AGateKitW": ["AGateKit"],
        "AGateAll": ["AGateKitW", "RSoftAll"],
        # rung 7: certificate checker and its kit modules
        "R7Cert": ["AGateAll"], "R7K1": ["RSoftKit"], "R7KT": ["AGateAll"],
        "R7K2": ["R7Cert"], "R7Defs": ["R7Cert"], "R7B3": ["R7K2", "R7K1", "R7Defs"],
        "R7K3": ["R7B3"], "R7K4": ["R7Defs"], "R7B5": ["R7K3", "R7K4"],
        "R7K5": ["R7B5"], "R7All": ["R7K5", "R7KT"], "R7Glue": ["R7All"],
        # rung 8
        "R8Cert": ["R7All"], "R8Glue": ["R8Cert", "R7Glue"], "R8Defs": ["R8Cert"], "R8Soft": ["RSoftKit"],
        "R8KA": ["R8Defs"], "R8KB": ["R8Soft"], "R8KC": ["R8Cert"], "R8KD": ["R8Soft"], "R8KE": ["R8Defs"], "R8KF": ["R8Defs"],
        "R8B2": ["R8KA", "R8KB", "R8KC", "R8KD", "R8KE"], "R8KG": ["R8B2"], "R8B3": ["R8KG", "R8KF"], "R8K": ["R8B3"],
        "R8All": ["R8K", "R8Glue"], "MechBisim": ["R7Cert"],
        # rung 9-LN15 (LayerNorm)
        "LNNet": ["R8All"], "LNCert": ["LNNet"], "LNDefs": ["LNCert"],
        "LNKA": ["LNDefs"], "LNKD": ["LNDefs"], "LNKG": ["LNDefs"], "LNB1": ["LNKA", "LNKD"],
        "LNKB": ["LNKA"], "LNB2": ["LNKA", "LNKB"], "LNKC": ["LNB2"], "LNKE": ["LNB1"], "LNKF": ["LNB1"],
        "LNB3": ["LNKA", "LNKD", "LNKF", "LNKG"], "LNKH": ["LNB3"],
        "LNB4": ["LNKC", "LNKD", "LNKE", "LNKH"], "LNKI": ["LNB4"], "LNAll": ["LNKI", "LNGlue", "LNKJ"],
        "LNGlue": ["LNCert"], "LNT": ["LNCert"], "LNKJ": ["LNT"]}


def ensure_basic(timeout=1800, name="Basic"):
    """Compile Lane4/<name>.lean to build/Lane4/<name>.olean if missing or stale."""
    for dep in DEPS.get(name, ["Basic"] if name != "Basic" else []):
        ensure_basic(timeout, dep)
    src = os.path.join(HERE, "Lane4", name + ".lean")
    olean = os.path.join(BUILD, "Lane4", name + ".olean")
    if os.path.exists(olean) and os.path.getmtime(olean) >= os.path.getmtime(src):
        return None
    os.makedirs(os.path.dirname(olean), exist_ok=True)
    r = run_lean([src, "-o", olean], timeout, HERE)
    if r["rc"] != 0 or r["timed_out"]:
        if os.path.exists(olean):
            os.remove(olean)
        raise SystemExit("Basic.lean failed to build:\n" + r["out"])
    return r


def strip_comments(s):
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    return re.sub(r"--.*", " ", s)


def scan(solution, arm, prog_banned=None):
    """Return a list of banned-token findings (empty = clean)."""
    found = []
    code = strip_comments(solution)
    for m in BANNED_RE.finditer(code):
        found.append(m.group(0).strip())
    if arm == "prog":
        if "-- PROOF" not in solution:
            found.append("missing `-- PROOF` marker line")
        else:
            top, bottom = solution.split("-- PROOF", 1)
            for m in (re.compile(prog_banned) if prog_banned else PROG_BANNED_RE).finditer(strip_comments(top)):
                found.append("program part uses `%s`" % m.group(0))
            if re.search(r"(?<![\w.])(def|abbrev|structure|inductive|class)(?![\w])", strip_comments(bottom)):
                found.append("definition below the `-- PROOF` marker")
    return sorted(set(found))


def check(casedir, timeout=600):
    casedir = os.path.abspath(casedir)
    meta = json.load(open(os.path.join(casedir, "case.json"), encoding="utf-8"))
    arm = meta.get("arm", "net")
    res = {"case": os.path.basename(casedir), "arm": arm, "pass": False, "time": time.strftime("%Y-%m-%d %H:%M:%S")}
    sol_path = os.path.join(casedir, "Solution.lean")
    if not os.path.exists(sol_path):
        res["reason"] = "no Solution.lean"
        return res
    read = lambda n: open(os.path.join(casedir, n), encoding="utf-8").read()
    solution = read("Solution.lean")
    banned = scan(solution, arm, meta.get("prog_banned"))
    res["native_decide_attempted"] = bool(re.search(r"native_decide|ofReduceBool", strip_comments(solution)))
    if banned:
        res["reason"] = "banned tokens: " + ", ".join(banned)
        return res
    module = meta.get("import", "Basic")          # rung 2 cases import Lane4.Seq
    assert module in DEPS
    full = "import Lane4.%s\n\n" % module + read("Spec.lean") + "\n\n" + solution + "\n\n" + read("Final.lean") + "\n"
    full_path = os.path.join(casedir, "_Full.lean")
    open(full_path, "w", encoding="utf-8", newline="\n").write(full)
    ensure_basic(name=module)
    r = run_lean([full_path], timeout, casedir)
    res.update({k: r[k] for k in ("rc", "timed_out", "mem_killed", "secs", "peak_rss_gb", "peak_commit_gb")})
    out = r["out"]
    # first errors matter most: keep the head and the tail
    res["lean_output"] = out if len(out) <= 6000 else out[:3500] + "\n[... output cut ...]\n" + out[-2500:]
    if r["timed_out"]:
        res["reason"] = "lean timed out after %ds" % timeout
        return res
    if r["mem_killed"]:
        res["reason"] = "lean passed the memory limit (%.1f GB); make the proof smaller" % MEM_KILL_GB
        return res
    if r["rc"] != 0 or re.search(r"(^|\n)[^\n]*: error", out):
        res["reason"] = "lean reported errors"
        return res
    if "declaration uses 'sorry'" in out or "sorryAx" in out:
        res["reason"] = "sorry"
        return res
    ax_lines = re.findall(r"'(Lane4Final\.\w+)' (depends on axioms: \[(.*?)\]|does not depend on any axioms)", out, flags=re.S)
    want = set(meta.get("final_theorems", ["Lane4Final.final"]))
    seen, axioms = set(), set()
    for name, _, lst in ax_lines:
        seen.add(name)
        axioms |= {a.strip() for a in lst.replace("\n", " ").split(",") if a.strip()}
    res["axioms"] = sorted(axioms)
    if not want <= seen:
        res["reason"] = "final theorems not all reported: missing %s" % sorted(want - seen)
        return res
    if not axioms <= ALLOWED_AXIOMS:
        res["reason"] = "non-standard axioms: %s" % sorted(axioms - ALLOWED_AXIOMS)
        return res
    res["pass"] = True
    res["reason"] = "kernel-checked"
    return res


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("casedir")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--json")
    a = ap.parse_args()
    r = check(a.casedir, a.timeout)
    if a.json:
        json.dump(r, open(a.json, "w", encoding="utf-8"), indent=1)
    print(("PASS" if r["pass"] else "FAIL") + "  " + r["case"] + "  " + r.get("reason", ""))
    for k in ("secs", "peak_rss_gb", "peak_commit_gb", "axioms"):
        if k in r:
            print("  %s: %s" % (k, r[k]))
    if not r["pass"] and r.get("lean_output"):
        print(r["lean_output"])
    sys.exit(0 if r["pass"] else 1)
