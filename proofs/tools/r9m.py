"""Rung 9-LN-M (PREREG_R9M.md): the FROZEN rung 9-LN15 recipe, screen, mirror and generator on a new task.
No frozen file is edited: the task (Python target, automaton, Lean definitions) is passed into the frozen tools
from here, at run time.

    python tools/r9m.py train <task> <seed0> <seed1>            train recipe n1 + screen
    python tools/r9m.py gen <task> <dir> [generator options]    per-network Lean files (tools/make_r9ln15_net.py main)
    python tools/r9m.py ctl <task> <seed>                       control copies of one fresh network's skeleton
    python tools/r9m.py checks <task> <seed> ...                numericchecks (tools/ln15_checks.py with the task passed in)

Tasks (five tokens = digits 0..4, token t is digit t - 1; before position 1 the digit is 0):
    M   the larger of the digits of the current and the previous token      (the registered task)
    E   1 if the current token equals the previous one, else 0              (the probe task of SCOPE_CLEAN.md; plumbing test only)
The Lean `target` is the task automaton run on the first i - 1 tokens, so `task.target w i = target w i` holds by `rfl`
(as rung 7's task B did); no proof text is added.
"""
import json, os, runpy, sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

TEQ_RFL = ("theorem target_eq (w : List ℕ) (i : ℕ) (_h1 : 1 ≤ i) (_h2 : i ≤ w.length) :\n"
           "    task.target w i = target w i := rfl")
TASKS = {
    "M": dict(
        py=lambda w: [max(int(w[i]) - 1, (int(w[i - 1]) - 1) if i else 0) for i in range(len(w))],
        dfa=(0, (lambda s, t: t - 1), (lambda s, t: max(s, t - 1))),
        defs=["/-- Target at position `i`: the larger of the digits of tokens `i` and `i - 1` (token `t` is digit",
              "`t - 1`; before position 1 the digit is 0). Written as the task automaton: the state after the first",
              "`i - 1` tokens is the digit of token `i - 1`. -/",
              "def target (w : List ℕ) (i : ℕ) : ℕ :=",
              "  max ((w.take (i - 1)).foldl (fun _ t => t - 1) 0) (w.getD (i - 1) 0 - 1)"],
        task="def task : Task :=\n  { ntok := 5, init := 0,\n    step := fun _ t => t - 1,\n    out := fun s t => max s (t - 1) }\n"),
    "E": dict(
        py=lambda w: [1 if (i > 0 and int(w[i]) == int(w[i - 1])) else 0 for i in range(len(w))],
        dfa=(0, (lambda s, t: t), (lambda s, t: 1 if s == t else 0)),
        defs=["/-- Target at position `i`: 1 if token `i` equals token `i - 1`, else 0 (0 at position 1). Written as the",
              "task automaton: the state after the first `i - 1` tokens is token `i - 1` (0 at the start). -/",
              "def target (w : List ℕ) (i : ℕ) : ℕ :=",
              "  if (w.take (i - 1)).foldl (fun _ t => t) 0 = w.getD (i - 1) 0 then 1 else 0"],
        task="def task : Task :=\n  { ntok := 5, init := 0,\n    step := fun _ t => t,\n    out := fun s t => if s = t then 1 else 0 }\n"),
}


def patch(name):
    """Pass the task into the frozen modules (their files are not touched)."""
    import r9ln as L, r7_cert as RC, make_r7_net as M7, make_r8_net as M8, make_r7_cases as MC
    T = TASKS[name]
    L.target = T["py"]
    RC.task_dfa = lambda _n: T["dfa"]
    MC.task_parts = lambda _c: (T["defs"], "")
    M7.TASKDEF["A"] = T["task"]
    M8.TEQ["A"] = TEQ_RFL
    return L


if __name__ == "__main__":
    import r5_checks as C5
    C5.memory_guard(1.5)
    cmd, name = sys.argv[1], sys.argv[2]
    base = os.path.join(HERE, "runs", "r9m-fresh" if name == "M" else "r11-probe/" + name)
    if cmd == "train":
        import time
        L = patch(name)
        for seed in range(int(sys.argv[3]), int(sys.argv[4]) + 1):
            t0 = time.time()
            d = os.path.join(base, "A", "n1", "s%03d" % seed)          # "A" is the frozen trainer's fixed sub-folder name
            if not os.path.exists(os.path.join(d, "T.json")): L.train("n1", seed, base)
            if not os.path.exists(os.path.join(d, "screen.json")): L.screen(d)
            L.line(d, t0)
    elif cmd == "gen":
        patch(name)
        import make_r9ln15_net as G
        sys.argv = [sys.argv[0]] + sys.argv[3:]
        G.main()
    elif cmd == "ctl":
        import copy
        seed = int(sys.argv[3]); src = os.path.join(base, "A", "n1", "s%03d" % seed)
        W = json.load(open(os.path.join(src, "W14.json"))); tj = json.load(open(os.path.join(src, "train.json")))
        fr = lambda v: "%d/%d" % F(v).as_integer_ratio(); neg = lambda v: fr(-F(v)); V = {}
        a = copy.deepcopy(W); a["embed"][1], a["embed"][2] = a["embed"][2], a["embed"][1]; V["swap12"] = a
        a = copy.deepcopy(W); a["outW"] = [neg(v) for v in a["outW"]]; a["outB"] = neg(a["outB"]); V["negout"] = a
        a = copy.deepcopy(W); a["outB"] = fr(F(a["outB"]) + F(1, 2)); V["bias_half"] = a
        a = copy.deepcopy(W); a["ln"]["ln2"]["g"] = [neg(v) for v in a["ln"]["ln2"]["g"]]; V["ln2neg"] = a
        V["rad16"] = copy.deepcopy(W); V["rad64"] = copy.deepcopy(W); V["taskA"] = copy.deepcopy(W)
        for nm, net in V.items():
            d = os.path.join(HERE, "runs", "r9m-ctl", nm); os.makedirs(d, exist_ok=True)
            json.dump(net, open(os.path.join(d, "W14.json"), "w")); json.dump(tj, open(os.path.join(d, "train.json"), "w"))
            print("wrote", nm)
    elif cmd == "checks":
        patch(name)
        sys.argv = [os.path.join(HERE, "tools", "ln15_checks.py"), os.path.relpath(base, HERE)] + sys.argv[3:]
        runpy.run_path(sys.argv[0], run_name="__main__")
