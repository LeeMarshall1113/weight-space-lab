"""Build a rung-8 kit case folder from its hand-written Spec.lean and HEAD.md.

    python tools/make_r8_kit.py <case id>

Adds Final.lean, case.json, TASK.md (HEAD.md + the standing rules of the rung-7 kit) and copies of the
framework files the case names. Text work only; no numerics.
"""
import json, os, shutil, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(HERE)
nl = "\n"

# id -> (import module, [(statement, theorem name)], [files copied into the folder])
CASES = {
    "ka": ("R8Defs", [("ScoreWin", "score_win")],
           ["AGate.lean", "AGateKit.lean", "RSoft.lean", "RSeq.lean", "Seq.lean", "R7Cert.lean", "R8Cert.lean", "R8Defs.lean",
            "R7K2.lean", "R7K3.lean"]),
    "kb": ("R8Soft", [("SavgArith", "savg_arith")], ["RSoftKit.lean", "RSoft.lean", "RSeq.lean", "R8Soft.lean", "R7K1.lean"]),
    "kc": ("R8Cert", [("RoundSound", "round_sound"), ("ExpEncl", "exp_encl")], ["R8Cert.lean", "R7Cert.lean"]),
    "kd": ("R8Soft", [("MixBound", "mix_bound")], ["R8Soft.lean"]),
    "ke": ("R8Defs", [("AFRange", "af_range"), ("EmbAF", "emb_af"), ("DotAF", "dot_af"), ("AffAF", "aff_af"),
                      ("AddAF", "add_af"), ("ReluAF", "relu_af"), ("ShiftAF", "shift_af")],
           ["AGate.lean", "AGateKit.lean", "AGateKitW.lean", "RSoft.lean", "RSeq.lean", "R7Cert.lean", "R8Cert.lean", "R8Defs.lean", "R7K2.lean"]),
    "kf": ("R8Defs", [("AbsClosed8", "abs_closed8"), ("AbsLen8", "abs_len8"), ("AbsTarget8", "abs_target8"), ("AbsKeys8", "abs_keys8")],
           ["R8Defs.lean", "R8Cert.lean", "R7Cert.lean", "Seq.lean", "R7K4.lean", "R7Defs.lean"]),
    "kg": ("R8B2", [("HeadSound8", "head_sound8")],
           ["AGate.lean", "RSoft.lean", "RSoftKit.lean", "RSeq.lean", "Seq.lean", "R7Cert.lean", "R8Cert.lean", "R8Defs.lean", "R8Soft.lean",
            "R7K2.lean", "R7K3.lean", "R8KA.lean", "R8KB.lean", "R8KC.lean", "R8KD.lean", "R8KE.lean"]),
    "kh": ("R8B3", [("Lane4.Cert8.Sound8", "sound8")],
           ["AGate.lean", "RSeq.lean", "Seq.lean", "R7Cert.lean", "R8Cert.lean", "R8Defs.lean", "R7K2.lean", "R7K5.lean",
            "R8KE.lean", "R8KF.lean", "R8KG.lean"]),
}


def mk(cid):
    imp, names, copies = CASES[cid]
    K = "runs/r8-kit/%s/" % cid
    os.makedirs(K + "scratch", exist_ok=True)
    for c in copies:
        shutil.copy("Lane4/" + c, K + c)
    st = lambda a: a if a.startswith("Lane4.") else "Lane4.Case." + a
    body = ("⟨" + ", ".join("Lane4.Case." + b for _, b in names) + "⟩") if len(names) > 1 else "Lane4.Case." + names[0][1]
    fin = ("namespace Lane4Final" + nl + "theorem final : " + " ∧ ".join(st(a) for a, _ in names) + " :=" + nl
           + "  " + body + nl + "end Lane4Final" + nl + "#print axioms Lane4Final.final" + nl)
    open(K + "Final.lean", "w", encoding="utf-8", newline=nl).write(fin)
    json.dump({"id": cid, "arm": "kit", "rung": 8, "import": imp, "final_theorems": ["Lane4Final.final"],
               "max_attempts": 30, "lean_timeout": 600}, open(K + "case.json", "w"))
    t = open("runs/r7-kit/kT/TASK.md", encoding="utf-8").read()
    rules = t[t.index("## Rules"):].replace("r7-kit/kT", "r8-kit/" + cid)
    head = open(K + "HEAD.md", encoding="utf-8").read()
    open(K + "TASK.md", "w", encoding="utf-8", newline=nl).write(head.rstrip() + nl + nl + rules)
    print("built", cid, "| import", imp, "| copies", len(copies))


if __name__ == "__main__":
    for c in sys.argv[1:]:
        mk(c)
