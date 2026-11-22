"""Build a rung 9-LN15 kit case folder from its hand-written HEAD.md (PREREG_R9LN15.md, stage 1).

    python tools/make_ln_kit.py <case id> ...

Writes Spec.lean (empty namespace: the statements are in the imported module Lane4/LNDefs.lean, namespace
Lane4.LNC), Final.lean, case.json, TASK.md (HEAD.md + the standing rules of the rung-7 kit) and copies of the
framework files the case names. Text work only; no numerics.
"""
import json, os, shutil, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(HERE)
nl = "\n"
BASE = ["LNNet.lean", "LNCert.lean", "LNDefs.lean", "AGate.lean", "RSoft.lean", "RSeq.lean", "R7Cert.lean", "R8Cert.lean", "R8Defs.lean", "R7K2.lean"]

# id -> (import module, [(statement, theorem name)], [extra files copied into the folder])
CASES = {
    "la": ("LNDefs", [("RsumRel", "rsum_rel"), ("ArdotRel", "ardot_rel"), ("PdotRel", "pdot_rel"), ("DotRelSound", "dot_rel_sound"),
                      ("ScoreRelSound", "score_rel_sound")], ["AGateKit.lean", "AGateKitW.lean"]),
    "lb": ("LNKA", [("ScoreWinLN", "score_win_ln")], ["AGateKit.lean", "Seq.lean", "R7K3.lean", "R8KA.lean", "LNKA.lean"]),
    "lc": ("LNB2", [("HeadSoundLN", "head_sound_ln")],
           ["Seq.lean", "RSoftKit.lean", "R8Soft.lean", "R7K3.lean", "R8KA.lean", "R8KB.lean", "R8KC.lean", "R8KD.lean", "R8KE.lean", "R8KG.lean",
            "LNKA.lean", "LNKB.lean"]),
    "ld": ("LNDefs", [("FrameFF", "frame_ff"), ("ZeroFacts", "zero_facts"), ("BoxSound", "box_sound"), ("AddFSound", "add_f_sound"),
                      ("ReluFSound", "relu_f_sound"), ("ResFSound", "res_f_sound"), ("HoFSound", "ho_f_sound")], ["R8KE.lean"]),
    "le": ("LNB1", [("DotFSound", "dot_f_sound")], ["LNKA.lean", "LNKD.lean"]),
    "lf": ("LNB1", [("CentSound", "cent_sound"), ("VarSound", "var_sound")], ["LNKA.lean", "LNKD.lean"]),
    "lg": ("LNDefs", [("RinvSound", "rinv_sound")], []),
    "lh": ("LNB3", [("LnFSound", "ln_f_sound")], ["LNKA.lean", "LNKD.lean", "LNKF.lean", "LNKG.lean"]),
    "lj": ("LNT", [("Lane4.LNT.OutShiftL", "out_shift_l"), ("Lane4.LNT.DiffWithinL", "diff_within_l")], ["LNT.lean", "R7KT.lean"]),
    "li": ("LNB4", [("Lane4.LNC.SoundLN", "sound_ln")],
           ["Seq.lean", "R7K5.lean", "R8KF.lean", "R8K.lean", "LNKC.lean", "LNKD.lean", "LNKE.lean", "LNKH.lean"]),
}
KIT = "runs/r9ln15-kit/"


def mk(cid):
    imp, names, copies = CASES[cid]
    K = KIT + cid + "/"
    os.makedirs(K + "scratch", exist_ok=True)
    for c in BASE + copies:
        shutil.copy("Lane4/" + c, K + c)
    open(K + "Spec.lean", "w", encoding="utf-8", newline=nl).write("namespace Lane4.Case" + nl + "end Lane4.Case" + nl)
    st = lambda a: a if a.startswith("Lane4.") else "Lane4.LNC." + a
    body = ("⟨" + ", ".join("Lane4.Case." + b for _, b in names) + "⟩") if len(names) > 1 else "Lane4.Case." + names[0][1]
    fin = ("namespace Lane4Final" + nl + "theorem final : " + " ∧ ".join(st(a) for a, _ in names) + " :=" + nl
           + "  " + body + nl + "end Lane4Final" + nl + "#print axioms Lane4Final.final" + nl)
    open(K + "Final.lean", "w", encoding="utf-8", newline=nl).write(fin)
    json.dump({"id": cid, "arm": "kit", "rung": 9, "import": imp, "final_theorems": ["Lane4Final.final"],
               "max_attempts": 30, "lean_timeout": 600}, open(K + "case.json", "w"))
    t = open("runs/r7-kit/kT/TASK.md", encoding="utf-8").read()
    rules = t[t.index("## Rules"):].replace("r7-kit/kT", "r9ln15-kit/" + cid)
    head = open(K + "HEAD.md", encoding="utf-8").read()
    open(K + "TASK.md", "w", encoding="utf-8", newline=nl).write(head.rstrip() + nl + nl + rules)
    print("built", cid, "| import", imp, "| copies", len(BASE + copies))


if __name__ == "__main__":
    for c in sys.argv[1:]:
        mk(c)
