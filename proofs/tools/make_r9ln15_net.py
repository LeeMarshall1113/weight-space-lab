"""Rung 9-LN15: the per-network Lean files (PREREG_R9LN15.md, Amendment 1).

    python tools/make_r9ln15_net.py <run dir> [--net W14.json] [--radius 1/32768] [--tag name] [--per 260]
                                    [--no-trained] [--task-b]
        -> runs/r9ln15-nets/<tag>/A.lean [B.lean ...] Z.lean, meta.json     (compile with tools/build_ln_net.py)

Modules R9LN15.<tag>.A, .B, ...: definitions (in A) and one `decide +kernel` theorem per case, at most --per cases
per file. Z imports them: if the mirror (tools/r9ln15_cert.py) accepts, `accept : checkLN δ lnet task cert = true`
(pieces put together by checkLN_of), then skeleton_ok, exact_all_lengths, binary32, and, unless --no-trained,
trained_exact_all_lengths, trained_binary32 from Lane4.LNKI.sound_ln. If the mirror rejects at a case, the single
file Z proves that case false and `reject : checkLN ... = false`. If the mirror rejects before any case (no
certificate), no Lean file is written: the rejection is mirror-only and is reported so.
No doctor, no per-network proof."""
import json, os, sys
from fractions import Fraction as F
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r9ln15_cert as C, make_r7_ka as KA, make_r7_net as M7, make_r7_cases as MC, r7
q, nl = KA.q, "\n"
arg = lambda n, d=None: sys.argv[sys.argv.index(n) + 1] if n in sys.argv else d
iv = lambda p: "(%s, %s)" % (q(p[0]), q(p[1]))
ivs = lambda row: "[" + ", ".join(iv(p) for p in row) + "]"
ivm = lambda M: "[" + ("," + nl + "      ").join(ivs(r) for r in M) + "]"
zi = lambda v: "(%d)" % v if v < 0 else "%d" % v
zl = lambda l: "[" + ", ".join(zi(v) for v in l) + "]"
zm = lambda M: "[" + ("," + nl + "      ").join(zl(r) for r in M) + "]"
b = lambda x: "true" if x else "false"
NSP = ["namespace Lane4.LNNetFile", "open Lane4.RSeq (Vec)",
       "open Lane4.Case Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.LNT Lane4.Bin32",
       "open Lane4.Seq (Mask cand tokAt)", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""]
END = ["", "end Lane4.LNNetFile"]


def hcert(name, hc):
    return ("def %s : HCert :=" % name + nl + "  { cands := [%s], L := %d, spread := %s," % (", ".join(b(x) for x in hc["cands"]), hc["L"], q(hc["spread"]))
            + nl + "    S := %s," % ivm(hc["S"]) + nl + "    VE := %s," % ivm(hc["VE"]) + nl + "    Bv := %s }" % KA.L(hc["Bv"]))


def lnet(name, net):
    ln = net["ln"]
    return (KA.lean_net(name + "N", net) + nl + "def %s : LNNet :=" % name + nl + "  { net := %sN, g1 := %s, b1 := %s," % (name, KA.L(ln["ln1"]["g"]), KA.L(ln["ln1"]["b"])) + nl
            + "    g2 := %s, b2 := %s," % (KA.L(ln["ln2"]["g"]), KA.L(ln["ln2"]["b"])) + nl + "    gf := %s, bf := %s }" % (KA.L(ln["lnf"]["g"]), KA.L(ln["lnf"]["b"])))


STATEMENT = """def Statement (N : LNNet) : Prop :=
  ∀ (u η M : ℝ) (fl ex sq : ℝ → ℝ), Rnd u η M fl → ExpM u η ex → SqrtM u η sq →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : LPert, p.Within (%(RAD)s) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl ex sq p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4
"""

TAIL = """
%(TEQ)s

theorem rad_cast : (((%(RAD)s : ℚ)) : ℝ) = %(RAD)s := by norm_num

/-- The registered statement for the skeleton `lnet`: every network within the additive ball of
radius %(RAD)s (LayerNorm gains and biases included), every length the rounding model covers. -/
theorem skeleton_ok : Statement lnet := by
  have s := Lane4.LNKI.sound_ln
  unfold Lane4.LNC.SoundLN at s
  intro u η M fl ex sq hr he hs hu0 hu hη0 hη p hp w hw h1 h2 h3 i hi1 hi2
  have hp' : p.Within (((%(RAD)s : ℚ)) : ℝ) := by rw [rad_cast]; exact hp
  have h := s (%(RAD)s) lnet task cert accept u η M fl ex sq hr he hs hu0 hu hη0 hη p hp' w hw h1 h2 h3 i hi1 hi2
  rw [target_eq w i hi1 hi2] at h
  exact h

theorem exact_all_lengths (p : LPert) (hp : p.Within (%(RAD)s)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |LNNet.out lnet (fun x => x) Real.exp Real.sqrt p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  skeleton_ok 0 0 (2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2) (fun x => x) Real.exp Real.sqrt
    (rnd_id (by positivity)) expM_real sqrtM_real le_rfl (by positivity) le_rfl (by positivity)
    p hp w hw (by simp) (by simp) le_rfl i h1 h2

/-- binary32: `fl` is round-to-nearest on the binary32 range; `ex` and `sq` are ASSUMED to satisfy
the exponential and square-root models (binary32 square root is correctly rounded). -/
theorem binary32 (rn fl ex sq : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex) (hsq : SqrtM (1 / 2 ^ 24) (1 / 2 ^ 149) sq)
    (p : LPert) (hp : p.Within (%(RAD)s))
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |LNNet.out lnet fl ex sq p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  skeleton_ok (1 / 2 ^ 24) (1 / 2 ^ 149) maxF fl ex sq (bin32_rnd' hrn hfl) hex hsq (by positivity) le_rfl
    (by positivity) le_rfl p hp w hw (side_u hlen) (side_eta hlen) (range_ok hlen) i h1 h2
"""

TRAINED = """
/-! The network exactly as trained. -/

theorem same : sameShapeL lnet trained = true := by decide +kernel
theorem near : nearNetL (%(RAD)s) lnet trained = true := by decide +kernel

theorem trained_in_ball : (diffPL lnet trained).Within (%(RAD)s) := by
  have d := Lane4.LNKJ.diff_within_l
  unfold Lane4.LNT.DiffWithinL at d
  have h := d lnet trained (%(RAD)s) (by norm_num) same near
  rwa [rad_cast] at h

theorem shift (fl ex sq : ℝ → ℝ) (w : List ℕ) (i : ℕ) :
    LNNet.out lnet fl ex sq (diffPL lnet trained) w i = LNNet.out trained fl ex sq zeroPL w i := by
  have o := Lane4.LNKJ.out_shift_l
  unfold Lane4.LNT.OutShiftL at o
  exact o lnet trained same fl ex sq w i

/-- THE HEADLINE: the network AS TRAINED (float32 weights, no rounding of weights, no
perturbation), exact real arithmetic, every input length. -/
theorem trained_exact_all_lengths (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |LNNet.out trained (fun x => x) Real.exp Real.sqrt zeroPL w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  rw [← shift]
  exact exact_all_lengths _ trained_in_ball w hw i h1 h2

/-- The network AS TRAINED, binary32 arithmetic (exponential and square root assumed as in
`binary32`), at most 65,535 input tokens. -/
theorem trained_binary32 (rn fl ex sq : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex) (hsq : SqrtM (1 / 2 ^ 24) (1 / 2 ^ 149) sq)
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |LNNet.out trained fl ex sq zeroPL w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  rw [← shift]
  exact binary32 rn fl ex sq hrn hfl hex hsq _ trained_in_ball w hw hlen i h1 h2
"""


def main():
    import make_r8_net as M8
    d = os.path.abspath(sys.argv[1])
    delta = F(arg("--radius", "1/32768"))
    per = int(arg("--per", "260"))
    netf = arg("--net", "W14.json")
    trained = "--no-trained" not in sys.argv
    task_as = "B" if "--task-b" in sys.argv else "A"
    W = json.load(open(netf if os.path.isabs(netf) else os.path.join(d, netf)))
    tj = json.load(open(os.path.join(d, "train.json")))
    tag = arg("--tag", "s%d" % tj["seed"])
    ok, why, info = C.check(W, delta, task=task_as)
    out = os.path.join(HERE, "runs", "r9ln15-nets", tag)
    os.makedirs(out, exist_ok=True)
    for f in os.listdir(out):
        if f.endswith(".lean"): os.remove(os.path.join(out, f))
    meta = dict(tag=tag, dir=os.path.relpath(d, HERE).replace(os.sep, "/"), net=os.path.basename(netf), seed=tj["seed"], radius=str(delta),
                task_as=task_as, mirror_ok=bool(ok), mirror_reason=why, trained=trained)
    cert = info.pop("cert", None); info.pop("mk", None); info.pop("cur", None)
    if cert is None:
        meta.update(files=[], kind="mirror-only reject", info=info)
        json.dump(meta, open(os.path.join(out, "meta.json"), "w"), indent=1)
        print(tag, "mirror reject before any case (mirror-only):", why); return
    dq, mod = q(delta), "R9LN15.%s." % tag
    nh, ns, dd = len(cert["heads"]), len(cert["states"]), cert["d"]
    defs, _ = MC.task_parts(r7.task("A"))
    A = ["import Lane4.LNAll", "", "/- the proofs study, rung 9-LN15, per-network file. Generated by tools/make_r9ln15_net.py; no hand edits.",
         "network: %s (%s), task automaton %s, radius %s" % (meta["dir"], meta["net"], task_as, dq),
         "mirror (tools/r9ln15_cert.py): %s (%s) -/" % ("accept" if ok else "reject", why), "", "namespace Lane4.Case", "open Lane4.RSeq (Vec)",
         "open Lane4.RSoft Lane4.AGate Lane4.LN", "open Lane4.Seq (Mask cand tokAt)", ""] + defs + ["", STATEMENT % dict(RAD=dq), "end Lane4.Case", ""] + NSP
    A.append(lnet("lnet", W))
    if trained: A.append(lnet("trained", json.load(open(os.path.join(d, "T.json")))))
    A.append(M7.TASKDEF["A"] if task_as == "A" else M7.TASKDEF_PLAIN["B"])
    for k in range(nh): A.append(hcert("hc%d" % k, cert["heads"][k]))
    w = cert["W"]
    A.append("def iw : IW :=" + nl + "  { E := %s," % zm(w["E"]) + nl + "    g1 := %s, b1 := %s, g2 := %s, b2 := %s, gf := %s, bf := %s," % tuple(zl(w[k]) for k in ("g1", "b1", "g2", "b2", "gf", "bf"))
             + nl + "    W1 := %s," % zm(w["W1"]) + nl + "    c1 := %s," % zl(w["c1"]) + nl + "    W2 := %s," % zm(w["W2"]) + nl + "    c2 := %s, oW := %s, oB := %s }" % (zl(w["c2"]), zl(w["oW"]), zi(w["oB"])))
    for k, (s, wins) in enumerate(cert["states"]):
        A.append("def s%d : ℕ × List (List ℕ) := (%d, [%s])" % (k, s, ", ".join("[" + ", ".join(str(t) for t in wn) + "]" for wn in wins)))
    A.append("def cert : CertLN :=" + nl + "  { heads := [%s]," % ", ".join("hc%d" % k for k in range(nh)) + nl
             + "    boxes := %s," % ivm(cert["boxes"]) + nl + "    W := iw," + nl + "    states := [%s] }" % ", ".join("s%d" % k for k in range(ns)))
    A.append("abbrev dI : ℤ := floorQ (%s)" % dq)
    case = lambda k, t: "caseOKLN (%s) dI lnetNB0 task cert %d s%d %d" % (dq, dd, k, t)
    files = []
    if not ok:
        k, t = cert["fail"]
        A += ["", "/-- the case at which the mirror rejects -/", "theorem cfail : %s = false := by decide +kernel" % case(k, t),
              "theorem smem : s%d ∈ cert.states := by decide +kernel" % k, "",
              "/-- THE CHECKER REJECTS. -/", "theorem reject : checkLN (%s) lnet task cert = false :=" % dq,
              "  checkLN_false_of_case (%s) lnet task cert lnetNB0 %d s%d %d rfl (by decide +kernel) smem (by decide +kernel) cfail" % (dq, dd, k, t - 1)] + END + ["#print axioms Lane4.LNNetFile.reject", ""]
        files = [("Z", A)]
    else:
        once = ["theorem rd0 : decide ((0 : ℚ) ≤ %s) = true := by decide +kernel" % dq,
                "theorem rd1 : decide ((%s : ℚ) ≤ 1 / 2) = true := by decide +kernel" % dq,
                "theorem hdim : (lnet.net.embed.headD []).length = %d := by decide +kernel" % dd,
                "theorem shape : lnet.net.shapeOK task.ntok = true := by decide +kernel",
                "theorem wts : weightsOK lnet.net lnetNB0 = true := by decide +kernel",
                "theorem lnw : lnWeightsOK (%s) lnet lnetNB0 %d = true := by decide +kernel" % (dq, dd),
                "theorem nh2 : decide (lnetNB0.heads.length ≤ 2) = true := by decide +kernel",
                "theorem d1 : decide (1 ≤ %d) = true := by decide +kernel" % dd,
                "theorem iwq : decide (cert.W = intW lnet lnetNB0) = true := by decide +kernel",
                "theorem bxs : decide (allSomeL (cert.W.E.map (ln1Box dI (slots lnetNB0 %d) cert.W)) = some cert.boxes) = true := by decide +kernel" % dd,
                "theorem bxk : cert.boxes.all (boxOK %d) = true := by decide +kernel" % dd,
                "theorem len : (cert.heads.length == lnetNB0.heads.length) = true := by decide +kernel",
                "theorem stl : cert.states.all (fun st => st.2.length == lnetNB0.heads.length) = true := by decide +kernel",
                "theorem ini : cert.states.contains (task.init, cert.heads.map (fun hc => if hc.cands.getD 0 false = true then [0] else [])) = true := by decide +kernel"]
        for k in range(nh):
            once.append("theorem hd%d : headOKLN (%s) cert.boxes lnetNH%d hc%d = true := by decide +kernel" % (k, dq, k, k))
        cases = [["theorem c%d_%d : %s = true := by decide +kernel" % (k, t, case(k, t)) for t in range(1, 6)] for k in range(ns)]
        perst = max(1, per // 5)
        chunks = [cases[i:i + perst] for i in range(0, ns, perst)]
        names = "ABCDEFGHIJKLMNOPQRSTUVWXY"
        for ci, ch in enumerate(chunks):
            pre = (A + [""] + once) if ci == 0 else (["import " + mod + "A", ""] + NSP)
            files.append((names[ci], pre + [""] + [l for g in ch for l in g] + END + [""]))

        def nest(lemma, nil, xs):
            t = nil
            for x in reversed(xs):
                t = "%s _ _ _ _ _ %s (%s)" % (lemma, x, t) if lemma == "heads_cons" else "%s _ _ _ %s (%s)" % (lemma, x, t)
            return t
        Z = ["import " + mod + names[ci] for ci in range(len(chunks))] + [""] + NSP
        for k in range(ns):
            Z.append("theorem st%d : (List.range task.ntok).all (fun k => caseOKLN (%s) (floorQ (%s)) lnetNB0 task cert %d s%d (k + 1)) = true :=" % (k, dq, dq, dd, k))
            Z.append("  range5_all _ c%d_1 c%d_2 c%d_3 c%d_4 c%d_5" % (k, k, k, k, k))
        Z += ["", "/-- THE CHECKER ACCEPTS: every conjunct evaluated by the kernel, put together by `checkLN_of`. -/",
              "theorem accept : checkLN (%s) lnet task cert = true :=" % dq,
              "  checkLN_of (%s) lnet task cert lnetNB0 %d rfl hdim rd0 rd1 shape wts lnw nh2 d1 iwq bxs bxk len" % (dq, dd),
              "    (%s) stl ini" % nest("heads_cons", "heads_nil _", ["hd%d" % k for k in range(nh)]),
              "    (%s)" % nest("all_cons_of", "all_nil_of _", ["st%d" % k for k in range(ns)])]
        ax = ["#print axioms Lane4.LNNetFile.accept"]
        if task_as == "A":
            Z.append(TAIL % dict(RAD=dq, TEQ=M8.TEQ["A"]))
            ax += ["#print axioms Lane4.LNNetFile.skeleton_ok", "#print axioms Lane4.LNNetFile.binary32"]
            if trained:
                Z.append(TRAINED % dict(RAD=dq))
                ax += ["#print axioms Lane4.LNNetFile.trained_exact_all_lengths", "#print axioms Lane4.LNNetFile.trained_binary32"]
        files.append(("Z", Z + END + ax + [""]))
    for name, body in files:
        open(os.path.join(out, name + ".lean"), "w", encoding="utf-8", newline=nl).write(nl.join(body))
    meta.update(files=[n for n, _ in files], kind="accept" if ok else "reject at a case", states=ns, info=info)
    json.dump(meta, open(os.path.join(out, "meta.json"), "w"), indent=1)
    print(tag, "mirror:", "accept" if ok else "reject", "|", why[:90], "| states", ns, "| table rows", info.get("table_rows"), "| files", [n for n, _ in files])


if __name__ == "__main__":
    main()
