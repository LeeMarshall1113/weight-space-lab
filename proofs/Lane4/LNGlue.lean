/-
Lane 4, rung 9-LN15: reassembly of the checker from its pieces, and two facts for the per-network
theorems. Written by the lane. `checkLN` is a conjunction; per network each conjunct is evaluated
by the kernel on its own (`decide +kernel`), and `checkLN_of` puts them together without evaluating
anything. `heads_cons`, `heads_nil`, `all_cons_of`, `all_nil_of` (Lane4/R7Glue.lean) and
`range5_all` (Lane4/R8Glue.lean) are reused.
-/
import Lane4.LNCert

namespace Lane4.LNC

open Lane4.Seq (Mask cand tokAt)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN

theorem checkLN_of (δ : ℚ) (N : LNNet) (T : Task) (c : CertLN) (B : ABlock) (d : ℕ)
    (hB : N.net.blocks = [B]) (hd : (N.net.embed.headD []).length = d)
    (hd0 : decide (0 ≤ δ) = true) (hd1 : decide (δ ≤ 1 / 2) = true)
    (h1 : N.net.shapeOK T.ntok = true) (h2 : weightsOK N.net B = true)
    (h3 : lnWeightsOK δ N B d = true)
    (h4 : decide (B.heads.length ≤ 2) = true) (h5 : decide (1 ≤ d) = true)
    (h6 : decide (c.W = intW N B) = true)
    (h7 : decide (allSomeL (c.W.E.map (ln1Box (floorQ δ) (slots B d) c.W)) = some c.boxes) = true)
    (h8 : c.boxes.all (boxOK d) = true)
    (h9 : (c.heads.length == B.heads.length) = true)
    (h10 : (List.zipWith (fun h hc => headOKLN δ c.boxes h hc) B.heads c.heads).all id = true)
    (h11 : c.states.all (fun st => st.2.length == B.heads.length) = true)
    (h12 : c.states.contains
            (T.init, c.heads.map (fun hc => if hc.cands.getD 0 false = true then [0] else [])) = true)
    (h13 : c.states.all (fun st => (List.range T.ntok).all
            (fun k => caseOKLN δ (floorQ δ) B T c d st (k + 1))) = true) :
    checkLN δ N T c = true := by
  unfold checkLN
  rw [hB]
  simp only [hd, hd0, hd1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, Bool.and_self]

/-- one failing case makes the checker reject -/
theorem checkLN_false_of_case (δ : ℚ) (N : LNNet) (T : Task) (c : CertLN) (B : ABlock) (d : ℕ)
    (st : ℕ × List (List ℕ)) (k : ℕ)
    (hB : N.net.blocks = [B]) (hd : (N.net.embed.headD []).length = d)
    (hst : st ∈ c.states) (hk : k < T.ntok)
    (hcase : caseOKLN δ (floorQ δ) B T c d st (k + 1) = false) :
    checkLN δ N T c = false := by
  have h13 : c.states.all (fun st => (List.range T.ntok).all
      (fun k => caseOKLN δ (floorQ δ) B T c d st (k + 1))) = false := by
    rw [List.all_eq_false]
    refine ⟨st, hst, ?_⟩
    rw [Bool.not_eq_true, List.all_eq_false]
    exact ⟨k, List.mem_range.mpr hk, by rw [hcase]; simp⟩
  unfold checkLN
  rw [hB]
  simp only [hd, h13, Bool.and_false]

/-- exact arithmetic: the real square root satisfies the square-root assumption -/
theorem sqrtM_real : SqrtM 0 0 Real.sqrt := ⟨fun x _ => by simp⟩

end Lane4.LNC
