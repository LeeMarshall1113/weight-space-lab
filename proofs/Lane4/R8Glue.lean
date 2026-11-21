/-
Lane 4, rung 8: reassembly of the checker from its pieces. Written by the lane.
`check8` is a conjunction; per network each conjunct is evaluated by the kernel on its own
(`decide +kernel`), and `check8_of` puts them together without evaluating anything.
The list lemmas `heads_cons`, `heads_nil`, `all_cons_of`, `all_nil_of` of Lane4/R7Glue.lean are reused.
-/
import Lane4.R8Cert
import Lane4.R7Glue

namespace Lane4.Cert8

open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate Lane4.Cert

theorem check8_of (δ : ℚ) (N : ANet) (T : Task) (c : Cert8) (B : ABlock)
    (hB : N.blocks = [B])
    (hd0 : decide (0 ≤ δ) = true) (hd1 : decide (δ ≤ 1 / 2) = true)
    (h1 : N.shapeOK T.ntok = true) (h2 : weightsOK N B = true)
    (h3 : (c.heads.length == B.heads.length) = true)
    (h4 : (List.zipWith (fun h hc => headOK8 δ (N.embed.map (embIV δ)) h hc) B.heads c.heads).all id
            = true)
    (h5 : c.states.all (fun st => st.2.length == B.heads.length) = true)
    (h6 : c.states.contains
            (T.init, c.heads.map (fun hc => if hc.cands.getD 0 false = true then [0] else [])) = true)
    (h7 : c.states.all (fun st => (List.range T.ntok).all
            (fun k => caseOK8 δ N B T c st (k + 1))) = true) :
    check8 δ N T c = true := by
  unfold check8
  rw [hB]
  simp only [hd0, hd1, h1, h2, h3, h4, h5, h6, h7, Bool.and_self]

/-- five cases, one lemma each -/
theorem range5_all (f : ℕ → Bool) (h1 : f 0 = true) (h2 : f 1 = true) (h3 : f 2 = true)
    (h4 : f 3 = true) (h5 : f 4 = true) : (List.range 5).all f = true := by
  rw [show List.range 5 = [0, 1, 2, 3, 4] from rfl]
  simp only [List.all_cons, List.all_nil, h1, h2, h3, h4, h5, Bool.and_self]

end Lane4.Cert8
