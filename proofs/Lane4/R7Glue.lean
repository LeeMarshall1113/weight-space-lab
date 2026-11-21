/-
Lane 4, rung 7: reassembly of the checker from its pieces. Written by the lane.
`check` is a conjunction; per network each conjunct is evaluated by the kernel on its own
(`decide +kernel`), and `check_of` puts them together without evaluating anything.
-/
import Lane4.R7All

namespace Lane4.Cert

open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate

theorem check_of (δ : ℚ) (N : ANet) (T : Task) (c : Cert) (B : ABlock)
    (hB : N.blocks = [B])
    (h1 : N.shapeOK T.ntok = true) (h2 : weightsOK N B = true)
    (h3 : (c.cands.length == B.heads.length) = true)
    (h4 : (List.zipWith (fun h cd => headOK δ (N.embed.map (embIV δ)) h cd) B.heads c.cands).all id
            = true)
    (h5 : c.states.all (fun st => st.2.length == B.heads.length) = true)
    (h6 : c.states.contains
            (T.init, c.cands.map (fun cd => if cd.getD 0 false = true then some 0 else none)) = true)
    (h7 : c.states.all (fun st => (List.range T.ntok).all
            (fun k => caseOK δ N B T c (N.embed.map (embIV δ)) st (k + 1))) = true) :
    check δ N T c = true := by
  unfold check
  rw [hB]
  simp only [h1, h2, h3, h4, h5, h6, h7, Bool.and_self]

/-- one more head -/
theorem heads_cons {α β : Type} (f : α → β → Bool) (a : α) (b : β) (as : List α) (bs : List β)
    (h : f a b = true) (hs : (List.zipWith f as bs).all id = true) :
    (List.zipWith f (a :: as) (b :: bs)).all id = true := by
  simp only [List.zipWith_cons_cons, List.all_cons, id, h, hs, Bool.and_self]

theorem heads_nil {α β : Type} (f : α → β → Bool) : (List.zipWith f ([] : List α) ([] : List β)).all id = true := by
  simp

/-- one more state -/
theorem all_cons_of {α : Type} (g : α → Bool) (a : α) (as : List α)
    (h : g a = true) (hs : as.all g = true) : (a :: as).all g = true := by
  simp only [List.all_cons, h, hs, Bool.and_self]

theorem all_nil_of {α : Type} (g : α → Bool) : ([] : List α).all g = true := by simp

end Lane4.Cert
