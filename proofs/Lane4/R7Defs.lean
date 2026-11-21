/-
Lane 4, rung 7: definitions shared by the kit cases k3 (head lemma), k4 (automaton lemma) and
k5 (composition). Written by the lane. No theorems.
-/
import Lane4.R7Cert

namespace Lane4.Cert

open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate

/-- Position `j` is the latest candidate key of the query at position `i`: the mask allows it,
its token is a candidate token (`cd`), and no later allowed position holds a candidate token.
`tok` gives the token at each position. -/
def Latest (m : Mask) (cd : List Bool) (tok : ℕ → ℕ) (n i j : ℕ) : Prop :=
  j ∈ cand m n i ∧ cd.getD (tok j) false = true ∧
  ∀ k ∈ cand m n i, cd.getD (tok k) false = true → k ≤ j

/-- The abstract state before any real token: the task's initial state, and per head the
BOS token (row 0) if it is a candidate. The same expression as in `check`. -/
def absInit (T : Task) (cands : List (List Bool)) : ℕ × List (Option ℕ) :=
  (T.init, cands.map (fun cd => if cd.getD 0 false = true then some 0 else none))

/-- Reading token `t`. The same expression as in `caseOK`. -/
def absStep (T : Task) (cands : List (List Bool)) (st : ℕ × List (Option ℕ)) (t : ℕ) :
    ℕ × List (Option ℕ) :=
  (T.step st.1 t, List.zipWith (fun cd p => pickNext cd t p) cands st.2)

/-- The abstract state after reading the tokens `pre`. -/
def absState (T : Task) (cands : List (List Bool)) (pre : List ℕ) : ℕ × List (Option ℕ) :=
  pre.foldl (absStep T cands) (absInit T cands)

end Lane4.Cert
