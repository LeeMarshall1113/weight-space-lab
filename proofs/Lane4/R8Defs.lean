/-
Lane 4, rung 8: definitions shared by the kit cases (meaning of affine forms, abstract states with
windows, what a window means in an input). Written by the lane. No theorems.
-/
import Lane4.R8Cert

namespace Lane4.Cert8

open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate Lane4.Cert

/-! ### affine forms -/

/-- value of a coefficient list under the symbol values `e`, the first coefficient belonging to
symbol number `k` -/
noncomputable def linVal : List ℚ → (ℕ → ℝ) → ℕ → ℝ
  | a :: l, e, k => ((a : ℚ) : ℝ) * e k + linVal l e (k + 1)
  | [], _, _ => 0

/-- The real `v` is represented by the affine form `a` under the symbol values `e`:
`v` is within the radius of centre + Σ coefficient · symbol. -/
def InAF (e : ℕ → ℝ) (v : ℝ) (a : AF) : Prop :=
  |v - (((a.c : ℚ) : ℝ) + linVal a.t e 0)| ≤ ((a.r : ℚ) : ℝ)

/-- Entry by entry, with equal lengths. -/
def InAFs (e : ℕ → ℝ) (v : List ℝ) (a : List AF) : Prop :=
  v.length = a.length ∧ ∀ k, k < v.length → InAF e (v.getD k 0) (a.getD k ⟨0, [], 0⟩)

/-- Every symbol is in `[-1, 1]`. -/
def Sym (e : ℕ → ℝ) : Prop := ∀ k, |e k| ≤ 1

/-! ### the abstract machine with windows -/

/-- The abstract state before any real token. The same expression as in `check8`. -/
def absInit8 (T : Task) (heads : List HCert) : ℕ × List (List ℕ) :=
  (T.init, heads.map (fun hc => if hc.cands.getD 0 false = true then [0] else []))

/-- Reading token `t`. The same expression as in `caseOK8`. -/
def absStep8 (T : Task) (heads : List HCert) (st : ℕ × List (List ℕ)) (t : ℕ) :
    ℕ × List (List ℕ) :=
  (T.step st.1 t, List.zipWith (fun hc win => winNext hc t win) heads st.2)

/-- The abstract state after reading the tokens `pre`. -/
def absState8 (T : Task) (heads : List HCert) (pre : List ℕ) : ℕ × List (List ℕ) :=
  pre.foldl (absStep8 T heads) (absInit8 T heads)

/-- `P` lists, newest first, the `P.length` latest candidate positions of the query at position
`i`: strictly decreasing, each allowed by the mask and holding a candidate token, and every other
allowed candidate position lies before all of them. `tok` gives the token at each position. -/
def WinPos (m : Mask) (cd : List Bool) (tok : ℕ → ℕ) (n i : ℕ) (P : List ℕ) : Prop :=
  P.Pairwise (fun a b => b < a) ∧
  (∀ j ∈ P, j ∈ cand m n i ∧ cd.getD (tok j) false = true) ∧
  (∀ k ∈ cand m n i, cd.getD (tok k) false = true → k ∉ P → ∀ j ∈ P, k < j)

/-- the number of keys of a full window at a query with token `t` -/
def fullLen (h : AHead) (hc : HCert) (t : ℕ) : ℕ :=
  hc.L + (if h.mask = Mask.causal ∧ hc.cands.getD t false = true then 1 else 0)

end Lane4.Cert8
