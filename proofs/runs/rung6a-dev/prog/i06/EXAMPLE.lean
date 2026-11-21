/-
WORKED EXAMPLE on a task outside the four task families: output the previous token
(the token before position 1 is 0). It was checked by the same checker and passed.
It shows the parts the checker joins: the study team's Spec.lean, a Solution.lean, and (not
shown) Final.lean. Only the part between the SOLUTION markers is what you write.
Pattern: a fold with an explicit step function, a lemma describing the fold from any
starting state (induction on the list, state generalised), then the statement.
-/

-- ===== Spec.lean (given) =====
namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def target (w : List ℕ) (i : ℕ) : ℕ := tokAt w (i - 1)

def StatementProg (f : List ℕ → List ℕ) : Prop :=
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → (f w).getD (i - 1) 0 = target w i

end Lane4.Case

-- ===== Solution.lean (SOLUTION START) =====
namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, outputs so far). -/
def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ := (t, s.2 ++ [s.1])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_eq (w : List ℕ) (a : ℕ) (acc : List ℕ) :
    (w.foldl step (a, acc)).2 = acc ++ (a :: w).take w.length := by
  induction w generalizing a acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [ih]
    simp

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target tokAt
  rw [fold_eq]
  have h' : i - 1 < (0 :: w).length := by simp; omega
  simp [List.getD_eq_getElem?_getD, h, List.getElem?_eq_getElem h']

end Lane4.Case
-- ===== SOLUTION END =====
