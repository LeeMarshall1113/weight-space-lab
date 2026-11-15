namespace Lane4.Case

def gstep (s t : ℕ) : ℕ := if val t = 0 then s else val t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (gstep s.1 t, s.2 ++ [gstep s.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

def scan : ℕ → List ℕ → List ℕ
  | _, [] => []
  | a, b :: t => gstep a b :: scan (gstep a b) t

theorem fold_eq (w : List ℕ) : ∀ (a : ℕ) (acc : List ℕ),
    (w.foldl step (a, acc)).2 = acc ++ scan a w := by
  induction w with
  | nil => intro a acc; simp [scan]
  | cons b t ih =>
    intro a acc
    simp only [List.foldl_cons, step, scan]
    rw [ih]
    simp

theorem scan_get (w : List ℕ) : ∀ (a i : ℕ), i < w.length →
    (scan a w).getD i 0 = (w.take (i + 1)).foldl gstep a := by
  induction w with
  | nil => intro a i h; simp at h
  | cons b t ih =>
    intro a i h
    cases i with
    | zero => simp [scan]
    | succ i =>
      have h' : i < t.length := by simpa using h
      simp only [scan, List.getD_cons_succ, List.take_succ_cons, List.foldl_cons]
      exact ih (gstep a b) i h'

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  unfold prog target lastv
  rw [fold_eq, List.nil_append]
  have h := scan_get w 0 (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  exact h

end Lane4.Case
