namespace Lane4.Case

def gstep (s t : ℕ) : ℕ := if val t = 0 then s else val t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (gstep s.1 t, s.2 ++ [gstep s.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_eq (w : List ℕ) (a : ℕ) (acc : List ℕ) :
    (w.foldl step (a, acc)).2 =
      acc ++ (List.range w.length).map (fun j => (w.take (j+1)).foldl gstep a) := by
  induction w generalizing a acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, step]
    rw [ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Function.comp_def, List.take_succ_cons, List.foldl_cons]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target lastv
  rw [fold_eq]
  have h2 : i - 1 + 1 = i := by omega
  simp [List.getD_eq_getElem?_getD, h, h2]
  rfl

end Lane4.Case
