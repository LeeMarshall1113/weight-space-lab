namespace Lane4.Case
open Lane4.Seq (tokAt)

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (if s.1 = 0 then code t else s.1,
   s.2 ++ [((if (if s.1 = 0 then code t else s.1) = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_snd (w : List ℕ) (s : ℕ) (acc : List ℕ) :
    (w.foldl step (s, acc)).2 = acc ++ (List.range w.length).map (fun j =>
      ((if (w.take (j+1)).foldl (fun s t => if s = 0 then code t else s) s = 2 then 1 else 0)
        + cbit (w.getD j 0)) % 2) := by
  induction w generalizing s acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [step, Function.comp_def, List.take_succ_cons, List.foldl_cons]
    intro a _
    rfl

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  unfold prog target firstc
  rw [fold_snd]
  have h : i - 1 < w.length := by omega
  simp [List.getD_eq_getElem?_getD, h]
  have : i - 1 + 1 = i := by omega
  rw [this]

end Lane4.Case
