namespace Lane4.Case
open Lane4.Seq (tokAt)

def nxt (s t : ℕ) : ℕ := if s = 0 then code t else s

def step (st : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (nxt st.1 t, st.2 ++ [((if nxt st.1 t = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_eq (w : List ℕ) (s : ℕ) (acc : List ℕ) :
    (w.foldl step (s, acc)).2 = acc ++ (List.range w.length).map
      (fun j => ((if (w.take (j+1)).foldl nxt s = 2 then 1 else 0) + cbit (w.getD j 0)) % 2) := by
  induction w generalizing s acc with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons]
    have : step (s, acc) b = (nxt s b, acc ++ [((if nxt s b = 2 then 1 else 0) + cbit b) % 2]) := rfl
    rw [this, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Function.comp_def, List.foldl_cons]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  unfold prog target firstc
  rw [fold_eq]
  simp only [List.nil_append, List.getD_eq_getElem?_getD]
  have h : i - 1 < (List.range w.length).length := by simp; omega
  have h2 : i - 1 + 1 = i := by omega
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  simp [h2, nxt, List.getD_eq_getElem?_getD]

end Lane4.Case
