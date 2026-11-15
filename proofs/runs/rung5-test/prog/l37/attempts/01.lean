namespace Lane4.Case

def adv (s t : ℕ) : ℕ := if val t = 0 then s else val t

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ := (adv s.1 t, s.2 ++ [adv s.1 t])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem fold_snd (w : List ℕ) : ∀ (a : ℕ) (acc : List ℕ),
    (w.foldl step (a, acc)).2 =
      acc ++ (List.range w.length).map (fun j => (w.take (j+1)).foldl adv a) := by
  induction w with
  | nil => intro a acc; simp
  | cons b t ih =>
    intro a acc
    simp only [List.foldl_cons, step]
    rw [ih, List.length_cons, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def, List.take_succ_cons]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h : i - 1 < w.length := by omega
  unfold prog target lastv
  rw [fold_snd]
  have e : i - 1 + 1 = i := by omega
  simp [List.getD_eq_getElem?_getD, h, e, adv]

end Lane4.Case
