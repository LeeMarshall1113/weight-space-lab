namespace Lane4.Case

def step (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  let c := if val t = 0 then s.1 else val t
  (c, s.2 ++ [c])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem prefix_ex (w : List ℕ) : ∀ (c : ℕ) (acc : List ℕ),
    ∃ r, (w.foldl step (c, acc)).2 = acc ++ r := by
  induction w with
  | nil => intro c acc; exact ⟨[], by simp⟩
  | cons b t ih =>
    intro c acc
    obtain ⟨r, hr⟩ := ih (if val b = 0 then c else val b) (acc ++ [if val b = 0 then c else val b])
    refine ⟨[if val b = 0 then c else val b] ++ r, ?_⟩
    simp only [List.foldl_cons, step]
    rw [hr]
    simp

theorem fold_get (w : List ℕ) : ∀ (c : ℕ) (acc : List ℕ) (k : ℕ), k < w.length →
    (w.foldl step (c, acc)).2.getD (acc.length + k) 0
      = (w.take (k + 1)).foldl (fun s t => if val t = 0 then s else val t) c := by
  induction w with
  | nil => intro c acc k hk; simp at hk
  | cons b t ih =>
    intro c acc k hk
    cases k with
    | zero =>
      obtain ⟨r, hr⟩ := prefix_ex t (if val b = 0 then c else val b) (acc ++ [if val b = 0 then c else val b])
      simp only [List.foldl_cons, step]
      rw [hr]
      simp [List.getD_eq_getElem?_getD]
    | succ k =>
      have hk' : k < t.length := by simp at hk; omega
      have := ih (if val b = 0 then c else val b) (acc ++ [if val b = 0 then c else val b]) k hk'
      simp only [List.foldl_cons, step]
      have e : acc.length + (k + 1) = (acc ++ [if val b = 0 then c else val b]).length + k := by
        simp; omega
      rw [e, this]
      simp [List.take_succ_cons]

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  have h := fold_get w 0 [] (i - 1) (by omega)
  have e : i - 1 + 1 = i := by omega
  rw [e] at h
  simp at h
  unfold prog target lastv
  simpa using h

end Lane4.Case
