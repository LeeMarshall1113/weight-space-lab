namespace Lane4.Case

def gstep (s t : ℕ) : ℕ := if s = 0 then code t else s

def step (st : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (gstep st.1 t, st.2 ++ [((if gstep st.1 t = 2 then 1 else 0) + cbit t) % 2])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, [])).2

-- PROOF

theorem pre_eq (w : List ℕ) : ∀ (s : ℕ) (acc : List ℕ),
    (w.foldl step (s, acc)).2 = acc ++ (w.foldl step (s, [])).2 := by
  induction w with
  | nil => intro s acc; simp
  | cons t r ih =>
    intro s acc
    simp only [List.foldl_cons, step]
    rw [ih, ih (gstep s t) ([] ++ _)]
    simp

theorem get_eq (w : List ℕ) : ∀ (s k : ℕ), k < w.length →
    (w.foldl step (s, [])).2.getD k 0
      = ((if (w.take (k + 1)).foldl gstep s = 2 then 1 else 0) + cbit (w.getD k 0)) % 2 := by
  induction w with
  | nil => intro s k h; simp at h
  | cons t r ih =>
    intro s k hk
    simp only [List.foldl_cons]
    rw [pre_eq r (gstep s t) ([] ++ _)]
    cases k with
    | zero => simp [step]
    | succ k' =>
      have hk' : k' < r.length := by simp at hk; omega
      have := ih (gstep s t) k' hk'
      simp only [step, List.nil_append, List.take_succ_cons, List.foldl_cons,
        List.getD_cons_succ, List.cons_append, this]
      simp [List.getD_cons_succ]
      simpa using this

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h := get_eq w 0 k (by omega)
  simp only [Nat.add_sub_cancel]
  unfold prog target firstc
  rw [h]
  rfl

end Lane4.Case
