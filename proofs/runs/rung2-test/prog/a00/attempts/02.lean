namespace Lane4.Case

def stp (s : ℕ × List ℕ) (t : ℕ) : ℕ × List ℕ :=
  (((t - 1) / 2 + (t - 1) % 2 + s.1) / 2, (((t - 1) / 2 + (t - 1) % 2 + s.1) % 2) :: s.2)

def prog (w : List ℕ) : List ℕ := (w.foldl stp (0, [])).2.reverse

def ds : ℕ → List ℕ → List ℕ
  | _, [] => []
  | c, t :: r => (((t - 1) / 2 + (t - 1) % 2 + c) % 2) :: ds (((t - 1) / 2 + (t - 1) % 2 + c) / 2) r

-- PROOF

theorem fold2 (w : List ℕ) : ∀ (c : ℕ) (out : List ℕ),
    (w.foldl stp (c, out)).2.reverse = out.reverse ++ ds c w := by
  induction w with
  | nil => intro c out; simp [ds]
  | cons t r ih =>
    intro c out
    rw [List.foldl_cons]
    have : stp (c, out) t = (((t - 1) / 2 + (t - 1) % 2 + c) / 2,
        (((t - 1) / 2 + (t - 1) % 2 + c) % 2) :: out) := by
      simp [stp]
    rw [this, ih]
    simp [ds]

theorem ds_get (w : List ℕ) : ∀ (c k : ℕ), k < w.length →
    (ds c w).getD k 0 = ((w.getD k 0 - 1) / 2 + (w.getD k 0 - 1) % 2 +
      (w.take k).foldl (fun c t => ((t - 1) / 2 + (t - 1) % 2 + c) / 2) c) % 2 := by
  induction w with
  | nil => intro c k h; simp at h
  | cons t r ih =>
    intro c k h
    cases k with
    | zero => simp [ds]
    | succ k =>
      have hk : k < r.length := by simpa using h
      simp only [ds, List.getD_cons_succ, List.take_succ_cons, List.foldl_cons]
      exact ih _ k hk

theorem prog_correct : StatementProg prog := by
  intro w _ i hi1 hi2
  unfold prog digit carryOut
  have h := fold2 w 0 []
  simp only [List.reverse_nil, List.nil_append] at h
  rw [h]
  have := ds_get w 0 (i - 1) (by omega)
  simpa [dA, dC] using this

end Lane4.Case
