namespace Lane4.Case

def step (acc : ℕ × ℕ) (t : ℕ) : ℕ × ℕ :=
  if t < 2 then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1)

def rep : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, t => t :: rep n t

def prog (w : List ℕ) : List ℕ :=
  rep (w.foldl step (0, 0)).1 1 ++ rep (w.foldl step (0, 0)).2 2

-- PROOF

theorem foldl_step (w : List ℕ) (x y : ℕ) :
    w.foldl step (x, y) =
      (x + w.countP (fun s => decide (s < 2)), y + w.countP (fun s => !decide (s < 2))) := by
  induction w generalizing x y with
  | nil => simp
  | cons t r ih =>
    rw [List.foldl_cons]
    by_cases h : t < 2
    · have : step (x, y) t = (x + 1, y) := by simp [step, h]
      rw [this, ih]
      simp [List.countP_cons, h]
      omega
    · have : step (x, y) t = (x, y + 1) := by simp [step, h]
      rw [this, ih]
      simp [List.countP_cons, h]
      omega

theorem getD_rep (b k : ℕ) (h : k < b) : (rep b 2).getD k 0 = 2 := by
  induction b generalizing k with
  | zero => omega
  | succ b ih =>
    cases k with
    | zero => simp [rep]
    | succ k => simp [rep]; exact ih k (by omega)

theorem getD_out (a b k : ℕ) (hk : k < a + b) :
    (rep a 1 ++ rep b 2).getD k 0 = if k < a then 1 else 2 := by
  induction a generalizing k with
  | zero => simp [rep]; exact getD_rep b k (by omega)
  | succ a ih =>
    cases k with
    | zero => simp [rep]
    | succ k =>
      have := ih k (by omega)
      simp [rep, this]

theorem prog_correct : StatementProg prog := by
  intro w hv i hi hil
  obtain ⟨_, hr⟩ := hv
  rw [show prog w = _ from rfl]
  have hf := foldl_step w 0 0
  rw [hf]
  simp only [Nat.zero_add]
  set a := w.countP (fun s => decide (s < 2)) with ha
  set b := w.countP (fun s => !decide (s < 2)) with hb
  have hlen : w.length = a + b := by
    have := List.length_eq_countP_add_countP (fun s => decide (s < 2)) w
    simpa [ha, hb] using this
  have h0 : w.countP (fun s => decide (s < 1)) = 0 := by
    rw [List.countP_eq_zero]
    intro s hs
    have := (hr s hs).1
    simp; omega
  have h1 : w.countP (fun s => decide (s ≤ 1)) = a := by
    rw [ha]
    apply List.countP_congr
    intro s _
    simp; omega
  have h2 : w.countP (fun s => decide (s < 2)) = a := rfl
  have h3 : w.countP (fun s => decide (s ≤ 2)) = a + b := by
    rw [← hlen]
    rw [List.countP_eq_length]
    intro s hs
    simp; exact (hr s hs).2
  rw [getD_out a b (i - 1) (by omega)]
  unfold IsRank
  by_cases hk : i - 1 < a
  · rw [if_pos hk]
    rw [h0, h1]
    omega
  · rw [if_neg hk]
    rw [h2, h3]
    omega

end Lane4.Case
