namespace Lane4.Case

def step (p : ℕ × ℕ × ℕ) (t : ℕ) : ℕ × ℕ × ℕ :=
  if t = 1 then (p.1 + 1, p.2.1, p.2.2)
  else if t = 2 then (p.1, p.2.1 + 1, p.2.2)
  else (p.1, p.2.1, p.2.2 + 1)

def build (p : ℕ × ℕ × ℕ) : List ℕ :=
  List.replicate p.1 1 ++ List.replicate p.2.1 2 ++ List.replicate p.2.2 3

def prog (w : List ℕ) : List ℕ := build (w.foldl step (0, 0, 0))

-- PROOF

theorem foldl_counts (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (x y z : ℕ) :
    w.foldl step (x, y, z) =
      (x + w.countP (fun s => decide (s = 1)), y + w.countP (fun s => decide (s = 2)),
        z + w.countP (fun s => decide (s = 3))) := by
  induction w generalizing x y z with
  | nil => simp
  | cons t r ih =>
    have ht := hw t (by simp)
    have hr : ∀ s ∈ r, 1 ≤ s ∧ s ≤ 3 := fun s hs => hw s (List.mem_cons_of_mem _ hs)
    rw [List.foldl_cons]
    obtain ⟨h1, h3⟩ := ht
    have : t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases this with rfl | rfl | rfl
    · simp only [step, if_true]
      rw [ih hr]
      simp [List.countP_cons]
      omega
    · simp only [step]
      simp only [show (2 : ℕ) ≠ 1 by omega, if_false, if_true]
      rw [ih hr]
      simp [List.countP_cons]
      omega
    · simp only [step]
      simp only [show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, if_false]
      rw [ih hr]
      simp [List.countP_cons]
      omega

theorem count_facts (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) :
    w.countP (fun s => decide (s < 1)) = 0 ∧
    w.countP (fun s => decide (s < 2)) = w.countP (fun s => decide (s = 1)) ∧
    w.countP (fun s => decide (s ≤ 1)) = w.countP (fun s => decide (s = 1)) ∧
    w.countP (fun s => decide (s ≤ 2)) =
      w.countP (fun s => decide (s = 1)) + w.countP (fun s => decide (s = 2)) ∧
    w.countP (fun s => decide (s < 3)) =
      w.countP (fun s => decide (s = 1)) + w.countP (fun s => decide (s = 2)) ∧
    w.countP (fun s => decide (s ≤ 3)) =
      w.countP (fun s => decide (s = 1)) + w.countP (fun s => decide (s = 2)) +
        w.countP (fun s => decide (s = 3)) := by
  induction w with
  | nil => simp
  | cons t r ih =>
    have ht := hw t (by simp)
    have hr : ∀ s ∈ r, 1 ≤ s ∧ s ≤ 3 := fun s hs => hw s (List.mem_cons_of_mem _ hs)
    obtain ⟨h1, h3⟩ := ht
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih hr
    have : t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases this with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.countP_cons, decide_eq_true_eq] <;> split_ifs <;> omega

theorem prog_correct : StatementProg prog := by
  intro w hv i hi1 hi2
  obtain ⟨_, hw⟩ := hv
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := count_facts w hw
  have hlen : w.length = w.countP (fun s => decide (s = 1)) + w.countP (fun s => decide (s = 2)) +
        w.countP (fun s => decide (s = 3)) := by
    rw [← c6, List.countP_eq_length.mpr]
    intro s hs
    have := hw s hs
    simp; omega
  unfold prog build
  rw [foldl_counts w hw 0 0 0]
  simp only [Nat.zero_add]
  generalize w.countP (fun s => decide (s = 1)) = A at *
  generalize w.countP (fun s => decide (s = 2)) = B at *
  generalize w.countP (fun s => decide (s = 3)) = C at *
  unfold IsRank
  by_cases hA : i - 1 < A
  · have : ((List.replicate A 1 ++ List.replicate B 2 ++ List.replicate C 3).getD (i - 1) 0) = 1 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, List.length_replicate, hA]
    rw [this, c1, c3]
    omega
  · by_cases hB : i - 1 < A + B
    · have : ((List.replicate A 1 ++ List.replicate B 2 ++ List.replicate C 3).getD (i - 1) 0) = 2 := by
        rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        rw [List.getElem?_append_left (by simp; omega)]
        simp [List.getElem?_replicate, show i - 1 - A < B by omega]
      rw [this, c2, c4]
      omega
    · have : ((List.replicate A 1 ++ List.replicate B 2 ++ List.replicate C 3).getD (i - 1) 0) = 3 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simp [List.getElem?_replicate, show i - 1 - (A + B) < C by omega]
      rw [this, c5, c6]
      omega

end Lane4.Case
