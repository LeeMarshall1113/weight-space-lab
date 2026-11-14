namespace Lane4.Case

def wgt (t : ℕ) : ℤ := if t = 1 then 0 else if t = 2 then 1 else if t = 3 then (-1) else if t = 4 then 1 else 0

def stp (s : ℤ) (t : ℕ) : ℤ := if s < 0 then s else s + wgt t

def prog (w : List ℕ) : Bool := decide (w.foldl stp 0 = 0)

-- PROOF

theorem fold_neg (r : List ℕ) (s : ℤ) (h : s < 0) : r.foldl stp s = s := by
  induction r with
  | nil => rfl
  | cons t r ih => simp [List.foldl_cons, stp, h, ih]

theorem fold_main (w : List ℕ) : ∀ s : ℤ, 0 ≤ s →
    ((0 ≤ w.foldl stp s ↔ ∀ k, k ≤ w.length → 0 ≤ s + ((w.take k).map wgt).sum) ∧
     (0 ≤ w.foldl stp s → w.foldl stp s = s + (w.map wgt).sum)) := by
  induction w with
  | nil => intro s hs; simp [hs]
  | cons t r ih =>
    intro s hs
    have e : stp s t = s + wgt t := by simp [stp, not_lt.mpr hs]
    by_cases hn : s + wgt t < 0
    · have hf : (t :: r).foldl stp s = s + wgt t := by
        rw [List.foldl_cons, e]; exact fold_neg r _ hn
      rw [hf]
      refine ⟨?_, ?_⟩
      · constructor
        · intro h; omega
        · intro h
          have := h 1 (by simp)
          simp at this; omega
      · intro h; omega
    · have hp := ih (s + wgt t) (by omega)
      rw [List.foldl_cons, e]
      refine ⟨?_, ?_⟩
      · rw [hp.1]
        constructor
        · intro h k hk
          cases k with
          | zero => simpa using hs
          | succ k =>
            have := h k (by simpa using hk)
            simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
            linarith
        · intro h k hk
          have := h (k+1) (by simpa using hk)
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this
          linarith
      · intro h
        have := hp.2 h
        simp only [List.map_cons, List.sum_cons]
        linarith

theorem prog_correct : StatementProg prog := by
  intro w _
  have h := fold_main w 0 le_rfl
  unfold prog Good
  simp only [decide_eq_true_eq, zero_add] at *
  constructor
  · intro h0
    have h1 := h.2 (by omega)
    have h2 : 0 ≤ w.foldl stp 0 := by omega
    refine ⟨?_, by omega⟩
    intro k hk
    exact h.1.mp h2 k hk
  · rintro ⟨hq, hs⟩
    have h2 := h.1.mpr hq
    have := h.2 h2
    omega

end Lane4.Case
