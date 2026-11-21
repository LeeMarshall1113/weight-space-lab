namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, successor value for token 1, for token 2, outputs). -/
def stp (s : ℕ × ℕ × ℕ × List ℕ) (t : ℕ) : ℕ × ℕ × ℕ × List ℕ :=
  (t, if s.1 = 1 then h t else s.2.1, if s.1 = 2 then h t else s.2.2.1,
    s.2.2.2 ++ [if t = 1 then (if s.1 = 1 then h t else s.2.1)
      else if t = 2 then (if s.1 = 2 then h t else s.2.2.1) else 0])

def prog (w : List ℕ) : List ℕ := (w.foldl stp (0, 0, 0, [])).2.2.2

-- PROOF

theorem find_cong (p q : ℕ → Bool) (l : List ℕ) (hl : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := hl a (by simp)
    have := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp only [List.find?_cons, ha, this]

theorem tokAt_app (w : List ℕ) (t j : ℕ) (hj : j ≤ w.length) :
    tokAt (w ++ [t]) j = tokAt w j := by
  unfold tokAt
  rw [show (0 :: (w ++ [t])) = (0 :: w) ++ [t] from rfl, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]

theorem tokAt_last (w : List ℕ) (t : ℕ) : tokAt (w ++ [t]) (w.length + 1) = t := by
  unfold tokAt
  rw [show (0 :: (w ++ [t])) = (0 :: w) ++ [t] from rfl, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

theorem G_step (G : List ℕ → ℕ → ℕ) (hG : ∀ w k, G w k = match (List.range w.length).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == k)) with
    | some j => h (tokAt w (j + 1))
    | none => 0) (w : List ℕ) (t k : ℕ) (hk : 1 ≤ k) :
    G (w ++ [t]) k = if tokAt w w.length = k then h t else G w k := by
  rw [hG (w ++ [t]) k, hG w k]
  rw [List.length_append, List.length_singleton, List.range_succ]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.find?_cons]
  rw [tokAt_app w t w.length le_rfl]
  have hc : ∀ j ∈ (List.range w.length).reverse,
      (decide (1 ≤ j) && (tokAt (w ++ [t]) j == k)) = (decide (1 ≤ j) && (tokAt w j == k)) := by
    intro j hj
    have : j < w.length := by simpa using hj
    rw [tokAt_app w t j (by omega)]
  rw [find_cong _ _ _ hc]
  by_cases hp : tokAt w w.length = k
  · have h1 : 1 ≤ w.length := by
      rcases Nat.eq_zero_or_pos w.length with h0 | h0
      · rw [h0] at hp
        have : tokAt w 0 = 0 := by simp [tokAt]
        omega
      · exact h0
    simp [hp, h1, tokAt_last]
  · simp only [hp]
    simp only [beq_iff_eq, hp, decide_false, Bool.and_false, if_false]
    rcases hf : (List.range w.length).reverse.find?
        (fun j => decide (1 ≤ j) && (tokAt w j == k)) with _ | j
    · simp
    · have hj : j ∈ (List.range w.length).reverse := List.mem_of_find?_eq_some hf
      have : j < w.length := by simpa using hj
      simp [tokAt_app w t (j + 1) (by omega)]

theorem target_app (w : List ℕ) (t i : ℕ) (hi : i ≤ w.length) :
    target (w ++ [t]) i = target w i := by
  unfold target prevOcc
  have hc : ∀ j ∈ (List.range i).reverse,
      (decide (1 ≤ j) && (tokAt (w ++ [t]) j == tokAt (w ++ [t]) i)) =
        (decide (1 ≤ j) && (tokAt w j == tokAt w i)) := by
    intro j hj
    have : j < i := by simpa using hj
    rw [tokAt_app w t j (by omega), tokAt_app w t i hi]
  rw [find_cong _ _ _ hc]
  rcases hf : (List.range i).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) with _ | j
  · simp
  · have hj : j ∈ (List.range i).reverse := List.mem_of_find?_eq_some hf
    have : j < i := by simpa using hj
    simp [tokAt_app w t (j + 1) (by omega)]

theorem target_last (G : List ℕ → ℕ → ℕ) (hG : ∀ w k, G w k = match (List.range w.length).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == k)) with
    | some j => h (tokAt w (j + 1))
    | none => 0) (w : List ℕ) (t : ℕ) :
    target (w ++ [t]) (w.length + 1) = G (w ++ [t]) t := by
  unfold target prevOcc
  rw [hG, tokAt_last, List.length_append, List.length_singleton]

theorem inv (G : List ℕ → ℕ → ℕ) (hG : ∀ w k, G w k = match (List.range w.length).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == k)) with
    | some j => h (tokAt w (j + 1))
    | none => 0) (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) :
    (w.foldl stp (0, 0, 0, [])).1 = tokAt w w.length ∧
    (w.foldl stp (0, 0, 0, [])).2.1 = G w 1 ∧
    (w.foldl stp (0, 0, 0, [])).2.2.1 = G w 2 ∧
    (w.foldl stp (0, 0, 0, [])).2.2.2.length = w.length ∧
    ∀ i, 1 ≤ i → i ≤ w.length →
      (w.foldl stp (0, 0, 0, [])).2.2.2.getD (i - 1) 0 = target w i := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [tokAt], by rw [hG]; simp, by rw [hG]; simp, by simp, ?_⟩
    intro i h1 h2
    simp at h2
    omega
  | append_singleton w t ih =>
    have ht := hw t (by simp)
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun x hx => hw x (by simp [hx]))
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize w.foldl stp (0, 0, 0, []) = s at *
    obtain ⟨p, a1, a2, out⟩ := s
    simp only at h1 h2 h3 h4 h5
    subst h1 h2 h3
    have e1 := G_step G hG w t 1 (by omega)
    have e2 := G_step G hG w t 2 (by omega)
    have hl : (w ++ [t]).length = w.length + 1 := by simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [stp, hl, tokAt_last]
    · simp only [stp, e1]
    · simp only [stp, e2]
    · simp [stp, h4]
    · intro i hi1 hi2
      rw [hl] at hi2
      by_cases hle : i ≤ w.length
      · simp only [stp]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD, h5 i hi1 hle, target_app w t i hle]
      · have hi : i = w.length + 1 := by omega
        subst hi
        rw [target_last G hG]
        simp only [stp, Nat.add_sub_cancel]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h4]
        simp only [Nat.sub_self]
        rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
        · simp [e1]
        · simp [e2]

theorem prog_correct : StatementProg prog := by
  intro w hw i hi1 hi2
  exact (inv (fun w k => match (List.range w.length).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == k)) with
    | some j => h (tokAt w (j + 1))
    | none => 0) (fun _ _ => rfl) w hw).2.2.2.2 i hi1 hi2

end Lane4.Case
