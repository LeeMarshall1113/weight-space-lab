namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, successor table, outputs so far). -/
def step (s : ℕ × (ℕ → ℕ) × List ℕ) (x : ℕ) : ℕ × (ℕ → ℕ) × List ℕ :=
  (x, fun t => if t = s.1 then x else s.2.1 t,
   s.2.2 ++ [h (if x = s.1 then x else s.2.1 x)])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, fun _ => 0, [])).2.2

-- PROOF

theorem find_succ (w : List ℕ) (t i : ℕ) :
    (List.range (i + 1)).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == t)) =
      if 1 ≤ i ∧ tokAt w i = t then some i
      else (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == t)) := by
  by_cases hc : 1 ≤ i ∧ tokAt w i = t
  · rw [if_pos hc]
    simp [List.range_succ, hc.1, hc.2]
  · rw [if_neg hc]
    have hp : (decide (1 ≤ i) && (tokAt w i == t)) = false := by
      by_cases h1 : 1 ≤ i
      · have : tokAt w i ≠ t := fun e => hc ⟨h1, e⟩
        simp [h1, this]
      · simp [h1]
    simp [List.range_succ, hp]

theorem target_eq (w : List ℕ) (i : ℕ) :
    target w i = h (((List.range i).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i))).elim 0
        (fun j => tokAt w (j + 1))) := by
  unfold target prevOcc
  cases (List.range i).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) <;> simp [h]

theorem inv (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) :
    ∀ k, k ≤ w.length → ∀ s, s = (w.take k).foldl step (0, fun _ => 0, []) →
    s.1 = tokAt w k ∧
    (∀ t, 1 ≤ t → s.2.1 t = ((List.range k).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == t))).elim 0 (fun j => tokAt w (j + 1))) ∧
    s.2.2.length = k ∧
    (∀ i, 1 ≤ i → i ≤ k → s.2.2.getD (i - 1) 0 = target w i) := by
  intro k
  induction k with
  | zero =>
    intro _ s hs
    subst hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Lane4.Seq.tokAt_zero]
    · intro t _
      simp
    · simp
    · intro i h1 h2
      omega
  | succ k ih =>
    intro hk s hs
    have hk' : k < w.length := by omega
    obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (w.take k).foldl step (0, fun _ => 0, []) := ⟨_, rfl⟩
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih (by omega) s0 hs0
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := by
      simp [List.take_succ, hk']
    rw [htake, List.foldl_append, ← hs0] at hs
    simp only [List.foldl_cons, List.foldl_nil] at hs
    subst hs
    have hx : tokAt w (k + 1) = w[k] := Lane4.Seq.tokAt_succ w k hk'
    have hkey : ∀ t, 1 ≤ t → (if t = s0.1 then w[k] else s0.2.1 t) =
        ((List.range (k + 1)).reverse.find?
          (fun j => decide (1 ≤ j) && (tokAt w j == t))).elim 0
            (fun j => tokAt w (j + 1)) := by
      intro t ht
      rw [find_succ]
      by_cases hc : tokAt w k = t
      · have hk1 : 1 ≤ k := by
          by_contra hcon
          have hk0 : k = 0 := by omega
          subst hk0
          rw [Lane4.Seq.tokAt_zero] at hc
          omega
        have h1 : t = s0.1 := by rw [ih1]; exact hc.symm
        rw [if_pos h1, if_pos ⟨hk1, hc⟩]
        simp [hx]
      · have h1 : ¬ t = s0.1 := by
          rw [ih1]; exact fun e => hc e.symm
        rw [if_neg h1, if_neg (fun e => hc e.2), ih2 t ht]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show w[k] = _
      exact hx.symm
    · intro t ht
      exact hkey t ht
    · simp [step, ih3]
    · intro i h1 h2
      by_cases hi : i ≤ k
      · have hlt : i - 1 < s0.2.2.length := by omega
        show (s0.2.2 ++ [_]).getD (i - 1) 0 = _
        rw [List.getD_append _ _ _ _ hlt]
        exact ih4 i h1 hi
      · have hik : i = k + 1 := by omega
        subst hik
        have e : ∀ v, (s0.2.2 ++ [v]).getD (k + 1 - 1) 0 = v := fun v => by
          rw [show k + 1 - 1 = s0.2.2.length by omega]
          simp [List.getD_eq_getElem?_getD]
        show (s0.2.2 ++ [_]).getD (k + 1 - 1) 0 = _
        rw [e, target_eq, hx]
        congr 1
        exact hkey w[k] (hw _ (List.getElem_mem hk')).1

theorem prog_correct : StatementProg prog := by
  intro w hw i h1 h2
  have := (inv w hw w.length le_rfl _ rfl).2.2.2 i h1 h2
  rw [List.take_length] at this
  exact this

end Lane4.Case
