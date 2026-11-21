namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, table of successor values per token, outputs so far). -/
def step (s : ℕ × (ℕ → ℕ) × List ℕ) (x : ℕ) : ℕ × (ℕ → ℕ) × List ℕ :=
  (x, fun t => if s.1 ≠ 0 ∧ t = s.1 then h x else s.2.1 t,
   s.2.2 ++ [(fun t => if s.1 ≠ 0 ∧ t = s.1 then h x else s.2.1 t) x])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, fun _ => 0, [])).2.2

-- PROOF

theorem key (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) :
    ∀ m, m ≤ w.length →
    ∃ a : ℕ → ℕ, (w.take m).foldl step (0, fun _ => 0, []) =
        (tokAt w m, a, (List.range m).map (fun i => target w (i + 1))) ∧
      ∀ t, a t = ((List.range m).reverse.find?
          (fun j => decide (1 ≤ j) && (tokAt w j == t))).elim 0
          (fun j => h (tokAt w (j + 1))) := by
  have tgt : ∀ i, target w i = ((List.range i).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i))).elim 0
      (fun j => h (tokAt w (j + 1))) := by
    intro i
    unfold target prevOcc
    cases hf : (List.range i).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) <;> simp [hf]
  have hfind : ∀ (m : ℕ) (p : ℕ → Bool), (List.range (m + 1)).reverse.find? p =
      if p m = true then some m else (List.range m).reverse.find? p := by
    intro m p
    rw [List.range_succ, List.reverse_append]
    cases hp : p m <;> simp [hp]
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun _ => 0, ?_, ?_⟩
    · simp [Lane4.Seq.tokAt_zero]
    · intro t; simp
  | succ m ih =>
    intro hm
    obtain ⟨a, hfold, ha⟩ := ih (by omega)
    have hlt : m < w.length := by omega
    have hx : w.take (m + 1) = w.take m ++ [w[m]] := by
      simp [List.take_succ, List.getElem?_eq_getElem hlt]
    have htok : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m hlt
    have hne : 1 ≤ m → tokAt w m ≠ 0 := by
      intro h1
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Lane4.Seq.tokAt_succ w k (by omega)]
      have := hw _ (List.getElem_mem (by omega : k < w.length))
      omega
    have hnew : ∀ t, (if tokAt w m ≠ 0 ∧ t = tokAt w m then h w[m] else a t) =
        ((List.range (m + 1)).reverse.find?
          (fun j => decide (1 ≤ j) && (tokAt w j == t))).elim 0
          (fun j => h (tokAt w (j + 1))) := by
      intro t
      rw [hfind m]
      by_cases hc : 1 ≤ m ∧ tokAt w m = t
      · obtain ⟨h1, h2⟩ := hc
        have hn := hne h1
        have : (decide (1 ≤ m) && (tokAt w m == t)) = true := by simp [h1, h2]
        rw [if_pos this, if_pos ⟨hn, h2.symm⟩, htok]
        rfl
      · have : ¬ ((decide (1 ≤ m) && (tokAt w m == t)) = true) := by
          intro hh
          apply hc
          simp at hh
          exact hh
        rw [if_neg this, ← ha t, if_neg]
        rintro ⟨h1, h2⟩
        apply hc
        refine ⟨?_, h2.symm⟩
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0
          exact absurd (Lane4.Seq.tokAt_zero w) h1
        · exact h0
    refine ⟨fun t => if tokAt w m ≠ 0 ∧ t = tokAt w m then h w[m] else a t, ?_, hnew⟩
    rw [hx, List.foldl_append, hfold]
    simp only [List.foldl_cons, List.foldl_nil, step]
    have hv : (if tokAt w m ≠ 0 ∧ w[m] = tokAt w m then h w[m] else a w[m]) =
        target w (m + 1) := by
      rw [hnew, tgt, htok]
    rw [hv, List.range_succ, List.map_append, htok]
    simp

theorem prog_correct : StatementProg prog := by
  intro w hw i hi1 hi
  obtain ⟨a, hfold, _⟩ := key w hw w.length le_rfl
  rw [List.take_length] at hfold
  unfold prog
  rw [hfold]
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp
  congr 1
  omega

end Lane4.Case
