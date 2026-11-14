namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, table token -> successor of its last completed occurrence, outputs). -/
def step (s : ℕ × (ℕ → ℕ) × List ℕ) (t : ℕ) : ℕ × (ℕ → ℕ) × List ℕ :=
  (t, fun u => if u = s.1 then t else s.2.1 u,
    s.2.2 ++ [h (if t = s.1 then t else s.2.1 t)])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, fun _ => 0, [])).2.2

-- PROOF

def ln (w : List ℕ) (u : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if 1 ≤ i ∧ tokAt w i = u then tokAt w (i + 1) else ln w u i

theorem vo_eq (w : List ℕ) (u : ℕ) (i : ℕ) :
    (match (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == u)) with
      | some j => h (tokAt w (j + 1))
      | none => 0) = h (ln w u i) := by
  induction i with
  | zero => simp [ln, h]
  | succ i ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons]
    by_cases hc : 1 ≤ i ∧ tokAt w i = u
    · have e : (decide (1 ≤ i) && (tokAt w i == u)) = true := by simp [hc.1, hc.2]
      rw [e]
      simp [ln, hc]
    · have e : (decide (1 ≤ i) && (tokAt w i == u)) = false := by
        by_cases h1 : 1 ≤ i
        · have : tokAt w i ≠ u := fun h2 => hc ⟨h1, h2⟩
          simp [this]
        · simp [h1]
      rw [e]
      simp only [ln, hc, if_false]
      exact ih

theorem target_eq (w : List ℕ) (i : ℕ) : target w i = h (ln w (tokAt w i) i) := by
  unfold target prevOcc
  rw [← vo_eq w (tokAt w i) i]
  cases (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) <;> rfl

theorem fold_inv (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) :
    ∀ (l pre : List ℕ) (s : ℕ × (ℕ → ℕ) × List ℕ), pre ++ l = w →
    s.1 = tokAt w pre.length →
    (∀ u, 1 ≤ u → s.2.1 u = ln w u pre.length) →
    s.2.2.length = pre.length →
    (∀ i, 1 ≤ i → i ≤ pre.length → s.2.2.getD (i - 1) 0 = target w i) →
    ((l.foldl step s).2.2.length = w.length ∧
      ∀ i, 1 ≤ i → i ≤ w.length → (l.foldl step s).2.2.getD (i - 1) 0 = target w i) := by
  intro l
  induction l with
  | nil =>
    intro pre s hp _ _ hl ho
    have : pre = w := by simpa using hp
    subst this
    exact ⟨hl, ho⟩
  | cons x l ih =>
    intro pre s hp h1 h2 hl ho
    have hxw : x ∈ w := by rw [← hp]; simp
    have hx1 : 1 ≤ x := (hw x hxw).1
    have hlt : pre.length < w.length := by
      rw [← hp]; simp
    have htok : tokAt w (pre.length + 1) = x := by
      rw [Lane4.Seq.tokAt_succ w pre.length hlt, ← hp]
      simp
    have hp' : (pre ++ [x]) ++ l = w := by rw [← hp]; simp
    simp only [List.foldl_cons]
    apply ih (pre ++ [x]) (step s x) hp'
    · simp [step, htok]
    · intro u hu
      simp only [step, List.length_append, List.length_singleton]
      show (if u = s.1 then x else s.2.1 u) = ln w u (pre.length + 1)
      simp only [ln]
      by_cases hu1 : u = s.1
      · have hc : 1 ≤ pre.length ∧ tokAt w pre.length = u := by
          refine ⟨?_, by rw [← h1]; exact hu1.symm⟩
          rcases Nat.eq_zero_or_pos pre.length with h0 | h0
          · exfalso
            have : s.1 = 0 := by rw [h1, h0]; exact Lane4.Seq.tokAt_zero w
            omega
          · exact h0
        rw [if_pos hu1, if_pos hc, htok]
      · have hc : ¬ (1 ≤ pre.length ∧ tokAt w pre.length = u) := by
          rintro ⟨_, h3⟩
          exact hu1 (by rw [h1, h3])
        rw [if_neg hu1, if_neg hc, h2 u hu]
    · simp [step, hl]
    · intro i hi1 hi2
      have hxx : (if x = s.1 then x else s.2.1 x) = ln w x (pre.length + 1) := by
        simp only [ln]
        by_cases hu1 : x = s.1
        · have hc : 1 ≤ pre.length ∧ tokAt w pre.length = x := by
            refine ⟨?_, by rw [← h1]; exact hu1.symm⟩
            rcases Nat.eq_zero_or_pos pre.length with h0 | h0
            · exfalso
              have : s.1 = 0 := by rw [h1, h0]; exact Lane4.Seq.tokAt_zero w
              omega
            · exact h0
          rw [if_pos hu1, if_pos hc, htok]
        · have hc : ¬ (1 ≤ pre.length ∧ tokAt w pre.length = x) := by
            rintro ⟨_, h3⟩
            exact hu1 (by rw [h1, h3])
          rw [if_neg hu1, if_neg hc, h2 x hx1]
      simp only [step, List.length_append, List.length_singleton] at hi2 ⊢
      rcases Nat.lt_or_ge i (pre.length + 1) with hlt2 | hge
      · have hi3 : i ≤ pre.length := by omega
        have hgl : i - 1 < s.2.2.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hgl]
        rw [← List.getD_eq_getElem?_getD]
        exact ho i hi1 hi3
      · have hieq : i = pre.length + 1 := by omega
        subst hieq
        have : pre.length + 1 - 1 = s.2.2.length := by omega
        rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [hxx, target_eq, htok]

theorem prog_correct : StatementProg prog := by
  intro w hw i hi1 hi2
  have := fold_inv w hw w [] (0, fun _ => 0, []) (by simp)
    (by simp [Lane4.Seq.tokAt_zero]) (by intro u _; simp [ln]) (by simp)
    (by intro i h1 h2; simp at h2; omega)
  exact this.2 i hi1 hi2

end Lane4.Case
