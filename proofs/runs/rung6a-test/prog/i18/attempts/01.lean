namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, table token -> value for next occurrence, outputs). -/
def step (s : ℕ × (ℕ → ℕ) × List ℕ) (x : ℕ) : ℕ × (ℕ → ℕ) × List ℕ :=
  (x, fun t => if t = s.1 then h x else s.2.1 t,
    s.2.2 ++ [if x = s.1 then h x else s.2.1 x])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, fun _ => 0, [])).2.2

-- PROOF

theorem prevOcc_eq (w : List ℕ) (i : ℕ) :
    prevOcc w i = (List.range i).reverse.find?
      (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) := rfl

theorem pf_succ (w : List ℕ) (tk i : ℕ) :
    (List.range (i + 1)).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tk)) =
    if (1 ≤ i ∧ tokAt w i = tk) then some i else
      (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tk)) := by
  by_cases h1 : 1 ≤ i <;> by_cases h2 : tokAt w i = tk <;> simp [List.range_succ, h1, h2]

theorem pf_skip (w : List ℕ) (tk i : ℕ) (hn : ¬ (1 ≤ i ∧ tokAt w i = tk)) :
    (List.range (i + 1)).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tk)) =
    (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tk)) := by
  rw [pf_succ, if_neg hn]

theorem pf_congr (u v : List ℕ) (tk i : ℕ) (hh : ∀ j, j < i → tokAt u j = tokAt v j) :
    (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt u j == tk)) =
    (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt v j == tk)) := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pf_succ, pf_succ, hh n (by omega), ih (fun j hj => hh j (by omega))]

theorem pf_spec (w : List ℕ) (tk i j : ℕ)
    (hh : (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tk)) = some j) :
    j < i ∧ tokAt w j = tk := by
  induction i with
  | zero => simp at hh
  | succ n ih =>
    rw [pf_succ] at hh
    split_ifs at hh with hc
    · injection hh with e
      subst e
      exact ⟨by omega, hc.2⟩
    · have := ih hh
      exact ⟨by omega, this.2⟩

theorem prevOcc_spec (w : List ℕ) (i j : ℕ) (hq : prevOcc w i = some j) :
    j < i ∧ tokAt w j = tokAt w i :=
  pf_spec w (tokAt w i) i j hq

theorem prevOcc_congr (u v : List ℕ) (i : ℕ) (hh : ∀ j, j ≤ i → tokAt u j = tokAt v j) :
    prevOcc u i = prevOcc v i := by
  rw [prevOcc_eq, prevOcc_eq, hh i le_rfl]
  exact pf_congr u v _ i (fun j hj => hh j (by omega))

theorem target_some (w : List ℕ) (i j : ℕ) (hq : prevOcc w i = some j) :
    target w i = h (tokAt w (j + 1)) := by
  unfold target
  rw [hq] <;> rfl

theorem target_none (w : List ℕ) (i : ℕ) (hq : prevOcc w i = none) :
    target w i = 0 := by
  unfold target
  rw [hq] <;> rfl

theorem target_congr (u v : List ℕ) (i : ℕ) (hh : ∀ j, j ≤ i → tokAt u j = tokAt v j) :
    target u i = target v i := by
  have hp := prevOcc_congr u v i hh
  cases hq : prevOcc v i with
  | none =>
    have hu : prevOcc u i = none := by rw [hp]; exact hq
    rw [target_none u i hu, target_none v i hq]
  | some j =>
    have hu : prevOcc u i = some j := by rw [hp]; exact hq
    have hj := (prevOcc_spec v i j hq).1
    rw [target_some u i j hu, target_some v i j hq, hh (j + 1) (by omega)]

theorem tokAt_app_le (w : List ℕ) (x j : ℕ) (hj : j ≤ w.length) :
    tokAt (w ++ [x]) j = tokAt w j := by
  rcases j with _ | k
  · rw [Lane4.Seq.tokAt_zero, Lane4.Seq.tokAt_zero]
  · have hk : k < w.length := by omega
    have hk2 : k < (w ++ [x]).length := by
      rw [List.length_append]
      exact Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)
    rw [Lane4.Seq.tokAt_succ _ _ hk2, Lane4.Seq.tokAt_succ _ _ hk]
    simp [hk]

theorem tokAt_app_succ (w : List ℕ) (x : ℕ) : tokAt (w ++ [x]) (w.length + 1) = x := by
  have hk : w.length < (w ++ [x]).length := by simp
  rw [Lane4.Seq.tokAt_succ _ _ hk]
  simp

theorem len_pos_of (w : List ℕ) (t : ℕ) (ht : 1 ≤ t) (hp : tokAt w w.length = t) :
    1 ≤ w.length := by
  by_contra hc
  have h0 : w.length = 0 := by omega
  rw [h0, Lane4.Seq.tokAt_zero] at hp
  omega

theorem tgt_nil (t : ℕ) :
    target (([] : List ℕ) ++ [t]) (([] : List ℕ).length + 1) = 0 := by
  first
  | rfl
  | simp [target, prevOcc]

theorem tgt_B1 (w : List ℕ) (x : ℕ) (hL : 1 ≤ w.length) (hp : tokAt w w.length = x) :
    target (w ++ [x]) (w.length + 1) = h x := by
  have p2 : 1 ≤ w.length ∧ tokAt (w ++ [x]) w.length = x :=
    ⟨hL, by rw [tokAt_app_le w x _ le_rfl]; exact hp⟩
  have hpo : prevOcc (w ++ [x]) (w.length + 1) = some w.length := by
    rw [prevOcc_eq, tokAt_app_succ, pf_succ, if_pos p2]
  rw [target_some _ _ _ hpo, tokAt_app_succ]

theorem tgt_B2 (w : List ℕ) (x t : ℕ) (hL : 1 ≤ w.length) (hp : tokAt w w.length = t)
    (hx : x ≠ t) :
    target ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1) = h x := by
  have hW : (w ++ [x]).length = w.length + 1 := by simp
  have e1 : tokAt ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1) = t := tokAt_app_succ _ _
  have n1 : ¬ (1 ≤ w.length + 1 ∧ tokAt ((w ++ [x]) ++ [t]) (w.length + 1) = t) := by
    rintro ⟨_, hh⟩
    rw [tokAt_app_le (w ++ [x]) t (w.length + 1) (by simp), tokAt_app_succ] at hh
    exact hx hh
  have p2 : 1 ≤ w.length ∧ tokAt ((w ++ [x]) ++ [t]) w.length = t :=
    ⟨hL, by
      rw [tokAt_app_le (w ++ [x]) t w.length (by simp), tokAt_app_le w x w.length le_rfl]
      exact hp⟩
  have hpo : prevOcc ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1) = some w.length := by
    rw [prevOcc_eq, e1, hW, pf_skip _ _ _ n1, pf_succ, if_pos p2]
  rw [target_some _ _ _ hpo, tokAt_app_le (w ++ [x]) t (w.length + 1) (by simp),
    tokAt_app_succ]

theorem tgt_C (w : List ℕ) (x t : ℕ) (hp : tokAt w w.length ≠ t) (hx : x ≠ t) :
    target ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1) = target (w ++ [t]) (w.length + 1) := by
  have hW : (w ++ [x]).length = w.length + 1 := by simp
  have e1 : tokAt ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1) = t := tokAt_app_succ _ _
  have e2 : tokAt (w ++ [t]) (w.length + 1) = t := tokAt_app_succ _ _
  have n1 : ¬ (1 ≤ w.length + 1 ∧ tokAt ((w ++ [x]) ++ [t]) (w.length + 1) = t) := by
    rintro ⟨_, hh⟩
    rw [tokAt_app_le (w ++ [x]) t (w.length + 1) (by simp), tokAt_app_succ] at hh
    exact hx hh
  have n2 : ¬ (1 ≤ w.length ∧ tokAt ((w ++ [x]) ++ [t]) w.length = t) := by
    rintro ⟨_, hh⟩
    rw [tokAt_app_le (w ++ [x]) t w.length (by simp), tokAt_app_le w x w.length le_rfl] at hh
    exact hp hh
  have n3 : ¬ (1 ≤ w.length ∧ tokAt (w ++ [t]) w.length = t) := by
    rintro ⟨_, hh⟩
    rw [tokAt_app_le w t w.length le_rfl] at hh
    exact hp hh
  have hpf := pf_congr ((w ++ [x]) ++ [t]) (w ++ [t]) t w.length (fun j hj => by
    rw [tokAt_app_le (w ++ [x]) t j (by rw [hW]; omega), tokAt_app_le w x j (by omega),
      tokAt_app_le w t j (by omega)])
  have C_pf : prevOcc ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1) =
      prevOcc (w ++ [t]) (w.length + 1) := by
    rw [prevOcc_eq, prevOcc_eq, e1, e2, hW, pf_skip _ _ _ n1, pf_skip _ _ _ n2,
      pf_skip _ _ _ n3, hpf]
  cases hq : prevOcc (w ++ [t]) (w.length + 1) with
  | none =>
    have h1' : prevOcc ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1) = none := by
      rw [C_pf]; exact hq
    rw [target_none _ _ h1', target_none _ _ hq]
  | some j =>
    have h1' : prevOcc ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1) = some j := by
      rw [C_pf]; exact hq
    obtain ⟨hj1, hj2⟩ := prevOcc_spec _ _ _ hq
    rw [tokAt_app_succ] at hj2
    have hjL : j < w.length := by
      rcases Nat.lt_or_ge j w.length with hlt | hge
      · exact hlt
      · exfalso
        have hje : j = w.length := by omega
        subst hje
        rw [tokAt_app_le w t _ le_rfl] at hj2
        exact hp hj2
    rw [target_some _ _ _ h1', target_some _ _ _ hq,
      tokAt_app_le (w ++ [x]) t (j + 1) (by rw [hW]; omega),
      tokAt_app_le w x (j + 1) (by omega), tokAt_app_le w t (j + 1) (by omega)]

theorem step_inv (w : List ℕ) (x : ℕ) (s : ℕ × (ℕ → ℕ) × List ℕ) (hx : 1 ≤ x)
    (hI : s.1 = tokAt w w.length ∧ s.2.2.length = w.length ∧
      (∀ i, 1 ≤ i → i ≤ w.length → s.2.2.getD (i - 1) 0 = target w i) ∧
      (∀ t, 1 ≤ t → t ≠ s.1 → s.2.1 t = target (w ++ [t]) (w.length + 1))) :
    (step s x).1 = tokAt (w ++ [x]) (w ++ [x]).length ∧
    (step s x).2.2.length = (w ++ [x]).length ∧
    (∀ i, 1 ≤ i → i ≤ (w ++ [x]).length →
      (step s x).2.2.getD (i - 1) 0 = target (w ++ [x]) i) ∧
    (∀ t, 1 ≤ t → t ≠ (step s x).1 →
      (step s x).2.1 t = target ((w ++ [x]) ++ [t]) ((w ++ [x]).length + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  have hW : (w ++ [x]).length = w.length + 1 := by simp
  have hv : (if x = s.1 then h x else s.2.1 x) = target (w ++ [x]) (w.length + 1) := by
    by_cases hxp : x = s.1
    · rw [if_pos hxp]
      have hp : tokAt w w.length = x := by rw [← h1]; exact hxp.symm
      exact (tgt_B1 w x (len_pos_of w x hx hp) hp).symm
    · rw [if_neg hxp]
      exact h4 x hx hxp
  refine ⟨?_, ?_, ?_, ?_⟩
  · show x = _
    rw [hW, tokAt_app_succ]
  · show (s.2.2 ++ [if x = s.1 then h x else s.2.1 x]).length = _
    simp [hW, h2]
  · intro i hi1 hi2
    show (s.2.2 ++ [if x = s.1 then h x else s.2.1 x]).getD (i - 1) 0 = _
    rw [hW] at hi2
    by_cases hle : i ≤ w.length
    · have hlt : i - 1 < s.2.2.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        ← List.getD_eq_getElem?_getD, h3 i hi1 hle]
      exact (target_congr (w ++ [x]) w i (fun j hj => tokAt_app_le w x j (by omega))).symm
    · have hi : i = w.length + 1 := by omega
      subst hi
      rw [← hv, Nat.add_sub_cancel, ← h2, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (le_refl _)]
      simp
  · intro t ht hne
    have hne' : t ≠ x := hne
    show (if t = s.1 then h x else s.2.1 t) = _
    by_cases htp : t = s.1
    · rw [if_pos htp]
      have hp : tokAt w w.length = t := by rw [← h1]; exact htp.symm
      exact (tgt_B2 w x t (len_pos_of w t ht hp) hp (Ne.symm hne')).symm
    · rw [if_neg htp, h4 t ht htp]
      have hp : tokAt w w.length ≠ t := by
        rw [← h1]
        exact fun e => htp e.symm
      exact (tgt_C w x t hp (Ne.symm hne')).symm

theorem inv_fold (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t) :
    (w.foldl step (0, fun _ => 0, [])).1 = tokAt w w.length ∧
    (w.foldl step (0, fun _ => 0, [])).2.2.length = w.length ∧
    (∀ i, 1 ≤ i → i ≤ w.length →
      (w.foldl step (0, fun _ => 0, [])).2.2.getD (i - 1) 0 = target w i) ∧
    (∀ t, 1 ≤ t → t ≠ (w.foldl step (0, fun _ => 0, [])).1 →
      (w.foldl step (0, fun _ => 0, [])).2.1 t = target (w ++ [t]) (w.length + 1)) := by
  refine List.reverseRecOn (motive := fun w => (∀ t ∈ w, 1 ≤ t) →
    ((w.foldl step (0, fun _ => 0, [])).1 = tokAt w w.length ∧
    (w.foldl step (0, fun _ => 0, [])).2.2.length = w.length ∧
    (∀ i, 1 ≤ i → i ≤ w.length →
      (w.foldl step (0, fun _ => 0, [])).2.2.getD (i - 1) 0 = target w i) ∧
    (∀ t, 1 ≤ t → t ≠ (w.foldl step (0, fun _ => 0, [])).1 →
      (w.foldl step (0, fun _ => 0, [])).2.1 t = target (w ++ [t]) (w.length + 1))))
    w ?_ ?_ hw
  · intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (Lane4.Seq.tokAt_zero []).symm
    · rfl
    · intro i hi1 hi2
      have : i ≤ 0 := hi2
      omega
    · intro t _ _
      exact (tgt_nil t).symm
  · intro w x ih hall
    have hx : 1 ≤ x := hall x (by simp)
    have ih' := ih (fun t ht => hall t (by simp [ht]))
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact step_inv w x _ hx ih'

theorem prog_correct : StatementProg prog := by
  intro w hw i hi1 hi2
  have := inv_fold w (fun t ht => (hw t ht).1)
  exact this.2.2.1 i hi1 hi2

end Lane4.Case
