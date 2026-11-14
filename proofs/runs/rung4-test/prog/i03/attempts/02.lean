namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, successor table, outputs so far). -/
def step (s : ℕ × (ℕ → ℕ) × List ℕ) (t : ℕ) : ℕ × (ℕ → ℕ) × List ℕ :=
  (t, fun c => if c = t then 0 else if c = s.1 then t else s.2.1 c,
   s.2.2 ++ [if s.1 = t then h t else h (s.2.1 t)])

def prog (w : List ℕ) : List ℕ := (w.foldl step (0, fun _ => 0, [])).2.2

def pv (w : List ℕ) (c : ℕ) : ℕ → Option ℕ
  | 0 => none
  | i + 1 => if (decide (1 ≤ i) && (tokAt w i == c)) = true then some i else pv w c i

def nxv (l : List ℕ) (c : ℕ) : ℕ :=
  match pv l c (l.length + 1) with
  | some j => if j < l.length then tokAt l (j + 1) else 0
  | none => 0

-- PROOF

theorem find_eq (w : List ℕ) (c : ℕ) : ∀ i,
    (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == c)) = pv w c i := by
  intro i
  induction i with
  | zero => simp [pv]
  | succ i ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.find?_cons, pv]
    by_cases hc : (decide (1 ≤ i) && (tokAt w i == c)) = true
    · simp [hc]
    · simp only [hc]
      simpa using ih

theorem target_eq (w : List ℕ) (i : ℕ) :
    target w i = (match pv w (tokAt w i) i with
      | some j => h (tokAt w (j + 1))
      | none => 0) := by
  unfold target prevOcc
  rw [find_eq]

theorem pv_some (w : List ℕ) (c : ℕ) : ∀ i j, pv w c i = some j →
    j < i ∧ 1 ≤ j ∧ tokAt w j = c := by
  intro i
  induction i with
  | zero => intro j hj; simp [pv] at hj
  | succ i ih =>
    intro j hj
    simp only [pv] at hj
    by_cases hc : (decide (1 ≤ i) && (tokAt w i == c)) = true
    · rw [if_pos hc] at hj
      have hj' : i = j := by simpa using hj
      subst hj'
      simp at hc
      exact ⟨by omega, hc.1, hc.2⟩
    · rw [if_neg hc] at hj
      obtain ⟨a, b, d⟩ := ih j hj
      exact ⟨by omega, b, d⟩

theorem pv_top (w : List ℕ) (c m : ℕ) (h1 : 1 ≤ m) (h2 : tokAt w m = c) :
    pv w c (m + 1) = some m := by
  simp [pv, h1, h2]

theorem pv_congr (a b : List ℕ) (c : ℕ) : ∀ i, (∀ j, j < i → tokAt a j = tokAt b j) →
    pv a c i = pv b c i := by
  intro i
  induction i with
  | zero => intro _; simp [pv]
  | succ i ih =>
    intro hab
    simp only [pv]
    rw [ih (fun j hj => hab j (by omega)), hab i (by omega)]

theorem tok_prefix (l : List ℕ) (t j : ℕ) (hj : j ≤ l.length) :
    tokAt (l ++ [t]) j = tokAt l j := by
  unfold tokAt
  rw [show (0 :: (l ++ [t])) = (0 :: l) ++ [t] from rfl, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]

theorem tok_last (l : List ℕ) (t : ℕ) : tokAt (l ++ [t]) (l.length + 1) = t := by
  unfold tokAt
  rw [show (0 :: (l ++ [t])) = (0 :: l) ++ [t] from rfl, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

theorem inv (l : List ℕ) (hl : ∀ t ∈ l, 1 ≤ t) :
    (l.foldl step (0, fun _ => 0, [])).1 = tokAt l l.length ∧
    (∀ c, 1 ≤ c → (l.foldl step (0, fun _ => 0, [])).2.1 c = nxv l c) ∧
    (l.foldl step (0, fun _ => 0, [])).2.2.length = l.length ∧
    (∀ i, 1 ≤ i → i ≤ l.length →
      (l.foldl step (0, fun _ => 0, [])).2.2.getD (i - 1) 0 = target l i) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [tokAt], ?_, by simp, ?_⟩
    · intro c _
      simp [nxv, pv]
    · intro i h1 h2
      simp at h2
      omega
  | append_singleton l t ih =>
    have ht : 1 ≤ t := hl t (by simp)
    obtain ⟨hp, hn, hlen, ho⟩ := ih (fun x hx => hl x (by simp [hx]))
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize l.foldl step (0, fun _ => 0, []) = S at hp hn hlen ho ⊢
    obtain ⟨p, nx, out⟩ := S
    dsimp only at hp hn hlen ho
    simp only [step]
    have hm : (l ++ [t]).length = l.length + 1 := by simp
    -- the old pv value
    have hpv : ∀ c, pv (l ++ [t]) c (l.length + 1) = pv l c (l.length + 1) := by
      intro c
      apply pv_congr
      intro j hj
      exact tok_prefix l t j (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hm, tok_last]
    · intro c hc
      dsimp only
      unfold nxv
      rw [hm]
      simp only [pv]
      rw [tok_last, hpv c]
      by_cases hct : c = t
      · subst hct
        simp
      · have hct' : ¬ (t = c) := fun e => hct e.symm
        have hb : (decide (1 ≤ l.length + 1) && (t == c)) = false := by
          simp [hct']
        rw [hb]
        simp only [Bool.false_eq_true, if_false]
        rw [if_neg hct]
        by_cases hcp : c = p
        · subst hcp
          have hm1 : 1 ≤ l.length := by
            by_contra hh
            have : l.length = 0 := by omega
            rw [this, Lane4.Seq.tokAt_zero] at hp
            omega
          rw [pv_top l c l.length hm1 hp.symm]
          simp [tok_last]
        · rw [if_neg hcp, hn c hc]
          unfold nxv
          cases hr : pv l c (l.length + 1) with
          | none => simp
          | some j =>
            obtain ⟨hj1, hj2, hj3⟩ := pv_some l c _ j hr
            have hjm : j < l.length := by
              by_contra hh
              have : j = l.length := by omega
              subst this
              exact hcp (hj3.symm.trans hp.symm ▸ rfl)
            simp only [hjm, if_true]
            rw [if_pos (by omega)]
            exact (tok_prefix l t (j + 1) (by omega)).symm
    · simp [hlen]
    · intro i hi1 hi2
      rw [hm] at hi2
      by_cases hi : i ≤ l.length
      · -- old position
        have hlt : i - 1 < out.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        rw [← List.getD_eq_getElem?_getD, ho i hi1 hi]
        rw [target_eq, target_eq, tok_prefix l t i hi]
        have : pv (l ++ [t]) (tokAt l i) i = pv l (tokAt l i) i := by
          apply pv_congr
          intro j hj
          exact tok_prefix l t j (by omega)
        rw [this]
        cases hr : pv l (tokAt l i) i with
        | none => rfl
        | some j =>
          obtain ⟨hj1, _, _⟩ := pv_some l _ _ j hr
          simp only
          rw [tok_prefix l t (j + 1) (by omega)]
      · -- new position
        have hi' : i = l.length + 1 := by omega
        subst hi'
        have hidx : l.length + 1 - 1 = out.length := by omega
        rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
        simp only [Option.getD_some]
        rw [target_eq, hm, tok_last, hpv t]
        cases hr : pv l t (l.length + 1) with
        | none =>
          have hpt : p ≠ t := by
            intro e
            have hm1 : 1 ≤ l.length := by
              by_contra hh
              have : l.length = 0 := by omega
              rw [this, Lane4.Seq.tokAt_zero] at hp
              omega
            have := pv_top l t l.length hm1 (hp.symm.trans e)
            rw [hr] at this
            simp at this
          have := hn t ht
          unfold nxv at this
          rw [hr] at this
          simp only at this
          rw [if_neg hpt, this]
          simp [h]
        | some j =>
          obtain ⟨hj1, hj2, hj3⟩ := pv_some l t _ j hr
          by_cases hpt : p = t
          · have hm1 : 1 ≤ l.length := by
              by_contra hh
              have : l.length = 0 := by omega
              rw [this, Lane4.Seq.tokAt_zero] at hp
              omega
            have := pv_top l t l.length hm1 (hp.symm.trans hpt)
            rw [hr] at this
            have hj : j = l.length := by simpa using this
            subst hj
            rw [if_pos hpt]
            simp [tok_last]
          · have := hn t ht
            unfold nxv at this
            rw [hr] at this
            simp only at this
            have hjm : j < l.length := by
              by_contra hh
              have : j = l.length := by omega
              subst this
              exact hpt (hp.trans hj3)
            rw [if_pos hjm] at this
            rw [if_neg hpt, this]
            simp only
            rw [tok_prefix l t (j + 1) (by omega)]

theorem prog_correct : StatementProg prog := by
  intro w hw i hi1 hi
  obtain ⟨_, _, _, h4⟩ := inv w (fun t ht => (hw t ht).1)
  exact h4 i hi1 hi

end Lane4.Case
