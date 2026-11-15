namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, successor-of-last-1, successor-of-last-2, outputs so far). -/
def stepP (s : ℕ × ℕ × ℕ × List ℕ) (t : ℕ) : ℕ × ℕ × ℕ × List ℕ :=
  (t,
   if t = 1 then 0 else if s.1 = 1 then t else s.2.1,
   if t = 2 then 0 else if s.1 = 2 then t else s.2.2.1,
   s.2.2.2 ++ [if t = 1 then h (if s.1 = 1 then 1 else s.2.1)
               else if t = 2 then h (if s.1 = 2 then 2 else s.2.2.1) else 0])

def prog (w : List ℕ) : List ℕ := (w.foldl stepP (0, 0, 0, [])).2.2.2

-- PROOF

theorem find_succ (p : ℕ → Bool) (n : ℕ) :
    (List.range (n + 1)).reverse.find? p
      = if p n = true then some n else (List.range n).reverse.find? p := by
  cases hpn : p n <;> simp [List.range_succ, List.find?_cons, hpn]

theorem find_congr (p q : ℕ → Bool) (n : ℕ) (hpq : ∀ j < n, p j = q j) :
    (List.range n).reverse.find? p = (List.range n).reverse.find? q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [find_succ, find_succ, hpq n (Nat.lt_succ_self n),
      ih (fun j hj => hpq j (by omega))]

theorem find_lt (p : ℕ → Bool) (n j : ℕ)
    (hf : (List.range n).reverse.find? p = some j) : j < n := by
  induction n with
  | zero => simp at hf
  | succ n ih =>
    rw [find_succ] at hf
    by_cases hp : p n = true
    · rw [if_pos hp] at hf
      have := Option.some.inj hf
      omega
    · rw [if_neg hp] at hf
      have := ih hf
      omega

theorem tok_snoc_lt (l : List ℕ) (x j : ℕ) (hj : j ≤ l.length) :
    tokAt (l ++ [x]) j = tokAt l j := by
  rcases j with _ | k
  · simp [tokAt]
  · have hk : k < l.length := by omega
    first
      | (simp [tokAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]; done)
      | (simp [tokAt, hk]; done)
      | (simp [tokAt, List.getD_append _ _ _ _ hk]; done)

theorem tok_snoc_self (l : List ℕ) (x : ℕ) :
    tokAt (l ++ [x]) (l.length + 1) = x := by
  first
    | (simp [tokAt]; done)
    | (simp [tokAt, List.getD_eq_getElem?_getD, List.getElem?_append_right]; done)
    | (simp [tokAt, List.getD_eq_getElem?_getD, List.getElem?_concat_length]; done)

theorem nxt_snoc (l : List ℕ) (x t : ℕ) (ht : 1 ≤ t) :
    (match (List.range ((l ++ [x]).length + 1)).reverse.find?
        (fun j => decide (1 ≤ j) && (tokAt (l ++ [x]) j == t)) with
      | some j => tokAt (l ++ [x]) (j + 1)
      | none => 0)
    = (if x = t then 0 else if tokAt l l.length = t then x else
        (match (List.range (l.length + 1)).reverse.find?
          (fun j => decide (1 ≤ j) && (tokAt l j == t)) with
        | some j => tokAt l (j + 1)
        | none => 0)) := by
  have hlen : (l ++ [x]).length = l.length + 1 := by simp
  rw [hlen]
  set Q : ℕ → Bool := fun j => decide (1 ≤ j) && (tokAt (l ++ [x]) j == t) with hQ
  set P : ℕ → Bool := fun j => decide (1 ≤ j) && (tokAt l j == t) with hP
  have hQP : ∀ j < l.length + 1, Q j = P j := by
    intro j hj
    simp only [hQ, hP]
    rw [tok_snoc_lt l x j (by omega)]
  rw [find_succ Q (l.length + 1)]
  by_cases hx : x = t
  · have hQt : Q (l.length + 1) = true := by simp [hQ, tok_snoc_self, hx]
    rw [if_pos hQt, if_pos hx]
    show tokAt (l ++ [x]) (l.length + 1 + 1) = 0
    exact Lane4.Seq.tokAt_beyond _ _ (by simp)
  · have hQf : ¬ (Q (l.length + 1) = true) := by simp [hQ, tok_snoc_self, hx]
    rw [if_neg hQf, if_neg hx]
    rw [find_congr Q P (l.length + 1) hQP, find_succ P l.length]
    by_cases hp : tokAt l l.length = t
    · have hl : 1 ≤ l.length := by
        rcases Nat.eq_zero_or_pos l.length with h0 | h0
        · exfalso
          rw [h0, Lane4.Seq.tokAt_zero] at hp
          omega
        · exact h0
      have hPl : P l.length = true := by simp [hP, hp, hl]
      rw [if_pos hPl, if_pos hp]
      show tokAt (l ++ [x]) (l.length + 1) = x
      exact tok_snoc_self l x
    · have hPl : ¬ (P l.length = true) := by simp [hP, hp]
      rw [if_neg hPl, if_neg hp]
      have hlt : ∀ j, (List.range l.length).reverse.find? P = some j → j < l.length :=
        fun j hj => find_lt P l.length j hj
      generalize (List.range l.length).reverse.find? P = F at hlt ⊢
      cases F with
      | none => rfl
      | some j =>
        have hj := hlt j rfl
        show tokAt (l ++ [x]) (j + 1) = tokAt l (j + 1)
        exact tok_snoc_lt l x (j + 1) (by omega)

theorem target_snoc_lt (l : List ℕ) (x i : ℕ) (hi : i ≤ l.length) :
    target (l ++ [x]) i = target l i := by
  unfold target prevOcc
  set Q : ℕ → Bool := fun j => decide (1 ≤ j) && (tokAt (l ++ [x]) j == tokAt (l ++ [x]) i)
    with hQ
  set P : ℕ → Bool := fun j => decide (1 ≤ j) && (tokAt l j == tokAt l i) with hP
  have hQP : ∀ j < i, Q j = P j := by
    intro j hj
    simp only [hQ, hP]
    rw [tok_snoc_lt l x j (by omega), tok_snoc_lt l x i hi]
  rw [find_congr Q P i hQP]
  have hlt : ∀ j, (List.range i).reverse.find? P = some j → j < i :=
    fun j hj => find_lt P i j hj
  generalize (List.range i).reverse.find? P = F at hlt ⊢
  cases F with
  | none => rfl
  | some j =>
    have hj := hlt j rfl
    show h (tokAt (l ++ [x]) (j + 1)) = h (tokAt l (j + 1))
    rw [tok_snoc_lt l x (j + 1) (by omega)]

theorem target_last (l : List ℕ) (x : ℕ) (hx : 1 ≤ x) :
    target (l ++ [x]) (l.length + 1)
    = if tokAt l l.length = x then h x else
        h (match (List.range (l.length + 1)).reverse.find?
            (fun j => decide (1 ≤ j) && (tokAt l j == x)) with
          | some j => tokAt l (j + 1)
          | none => 0) := by
  unfold target prevOcc
  simp only [tok_snoc_self]
  set Q : ℕ → Bool := fun j => decide (1 ≤ j) && (tokAt (l ++ [x]) j == x) with hQ
  set P : ℕ → Bool := fun j => decide (1 ≤ j) && (tokAt l j == x) with hP
  have hQP : ∀ j < l.length + 1, Q j = P j := by
    intro j hj
    simp only [hQ, hP]
    rw [tok_snoc_lt l x j (by omega)]
  rw [find_congr Q P (l.length + 1) hQP, find_succ P l.length]
  by_cases hp : tokAt l l.length = x
  · have hl : 1 ≤ l.length := by
      rcases Nat.eq_zero_or_pos l.length with h0 | h0
      · exfalso
        rw [h0, Lane4.Seq.tokAt_zero] at hp
        omega
      · exact h0
    have hPl : P l.length = true := by simp [hP, hp, hl]
    rw [if_pos hPl, if_pos hp]
    show h (tokAt (l ++ [x]) (l.length + 1)) = h x
    rw [tok_snoc_self]
  · have hPl : ¬ (P l.length = true) := by simp [hP, hp]
    rw [if_neg hPl, if_neg hp]
    have hlt : ∀ j, (List.range l.length).reverse.find? P = some j → j < l.length :=
      fun j hj => find_lt P l.length j hj
    generalize (List.range l.length).reverse.find? P = F at hlt ⊢
    cases F with
    | none => simp [h]
    | some j =>
      have hj := hlt j rfl
      show h (tokAt (l ++ [x]) (j + 1)) = h (tokAt l (j + 1))
      rw [tok_snoc_lt l x (j + 1) (by omega)]

theorem fold_inv (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) :
    (w.foldl stepP (0, 0, 0, [])).1 = tokAt w w.length ∧
    (w.foldl stepP (0, 0, 0, [])).2.1
      = (match (List.range (w.length + 1)).reverse.find?
          (fun j => decide (1 ≤ j) && (tokAt w j == 1)) with
        | some j => tokAt w (j + 1)
        | none => 0) ∧
    (w.foldl stepP (0, 0, 0, [])).2.2.1
      = (match (List.range (w.length + 1)).reverse.find?
          (fun j => decide (1 ≤ j) && (tokAt w j == 2)) with
        | some j => tokAt w (j + 1)
        | none => 0) ∧
    (w.foldl stepP (0, 0, 0, [])).2.2.2.length = w.length ∧
    ∀ i, 1 ≤ i → i ≤ w.length →
      (w.foldl stepP (0, 0, 0, [])).2.2.2.getD (i - 1) 0 = target w i := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [tokAt]
    · first | rfl | decide | simp
    · first | rfl | decide | simp
    · simp
    · intro i h1 h2
      simp at h2
      omega
  | append_singleton l x ih =>
    obtain ⟨hp, ha, hb, hlen, hout⟩ := ih (fun t ht => hw t (by simp [ht]))
    have hx : 1 ≤ x ∧ x ≤ 2 := hw x (by simp)
    have hf : (l ++ [x]).foldl stepP (0, 0, 0, [])
        = stepP (l.foldl stepP (0, 0, 0, [])) x := by
      simp [List.foldl_append]
    rw [hf]
    generalize l.foldl stepP (0, 0, 0, []) = s at hp ha hb hlen hout ⊢
    obtain ⟨p, a, b, out⟩ := s
    dsimp only at hp ha hb hlen hout
    subst hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [stepP, tok_snoc_self]
    · rw [nxt_snoc l x 1 (le_refl _), ← ha]
      rfl
    · rw [nxt_snoc l x 2 (by omega), ← hb]
      rfl
    · simp [stepP, hlen]
    · intro i h1 h2
      have h2' : i ≤ l.length + 1 := by simpa using h2
      rcases Nat.lt_or_ge i (l.length + 1) with hlt | hge
      · have hi : i ≤ l.length := by omega
        rw [target_snoc_lt l x i hi]
        have hg : (stepP (tokAt l l.length, a, b, out) x).2.2.2.getD (i - 1) 0
            = out.getD (i - 1) 0 := by
          have hk : i - 1 < out.length := by omega
          first
            | (simp [stepP, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]; done)
            | (simp [stepP, List.getD_append _ _ _ _ hk]; done)
        rw [hg]
        exact hout i h1 hi
      · have hi : i = l.length + 1 := by omega
        subst hi
        rw [target_last l x hx.1]
        have hg : (stepP (tokAt l l.length, a, b, out) x).2.2.2.getD (l.length + 1 - 1) 0
            = (if x = 1 then h (if tokAt l l.length = 1 then 1 else a)
                else if x = 2 then h (if tokAt l l.length = 2 then 2 else b) else 0) := by
          have hk : l.length + 1 - 1 = out.length := by omega
          rw [hk]
          first
            | (simp [stepP, List.getD_eq_getElem?_getD]; done)
            | (simp [stepP, List.getD_eq_getElem?_getD, List.getElem?_append_right]; done)
            | (simp [stepP, List.getD_eq_getElem?_getD, List.getElem?_concat_length]; done)
        rw [hg]
        subst ha
        subst hb
        have hx12 : x = 1 ∨ x = 2 := by omega
        rcases hx12 with rfl | rfl
        · by_cases hq : tokAt l l.length = 1 <;> simp [hq]
        · by_cases hq : tokAt l l.length = 2 <;> simp [hq]

theorem prog_correct : StatementProg prog := by
  intro w hw i h1 h2
  obtain ⟨_, _, _, _, hout⟩ := fold_inv w hw
  exact hout i h1 h2

end Lane4.Case
