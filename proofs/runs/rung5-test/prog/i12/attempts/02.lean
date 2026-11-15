namespace Lane4.Case
open Lane4.Seq (tokAt)

/-- State: (previous token, table token -> h(next token after its last seen occurrence), outputs). -/
def stp1 (s : ℕ × (ℕ → ℕ) × List ℕ) (x : ℕ) : ℕ × (ℕ → ℕ) × List ℕ :=
  (x, Function.update s.2.1 s.1 (h x), s.2.2 ++ [Function.update s.2.1 s.1 (h x) x])

def prog (w : List ℕ) : List ℕ := (w.foldl stp1 (0, fun _ => 0, [])).2.2

def pgo1 (u : List ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | n + 1, t => if 1 ≤ n ∧ tokAt u n = t then some n else pgo1 u n t

def tvl1 (u : List ℕ) : Option ℕ → ℕ
  | none => 0
  | some j => h (tokAt u (j + 1))

-- PROOF

theorem tokApp1 (u v : List ℕ) (j : ℕ) (hj : j ≤ u.length) :
    tokAt (u ++ v) j = tokAt u j := by
  unfold tokAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [show (0 :: (u ++ v)) = (0 :: u) ++ v from rfl,
    List.getElem?_append_left (by simp; omega)]

theorem tokSnoc1 (u : List ℕ) (x : ℕ) : tokAt (u ++ [x]) (u.length + 1) = x := by
  unfold tokAt
  rw [List.getD_eq_getElem?_getD]
  rw [show (0 :: (u ++ [x])) = (0 :: u) ++ [x] from rfl,
    List.getElem?_append_right (by simp)]
  simp

theorem pgoSucc1 (u : List ℕ) (n t : ℕ) :
    pgo1 u (n + 1) t = if 1 ≤ n ∧ tokAt u n = t then some n else pgo1 u n t := by
  simp only [pgo1]

theorem pgoLt1 (u : List ℕ) (n t j : ℕ) (hj : pgo1 u n t = some j) : j < n := by
  induction n with
  | zero => simp [pgo1] at hj
  | succ n ih =>
    rw [pgoSucc1] at hj
    by_cases hc : 1 ≤ n ∧ tokAt u n = t
    · rw [if_pos hc] at hj
      cases hj
      omega
    · rw [if_neg hc] at hj
      have := ih hj
      omega

theorem pgoEq1 (u : List ℕ) (n t : ℕ) :
    pgo1 u n t = (List.range n).reverse.find? (fun j => decide (1 ≤ j) && (tokAt u j == t)) := by
  induction n with
  | zero => simp [pgo1]
  | succ n ih =>
    rw [pgoSucc1, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    simp only [List.find?_cons]
    by_cases hc : 1 ≤ n ∧ tokAt u n = t
    · simp [hc]
    · rw [if_neg hc, ih]
      have : ¬ ((decide (1 ≤ n) && (tokAt u n == t)) = true) := by
        intro h0
        apply hc
        simpa using h0
      cases hb : (decide (1 ≤ n) && (tokAt u n == t))
      · simp
      · exact absurd hb this

theorem pgoAgree1 (u : List ℕ) (x t : ℕ) (n : ℕ) (hn : n ≤ u.length) :
    pgo1 (u ++ [x]) n t = pgo1 u n t := by
  induction n with
  | zero => simp [pgo1]
  | succ n ih =>
    rw [pgoSucc1, pgoSucc1, ih (by omega), tokApp1 u [x] n (by omega)]

theorem tvlAgree1 (u : List ℕ) (x : ℕ) (o : Option ℕ)
    (ho : ∀ j, o = some j → j < u.length) :
    tvl1 (u ++ [x]) o = tvl1 u o := by
  cases o with
  | none => simp [tvl1]
  | some j =>
    have hj := ho j rfl
    simp only [tvl1]
    rw [tokApp1 u [x] (j + 1) (by omega)]

theorem inv1 (u : List ℕ) (hu : ∀ t ∈ u, 1 ≤ t) :
    (u.foldl stp1 (0, fun _ => 0, [])).1 = tokAt u u.length ∧
    (∀ t, t ≠ 0 → (u.foldl stp1 (0, fun _ => 0, [])).2.1 t = tvl1 u (pgo1 u u.length t)) ∧
    (u.foldl stp1 (0, fun _ => 0, [])).2.2.length = u.length ∧
    (∀ i, 1 ≤ i → i ≤ u.length →
      (u.foldl stp1 (0, fun _ => 0, [])).2.2.getD (i - 1) 0
        = tvl1 u (pgo1 u i (tokAt u i))) := by
  induction u using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [tokAt]
    · intro t _
      simp [pgo1, tvl1]
    · simp
    · intro i h1 h2
      simp at h2
      omega
  | append_singleton u x ih =>
    have hu' : ∀ t ∈ u, 1 ≤ t := fun t ht => hu t (List.mem_append_left _ ht)
    have hx : 1 ≤ x := hu x (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := ih hu'
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize u.foldl stp1 (0, fun _ => 0, []) = s at h1 h2 h3 h4 ⊢
    obtain ⟨p, T, o⟩ := s
    dsimp only at h1 h2 h3 h4
    simp only [List.length_append, List.length_singleton]
    have hT : ∀ t, t ≠ 0 →
        Function.update T p (h x) t = tvl1 (u ++ [x]) (pgo1 (u ++ [x]) (u.length + 1) t) := by
      intro t ht
      rw [pgoSucc1, tokApp1 u [x] u.length (le_refl _), pgoAgree1 u x t u.length (le_refl _)]
      by_cases htp : t = p
      · subst htp
        have hn : 1 ≤ u.length := by
          by_contra hcon
          have h0 : u.length = 0 := by omega
          rw [h0] at h1
          simp [tokAt] at h1
          exact ht h1.symm
        rw [Function.update_self, h1]
        have hc : 1 ≤ u.length ∧ tokAt u u.length = tokAt u u.length := ⟨hn, rfl⟩
        rw [if_pos hc]
        simp only [tvl1]
        rw [tokSnoc1]
      · rw [Function.update_of_ne htp, h2 t ht]
        have hc : ¬ (1 ≤ u.length ∧ tokAt u u.length = t) := by
          intro hc
          apply htp
          rw [h1]
          exact hc.2.symm
        rw [if_neg hc]
        exact (tvlAgree1 u x _ (fun j hj => pgoLt1 u _ t j hj)).symm
    refine ⟨rfl, hT, ?_, ?_⟩
    · simp [h3]
    · intro i hi1 hi2
      rcases Nat.lt_or_ge i (u.length + 1) with hlt | hge
      · have hi3 : i ≤ u.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD, h4 i hi1 hi3, tokApp1 u [x] i hi3,
          pgoAgree1 u x _ i hi3]
        exact (tvlAgree1 u x _ (fun j hj => by
          have := pgoLt1 u i _ j hj
          omega)).symm
      · have hi : i = u.length + 1 := by omega
        subst hi
        rw [List.getD_eq_getElem?_getD, Nat.add_sub_cancel,
          List.getElem?_append_right (by omega)]
        have hl : u.length - o.length = 0 := by omega
        rw [hl, tokSnoc1]
        have := hT x (by omega)
        simp only [List.getElem?_cons_zero, Option.getD_some]
        rw [this]
        rw [tokSnoc1]

theorem prog_correct : StatementProg prog := by
  intro w hw i hi1 hi2
  have hw1 : ∀ t ∈ w, 1 ≤ t := fun t ht => (hw t ht).1
  obtain ⟨_, _, _, h4⟩ := inv1 w hw1
  unfold prog
  rw [h4 i hi1 hi2]
  unfold target prevOcc
  rw [← pgoEq1]
  cases hp : pgo1 w i (tokAt w i) <;> simp [tvl1]

end Lane4.Case
