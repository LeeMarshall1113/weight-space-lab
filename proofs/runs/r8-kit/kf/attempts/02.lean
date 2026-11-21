set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate Lane4.Cert Lane4.Cert8

theorem absState8_snoc (T : Task) (heads : List HCert) (l : List ℕ) (a : ℕ) :
    absState8 T heads (l ++ [a]) = absStep8 T heads (absState8 T heads l) a := by
  simp [absState8, List.foldl_append]

theorem abs_closed8 : AbsClosed8 := by
  intro T heads states h0 hs pre
  induction pre using List.reverseRecOn with
  | nil => intro _; simpa [absState8] using h0
  | append_singleton l a ih =>
    intro hall
    have h1 : ∀ t ∈ l, 1 ≤ t ∧ t ≤ T.ntok := fun t ht => hall t (by simp [ht])
    have h2 := hall a (by simp)
    rw [absState8_snoc]
    exact hs _ (ih h1) a h2.1 h2.2

theorem abs_len8 : AbsLen8 := by
  intro T heads pre
  induction pre using List.reverseRecOn with
  | nil => simp [absState8, absInit8]
  | append_singleton l a ih =>
    rw [absState8_snoc]
    simp [absStep8, List.length_zipWith, ih]

theorem abs_fst8 (T : Task) (heads : List HCert) (pre : List ℕ) :
    (absState8 T heads pre).1 = pre.foldl T.step T.init := by
  induction pre using List.reverseRecOn with
  | nil => simp [absState8, absInit8]
  | append_singleton l a ih =>
    rw [absState8_snoc]
    simp [absStep8, ih, List.foldl_append]

theorem abs_target8 : AbsTarget8 := by
  intro T heads w i h1 h2
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Task.target, abs_fst8, Nat.add_sub_cancel]
  simp [tokAt]

theorem zw_getD8 (f : HCert → List ℕ → List ℕ) (d : HCert) :
    ∀ (hs : List HCert) (l : List (List ℕ)) (a : ℕ), a < hs.length →
      l.length = hs.length →
      (List.zipWith f hs l).getD a [] = f (hs.getD a d) (l.getD a []) := by
  intro hs
  induction hs with
  | nil => intro l a h; simp at h
  | cons c cs ih =>
    intro l a ha hl
    cases l with
    | nil => simp at hl
    | cons p ps =>
      cases a with
      | zero => simp
      | succ a =>
        simp only [List.zipWith_cons_cons, List.getD_cons_succ]
        exact ih ps a (by simpa using ha) (by simpa using hl)

theorem map_getD8 (g : HCert → List ℕ) (d : HCert) :
    ∀ (hs : List HCert) (a : ℕ), a < hs.length →
      (hs.map g).getD a [] = g (hs.getD a d) := by
  intro hs
  induction hs with
  | nil => intro a h; simp at h
  | cons c cs ih =>
    intro a ha
    cases a with
    | zero => simp
    | succ a =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih a (by simpa using ha)

theorem tmt (f : ℕ → ℕ) : ∀ (n : ℕ) (l : List ℕ), (l.map f).take n = (l.take n).map f := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ n ih =>
    intro l
    cases l with
    | nil => simp
    | cons a l => simp only [List.map_cons, List.take_succ_cons, ih]

theorem ttt : ∀ (n : ℕ) (l : List ℕ), (l.take (n + 1)).take n = l.take n := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ n ih =>
    intro l
    cases l with
    | nil => simp
    | cons a l => simp only [List.take_succ_cons, ih]

theorem win_step (tok : ℕ → ℕ) (Q : List ℕ) (q L : ℕ) :
    ((tok q) :: (Q.take L).map tok).take L = ((q :: Q).take L).map tok := by
  cases L with
  | zero => simp
  | succ m => simp only [List.take_succ_cons, List.map_cons, tmt, ttt]

def Qs (cd : List Bool) (w : List ℕ) (k : ℕ) : List ℕ :=
  ((List.range (k + 1)).filter (fun j => cd.getD (tokAt w j) false)).reverse

theorem Qs_succ (cd : List Bool) (w : List ℕ) (k : ℕ) :
    Qs cd w (k + 1) = if cd.getD (tokAt w (k + 1)) false = true then (k + 1) :: Qs cd w k
      else Qs cd w k := by
  unfold Qs
  rw [show List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] from List.range_succ (n := k + 1)]
  by_cases hp : cd.getD (tokAt w (k + 1)) false = true
  · simp [List.filter_append, List.filter_cons, hp, List.reverse_append]
  · simp [List.filter_append, List.filter_cons, hp, List.reverse_append]

theorem inv_win (T : Task) (heads : List HCert) (w : List ℕ) (a : ℕ) (hc : HCert)
    (ha : a < heads.length) (hh : heads.getD a hc = hc) (hL : 1 ≤ hc.L) :
    ∀ k, k ≤ w.length →
      (absState8 T heads (w.take k)).2.getD a [] =
        ((Qs hc.cands w k).take hc.L).map (tokAt w) := by
  intro k
  induction k with
  | zero =>
    intro _
    have e : (absState8 T heads (w.take 0)).2.getD a [] =
        (if hc.cands.getD 0 false = true then [0] else []) := by
      simp only [List.take_zero, absState8, List.foldl_nil, absInit8]
      have := map_getD8 (fun c => if c.cands.getD 0 false = true then [0] else []) hc heads a ha
      rw [hh] at this
      exact this
    rw [e]
    have t0 : tokAt w 0 = 0 := by simp [tokAt]
    obtain ⟨m, hm⟩ : ∃ m, hc.L = m + 1 := ⟨hc.L - 1, by omega⟩
    rw [hm]
    by_cases hp : hc.cands.getD 0 false = true
    · have hp' : hc.cands[0]?.getD false = true := by simpa using hp
      simp [Qs, t0, hp, hp', List.filter_cons, List.range_one]
    · have hp' : ¬ hc.cands[0]?.getD false = true := by simpa using hp
      simp [Qs, t0, hp, hp', List.filter_cons, List.range_one]
  | succ k ih =>
    intro hk
    have hk' : k < w.length := by omega
    have ih' := ih (by omega)
    have tk : tokAt w (k + 1) = w.getD k 0 := by simp [tokAt]
    have ht : w.take (k + 1) = w.take k ++ [w.getD k 0] := by
      rw [List.take_succ]
      simp [List.getElem?_eq_getElem hk', List.getD_eq_getElem?_getD]
    have hlen := abs_len8 T heads (w.take k)
    have e : (absState8 T heads (w.take (k + 1))).2.getD a [] =
        winNext hc (w.getD k 0) ((absState8 T heads (w.take k)).2.getD a []) := by
      rw [ht, absState8_snoc]
      have := zw_getD8 (fun c win => winNext c (w.getD k 0) win) hc heads
        (absState8 T heads (w.take k)).2 a ha hlen
      rw [hh] at this
      exact this
    rw [e, ih', ← tk]
    by_cases hp : hc.cands.getD (tokAt w (k + 1)) false = true
    · rw [winNext, if_pos hp, Qs_succ, if_pos hp]
      exact win_step (tokAt w) (Qs hc.cands w k) (k + 1) hc.L
    · rw [winNext, if_neg hp, Qs_succ, if_neg hp]

theorem take_facts (Q : List ℕ) (L : ℕ) (hQ : Q.Pairwise (fun a b => b < a)) :
    (Q.take L).Pairwise (fun a b => b < a) ∧
    (∀ k ∈ Q, k ∉ Q.take L → ∀ j ∈ Q.take L, k < j) ∧
    (Q.take L).length ≤ L ∧ ((Q.take L).length < L → Q.take L = Q) := by
  refine ⟨hQ.sublist (List.take_sublist _ _), ?_, List.length_take_le _ _, ?_⟩
  · intro k hk hn j hj
    have e := List.take_append_drop L Q
    have hQ2 : (Q.take L ++ Q.drop L).Pairwise (fun a b => b < a) := by rw [e]; exact hQ
    have hk2 : k ∈ Q.take L ++ Q.drop L := by rw [e]; exact hk
    obtain ⟨_, _, h3⟩ := List.pairwise_append.mp hQ2
    have hkd : k ∈ Q.drop L := by
      rcases List.mem_append.mp hk2 with h | h
      · exact absurd h hn
      · exact h
    exact h3 j hj k hkd
  · intro hl
    by_cases hq : Q.length ≤ L
    · exact List.take_of_length_le hq
    · simp [List.length_take] at hl
      omega

theorem plain_case (m : Mask) (cd : List Bool) (tok : ℕ → ℕ) (n i k L : ℕ) (Q : List ℕ)
    (hQ : Q.Pairwise (fun a b => b < a))
    (hmem : ∀ j, j ∈ Q ↔ j ≤ k ∧ cd.getD (tok j) false = true)
    (hc1 : ∀ j ≤ k, j ∈ cand m n i)
    (hc2 : ∀ j ∈ cand m n i, cd.getD (tok j) false = true → j ≤ k) :
    WinPos m cd tok n i (Q.take L) ∧ (Q.take L).length ≤ L ∧
      ((Q.take L).length < L → ∀ j ∈ cand m n i, cd.getD (tok j) false = true →
        j ∈ Q.take L) := by
  obtain ⟨F1, F2, F3, F4⟩ := take_facts Q L hQ
  have W : WinPos m cd tok n i (Q.take L) := by
    unfold WinPos
    refine ⟨F1, ?_, ?_⟩
    · intro j hj
      have := (hmem j).mp (List.mem_of_mem_take hj)
      exact ⟨hc1 j this.1, this.2⟩
    · intro j hj hcd hn j' hj'
      exact F2 j ((hmem j).mpr ⟨hc2 j hj hcd, hcd⟩) hn j' hj'
  refine ⟨W, F3, ?_⟩
  intro hl j hj hcd
  rw [F4 hl]
  exact (hmem j).mpr ⟨hc2 j hj hcd, hcd⟩

theorem cons_case (m : Mask) (cd : List Bool) (tok : ℕ → ℕ) (n i k L : ℕ) (Q : List ℕ)
    (hQ : Q.Pairwise (fun a b => b < a))
    (hmem : ∀ j, j ∈ Q ↔ j ≤ k ∧ cd.getD (tok j) false = true)
    (q : ℕ) (hq : cd.getD (tok q) false = true) (hqc : q ∈ cand m n i)
    (hlt : ∀ j ≤ k, j < q)
    (hc1 : ∀ j ≤ k, j ∈ cand m n i)
    (hc2 : ∀ j ∈ cand m n i, cd.getD (tok j) false = true → j ≤ k ∨ j = q) :
    WinPos m cd tok n i (q :: Q.take L) ∧ (q :: Q.take L).length ≤ L + 1 ∧
      ((q :: Q.take L).length < L + 1 → ∀ j ∈ cand m n i, cd.getD (tok j) false = true →
        j ∈ q :: Q.take L) := by
  obtain ⟨F1, F2, F3, F4⟩ := take_facts Q L hQ
  have W : WinPos m cd tok n i (q :: Q.take L) := by
    unfold WinPos
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨fun b hb => ?_, F1⟩
      have := (hmem b).mp (List.mem_of_mem_take hb)
      exact hlt b this.1
    · intro j hj
      rcases List.mem_cons.mp hj with h | hj
      · subst h
        exact ⟨hqc, hq⟩
      · have := (hmem j).mp (List.mem_of_mem_take hj)
        exact ⟨hc1 j this.1, this.2⟩
    · intro j hj hcd hn j' hj'
      have hjq : j ≠ q := fun e => hn (List.mem_cons.mpr (Or.inl e))
      have hjk : j ≤ k := by
        rcases hc2 j hj hcd with h | h
        · exact h
        · exact absurd h hjq
      have hjn : j ∉ Q.take L := fun e => hn (List.mem_cons.mpr (Or.inr e))
      rcases List.mem_cons.mp hj' with h | hj'
      · rw [h]; exact hlt j hjk
      · exact F2 j ((hmem j).mpr ⟨hjk, hcd⟩) hjn j' hj'
  refine ⟨W, ?_, ?_⟩
  · rw [List.length_cons]; omega
  · intro hl j hj hcd
    rw [List.length_cons] at hl
    have hl2 : (Q.take L).length < L := by omega
    rcases hc2 j hj hcd with h | h
    · exact List.mem_cons.mpr (Or.inr (by rw [F4 hl2]; exact (hmem j).mpr ⟨h, hcd⟩))
    · exact List.mem_cons.mpr (Or.inl h)

theorem abs_keys8 : AbsKeys8 := by
  intro T heads w i a h hc h1 h2 ha hhc hm hL
  have hmask : h.mask = Mask.causal ∨ h.mask = Mask.strict := by
    cases hh : h.mask <;> first | exact absurd hh hm | exact Or.inl rfl | exact Or.inr rfl
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k ≤ w.length := by omega
  have hwin := inv_win T heads w a hc ha hhc hL k hk
  simp only [Nat.add_sub_cancel]
  rw [hwin]
  have hmem : ∀ j, j ∈ Qs hc.cands w k ↔ j ≤ k ∧ hc.cands.getD (tokAt w j) false = true := by
    intro j
    simp only [Qs, List.mem_reverse, List.mem_filter, List.mem_range]
    constructor <;> rintro ⟨e1, e2⟩ <;> exact ⟨by omega, e2⟩
  have hpw : (Qs hc.cands w k).Pairwise (fun a b => b < a) := by
    have := (List.pairwise_lt_range (k + 1)).filter (fun j => hc.cands.getD (tokAt w j) false)
    unfold Qs
    rw [List.pairwise_reverse]
    exact this
  generalize Qs hc.cands w k = Q at hmem hpw ⊢
  rcases hmask with hmc | hms
  · by_cases hp : hc.cands.getD (tokAt w (k + 1)) false = true
    · have hk1 : keysAt h hc (tokAt w (k + 1)) ((Q.take hc.L).map (tokAt w)) =
          tokAt w (k + 1) :: (Q.take hc.L).map (tokAt w) := by
        simp [keysAt, hmc, hp]
      have hf : fullLen h hc (tokAt w (k + 1)) = hc.L + 1 := by
        simp [fullLen, hmc, hp]
      obtain ⟨A, B, C⟩ := cons_case h.mask hc.cands (tokAt w) (w.length + 1) (k + 1) k hc.L Q
        hpw hmem (k + 1) hp (by simp [hmc, cand]) (fun j hj => by omega)
        (fun j hj => by simp [hmc, cand]; omega)
        (fun j hj _ => by simp [hmc, cand] at hj; omega)
      refine ⟨(k + 1) :: Q.take hc.L, A, ?_, ?_, ?_⟩
      · rw [hk1]; rfl
      · rw [hf]; exact B
      · rw [hf]; exact C
    · have hk1 : keysAt h hc (tokAt w (k + 1)) ((Q.take hc.L).map (tokAt w)) =
          (Q.take hc.L).map (tokAt w) := by
        simp [keysAt, hmc, hp]
      have hf : fullLen h hc (tokAt w (k + 1)) = hc.L := by
        simp [fullLen, hmc, hp]
      obtain ⟨A, B, C⟩ := plain_case h.mask hc.cands (tokAt w) (w.length + 1) (k + 1) k hc.L Q
        hpw hmem (fun j hj => by simp [hmc, cand]; omega)
        (fun j hj hcd => by
          simp [hmc, cand] at hj
          by_contra hne
          have : j = k + 1 := by omega
          subst this
          exact hp hcd)
      refine ⟨Q.take hc.L, A, ?_, ?_, ?_⟩
      · rw [hk1]
      · rw [hf]; exact B
      · rw [hf]; exact C
  · have hk1 : keysAt h hc (tokAt w (k + 1)) ((Q.take hc.L).map (tokAt w)) =
        (Q.take hc.L).map (tokAt w) := by
      simp [keysAt, hms]
    have hf : fullLen h hc (tokAt w (k + 1)) = hc.L := by
      simp [fullLen, hms]
    obtain ⟨A, B, C⟩ := plain_case h.mask hc.cands (tokAt w) (w.length + 1) (k + 1) k hc.L Q
      hpw hmem (fun j hj => by simp [hms, cand]; omega)
      (fun j hj _ => by simp [hms, cand] at hj; omega)
    refine ⟨Q.take hc.L, A, ?_, ?_, ?_⟩
    · rw [hk1]
    · rw [hf]; exact B
    · rw [hf]; exact C

end Lane4.Case
