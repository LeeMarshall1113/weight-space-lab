set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd rsum)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2

/-! ### small facts -/

theorem SC_pos : (0 : ℤ) < SC := by unfold SC; norm_num
theorem SC_real : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num

theorem wide_mag (s : FF) (e : ℤ) : (s.wide e).mag = s.mag + e := by
  simp only [FF.mag, FF.dev, FF.wide]
  ring

theorem mag_nonneg_of_inff (e : ℕ → ℝ) (v : ℝ) (a : FF) (h : InFF e v a) : 0 ≤ a.mag := by
  have h1 := Lane4.LNKD.inff_r_nonneg e v a h
  have h2 := Lane4.LNKD.linI_nonneg a.t
  have h3 := Lane4.LNKD.iabs_nonneg' a.c
  unfold FF.mag FF.dev
  omega

/-! ### list helpers -/

theorem getD_map_lt {α β : Type} (f : α → β) (d : α) (d' : β) :
    ∀ (l : List α) (k : ℕ), k < l.length → (l.map f).getD k d' = f (l.getD k d)
  | [], k, h => by simp at h
  | a :: l, 0, _ => by simp
  | a :: l, k + 1, h => by
      simp only [List.map_cons, List.getD_cons_succ]
      exact getD_map_lt f d d' l k (by simpa using h)

theorem mem_idx {α : Type} (d : α) : ∀ (l : List α) (a : α), a ∈ l →
    ∃ j, j < l.length ∧ l.getD j d = a
  | [], a, h => by simp at h
  | x :: l, a, h => by
      rcases List.mem_cons.mp h with h1 | h1
      · subst h1
        exact ⟨0, by simp, by simp⟩
      · obtain ⟨j, hj, hja⟩ := mem_idx d l a h1
        exact ⟨j + 1, by simpa using hj, by simpa using hja⟩

theorem getD_app_lt : ∀ (Q R : List ℤ) (j : ℕ), j < Q.length → (Q ++ R).getD j 0 = Q.getD j 0
  | [], R, j, h => by simp at h
  | a :: Q, R, 0, _ => by simp
  | a :: Q, R, j + 1, h => by
      simp only [List.cons_append, List.getD_cons_succ]
      exact getD_app_lt Q R j (by simpa using h)

theorem getD_app_ge : ∀ (Q R : List ℤ) (j : ℕ), Q.length ≤ j →
    (Q ++ R).getD j 0 = R.getD (j - Q.length) 0
  | [], R, j, _ => by simp
  | a :: Q, R, 0, h => by simp at h
  | a :: Q, R, j + 1, h => by
      simp only [List.cons_append, List.getD_cons_succ, List.length_cons]
      rw [getD_app_ge Q R j (by simpa using h), Nat.add_sub_add_right]

theorem getD_rep : ∀ (m j : ℕ), (List.replicate m (0 : ℤ)).getD j 0 = 0
  | 0, j => by simp
  | m + 1, 0 => by simp
  | m + 1, j + 1 => by
      simp only [List.replicate_succ, List.getD_cons_succ]
      exact getD_rep m j

theorem allSomeL_spec {α : Type} (d : α) : ∀ (l : List (Option α)) (r : List α),
    allSomeL l = some r →
    r.length = l.length ∧ ∀ i, i < l.length → l.getD i none = some (r.getD i d)
  | [], r, h => by
      simp [allSomeL] at h
      subst h
      exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | none :: l, r, h => by simp [allSomeL] at h
  | some a :: l, r, h => by
      cases hl : allSomeL l with
      | none => simp [allSomeL, hl] at h
      | some r' =>
        simp [allSomeL, hl] at h
        subst h
        obtain ⟨h1, h2⟩ := allSomeL_spec d l r' hl
        refine ⟨by simp [h1], ?_⟩
        intro i hi
        cases i with
        | zero => simp
        | succ i =>
          simp only [List.getD_cons_succ]
          exact h2 i (by simpa using hi)

theorem radd_length (fl : ℝ → ℝ) : ∀ (a b : List ℝ), (radd fl a b).length = min a.length b.length
  | [], b => by simp [radd]
  | a :: x, [] => by simp [radd]
  | a :: x, b :: y => by
      rw [show radd fl (a :: x) (b :: y) = fl (a + b) :: radd fl x y from rfl, List.length_cons,
        radd_length fl x y]
      simp only [List.length_cons]
      omega

theorem radd_getD (fl : ℝ → ℝ) : ∀ (a b : List ℝ) (j : ℕ), j < a.length → j < b.length →
    (radd fl a b).getD j 0 = fl (a.getD j 0 + b.getD j 0)
  | [], b, j, h, _ => by simp at h
  | a :: x, [], j, _, h => by simp at h
  | a :: x, b :: y, 0, _, _ => by simp [radd]
  | a :: x, b :: y, j + 1, h1, h2 => by
      simp only [radd, List.getD_cons_succ]
      exact radd_getD fl x y j (by simpa using h1) (by simpa using h2)

theorem araffine_length (fl : ℝ → ℝ) : ∀ (M : List (List ℚ)) (b : List ℚ) (x : List ℝ)
    (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (i : ℕ),
    (araffine fl M b x dW db i).length = min M.length b.length
  | [], b, x, dW, db, i => by simp [araffine]
  | r :: M, [], x, dW, db, i => by simp [araffine]
  | r :: M, c :: b, x, dW, db, i => by
      simp only [araffine, List.length_cons]
      rw [araffine_length fl M b x dW db (i + 1)]
      omega

theorem araffine_get (fl : ℝ → ℝ) (x : List ℝ) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) :
    ∀ (M : List (List ℚ)) (b : List ℚ) (i j : ℕ), j < M.length → j < b.length →
    (araffine fl M b x dW db i).getD j 0 =
      fl (ardot fl (M.getD j []) x (dW (i + j)) 0 0 + asw fl (b.getD j 0) (db (i + j)))
  | [], b, i, j, h, _ => by simp at h
  | r :: M, [], i, j, _, h => by simp at h
  | r :: M, c :: b, i, 0, _, _ => by simp [araffine]
  | r :: M, c :: b, i, j + 1, h1, h2 => by
      simp only [araffine, List.getD_cons_succ]
      rw [araffine_get fl x dW db M b (i + 1) j (by simpa using h1) (by simpa using h2)]
      rw [show i + 1 + j = i + (j + 1) by omega]

theorem dotRows_len (dI : ℤ) (ns slot0 : ℕ) (xs : List FF) (ms : List ℤ) (sd sc : ℤ) :
    ∀ (W : List (List ℤ)) (b : List ℤ) (slot : ℕ),
    (dotRows dI ns slot0 xs ms sd sc W b slot).length = min W.length b.length
  | [], b, slot => by simp [dotRows]
  | w :: W, [], slot => by simp [dotRows]
  | w :: W, b0 :: b, slot => by
      simp only [dotRows, List.length_cons]
      rw [dotRows_len dI ns slot0 xs ms sd sc W b (slot + 1)]
      omega

theorem dotRows_get (dI : ℤ) (ns slot0 : ℕ) (xs : List FF) (ms : List ℤ) (sd sc : ℤ) :
    ∀ (W : List (List ℤ)) (b : List ℤ) (slot j : ℕ), j < W.length → j < b.length →
    (dotRows dI ns slot0 xs ms sd sc W b slot).getD j (false, zeroF 0) =
      dotF dI ns (some slot0) (some (slot + j)) (W.getD j []) xs ms sd sc (b.getD j 0)
  | [], b, slot, j, h, _ => by simp at h
  | w :: W, [], slot, j, _, h => by simp at h
  | w :: W, b0 :: b, slot, 0, _, _ => by simp [dotRows]
  | w :: W, b0 :: b, slot, j + 1, h1, h2 => by
      simp only [dotRows, List.getD_cons_succ]
      rw [dotRows_get dI ns slot0 xs ms sd sc W b (slot + 1) j (by simpa using h1) (by simpa using h2)]
      rw [show slot + 1 + j = slot + (j + 1) by omega]

theorem addHO_len (ns hB slot0 : ℕ) (n8 : ℤ) :
    ∀ (acc : List FF) (ho : List AF) (r : ℕ),
    (addHO ns hB slot0 n8 acc ho r).length = min acc.length ho.length
  | [], ho, r => by simp [addHO]
  | a :: acc, [], r => by simp [addHO]
  | a :: acc, o :: ho, r => by
      simp only [addHO, List.length_cons]
      rw [addHO_len ns hB slot0 n8 acc ho (r + 1)]
      omega

theorem addHO_get (ns hB slot0 : ℕ) (n8 : ℤ) :
    ∀ (acc : List FF) (ho : List AF) (r j : ℕ), j < acc.length → j < ho.length →
    (addHO ns hB slot0 n8 acc ho r).getD j (false, zeroF 0) =
      addOne (acc.getD j (zeroF 0)) (hoF ns hB (slot0 + r + j) n8 (ho.getD j ⟨0, [], 0⟩))
  | [], ho, r, j, h, _ => by simp at h
  | a :: acc, [], r, j, _, h => by simp at h
  | a :: acc, o :: ho, r, 0, _, _ => by simp [addHO]
  | a :: acc, o :: ho, r, j + 1, h1, h2 => by
      simp only [addHO, List.getD_cons_succ]
      rw [addHO_get ns hB slot0 n8 acc ho (r + 1) j (by simpa using h1) (by simpa using h2)]
      rw [show slot0 + (r + 1) + j = slot0 + r + (j + 1) by omega]

theorem splitOK_get {l : List (Bool × FF)} {r : List FF} (h : splitOK l = some r) :
    r.length = l.length ∧ ∀ j, j < l.length →
      (l.getD j (false, zeroF 0)).1 = true ∧
        r.getD j (zeroF 0) = (l.getD j (false, zeroF 0)).2 := by
  unfold splitOK at h
  by_cases hh : l.all (fun p => p.1) = true
  · rw [if_pos hh] at h
    have hr : l.map (fun p => p.2) = r := Option.some.inj h
    subst hr
    refine ⟨by simp, ?_⟩
    intro j hj
    refine ⟨?_, ?_⟩
    · exact List.all_eq_true.mp hh _ (zgetD_mem' (false, zeroF 0) l j hj)
    · exact getD_map_lt (fun p => p.2) (false, zeroF 0) (zeroF 0) l j hj
  · rw [if_neg hh] at h
    simp at h

theorem splitOK1_some {p : Bool × FF} {o : FF} (h : splitOK1 p = some o) : p.1 = true ∧ p.2 = o := by
  unfold splitOK1 at h
  by_cases hh : p.1 = true
  · rw [if_pos hh] at h
    exact ⟨hh, Option.some.inj h⟩
  · rw [if_neg hh] at h
    simp at h

/-! ### rounded sums of forms -/

theorem addOne_facts (a : FF) (h : Bool × FF) (hg : (addOne a h).1 = true) :
    h.1 = true ∧ (addOne a h).2.mag ≤ 15 * SC := by
  have h1 : (h.1 && FF.small ((a.add h.2).wide (chg (a.add h.2).mag))) = true := hg
  rw [Bool.and_eq_true] at h1
  have h2 : FF.small ((a.add h.2).wide (chg (a.add h.2).mag)) = true := h1.2
  unfold FF.small at h2
  exact ⟨h1.1, of_decide_eq_true h2⟩

theorem add_sound3 {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (e : ℕ → ℝ) (x y : ℝ) (a b : FF)
    (he : Sym e) (hx : InFF e x a) (hy : InFF e y b) (hlen : a.t.length = b.t.length)
    (hsm : (addOne a (true, b)).2.mag ≤ 15 * SC) : InFF e (fl (x + y)) (addOne a (true, b)).2 := by
  have hs : InFF e (x + y) (a.add b) := by
    unfold InFF at hx hy ⊢
    simp only [FF.add]
    rw [Lane4.LNKD.linValI_zipWith_add e a.t b.t 0 hlen]
    push_cast
    have e1 : (x + y) * 2 ^ 56 - (((a.c : ℝ) + b.c) + (linValI a.t e 0 + linValI b.t e 0))
        = (x * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0)) + (y * 2 ^ 56 - ((b.c : ℝ) + linValI b.t e 0)) := by
      ring
    rw [e1]
    exact le_trans (abs_add_le _ _) (add_le_add hx hy)
  have hbs := Lane4.LNKD.box_sound e (x + y) (a.add b) he hs
  have hm0 := mag_nonneg_of_inff e (x + y) (a.add b) hs
  have hsm' : (a.add b).mag + chg (a.add b).mag ≤ 15 * SC := by
    have : ((a.add b).wide (chg (a.add b).mag)).mag ≤ 15 * SC := hsm
    rw [wide_mag] at this
    exact this
  have hc0 : 0 ≤ chg (a.add b).mag := by
    unfold chg
    have := Int.ediv_nonneg hm0 (by norm_num : (0 : ℤ) ≤ 2 ^ 22)
    omega
  have hSCp := SC_pos
  have hm16 : (a.add b).mag ≤ 16 * SC := by omega
  have h1 : (((a.add b).mag : ℤ) : ℝ) ≤ 16 * 2 ^ 56 := by
    have := (show (((a.add b).mag : ℤ) : ℝ) ≤ (((16 * SC : ℤ)) : ℝ) by exact_mod_cast hm16)
    rw [Int.cast_mul, SC_real] at this
    simpa using this
  have h16 : |x + y| ≤ 16 := by
    have : |x + y| * 2 ^ 56 ≤ 16 * 2 ^ 56 := le_trans hbs.2.2 h1
    exact le_of_mul_le_mul_right this (by norm_num)
  have hxy : |x + y| ≤ M := by
    have := hC.M1
    have h40 : (2 : ℝ) ^ 40 ≥ 16 := by norm_num
    linarith
  have hf := hC.rnd.err (x + y) hxy
  exact Lane4.LNKD.wide_round hC e he (x + y) (fl (x + y)) (a.add b) hs hf

/-! ### the head output slots -/

theorem hoF_len (ns hB slot : ℕ) (n8 : ℤ) (o : AF) (h : (hoF ns hB slot n8 o).1 = true) :
    (hoF ns hB slot n8 o).2.t.length = ns := by
  have hg' : (zeroFrom hB ⟨floorQ o.c, padTo ns (o.t.map floorQ), 0⟩
      && ((⟨floorQ o.c, padTo ns (o.t.map floorQ), 0⟩ : FF).t.length == ns)) = true := h
  rw [Bool.and_eq_true, beq_iff_eq] at hg'
  have h2 : (padTo ns (o.t.map floorQ)).length = ns := hg'.2
  show (addAt (padTo ns (o.t.map floorQ)) slot (ceilQ o.r + 1 + n8)).length = ns
  rw [Lane4.LNKD.addAt_length]
  exact h2

theorem hoF_coeff (ns hB slot n8 : ℕ) (a : AF) (pre : ℕ) (rest : List ℚ)
    (hat : a.t = List.replicate pre 0 ++ rest) (hrest : rest.length ≤ n8) (k : ℕ)
    (hk : k ≠ slot) (hk2 : ¬ (pre ≤ k ∧ k < pre + n8)) :
    (hoF ns hB slot (n8 : ℤ) a).2.t.getD k 0 = 0 := by
  have hF : (hoF ns hB slot (n8 : ℤ) a).2.t
      = addAt (padTo ns (a.t.map floorQ)) slot (ceilQ a.r + 1 + (n8 : ℤ)) := rfl
  rw [hF, Lane4.LNKD.addAt_getD_ne _ _ _ _ hk]
  have hL : a.t.map floorQ = List.replicate pre 0 ++ rest.map floorQ := by
    rw [hat, List.map_append, List.map_replicate, Lane4.LNKD.floorQ_zero]
  have hLen : (a.t.map floorQ).length = pre + rest.length := by
    rw [hL]; simp
  unfold padTo
  by_cases h1 : k < pre
  · have h2 : k < (a.t.map floorQ).length := by omega
    rw [getD_app_lt _ _ _ h2, hL, getD_app_lt _ _ _ (by simpa using h1)]
    exact getD_rep _ _
  · have h2 : (a.t.map floorQ).length ≤ k := by omega
    rw [getD_app_ge _ _ _ h2]
    exact getD_rep _ _

theorem ho_coord (e0 : ℕ → ℝ) (he0 : Sym e0) (v : ℝ) (a : AF) (pre : ℕ) (rest : List ℚ)
    (ns hB slot n8 : ℕ) (hv : InAF e0 v a) (hat : a.t = List.replicate pre 0 ++ rest)
    (hrest : rest.length ≤ n8) (hBs : hB ≤ slot) (hsl : slot < ns)
    (hg : (hoF ns hB slot (n8 : ℤ) a).1 = true) :
    ∃ s : ℝ, |s| ≤ 1 ∧ ∀ e : ℕ → ℝ, (∀ k, pre ≤ k → k < pre + n8 → e k = e0 k) → e slot = s →
      InFF e v (hoF ns hB slot (n8 : ℤ) a).2 := by
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ :=
    Lane4.LNKD.ho_f_sound e0 v a pre rest ns hB slot n8 he0 hv hat hrest hBs hsl hg
  refine ⟨s, hs1, ?_⟩
  intro e hag hes
  have h1 : InFF (fun m => if m < hB then e0 m else e m) v (hoF ns hB slot (n8 : ℤ) a).2 :=
    hs2 (fun m => if m < hB then e0 m else e m) (fun k hk => by simp [hk])
      (by simp [show ¬ slot < hB from by omega, hes])
  refine Lane4.LNKD.frame_ff _ (fun m => if m < hB then e0 m else e m) e v ?_ h1
  intro k hne
  by_cases hk : k < hB
  · have hne' : e k ≠ e0 k := by simpa [hk] using hne
    apply hoF_coeff ns hB slot n8 a pre rest hat hrest k
    · omega
    · intro hc
      exact hne' (hag k hc.1 hc.2)
  · exfalso
    apply hne
    simp [hk]

theorem ho_coord2 (e' : ℕ → ℝ) (he' : ∀ k, |e' k| ≤ 1) (pre : ℕ) (K : List ℕ) (hK4 : K.length ≤ 4)
    (ns hB slot : ℕ) (v : ℝ) (a : AF)
    (hshape : (K.length = 0 ∧ a.t = []) ∨
      ∃ rest, a.t = List.replicate pre 0 ++ rest ∧ rest.length ≤ K.length - 1)
    (hBs : hB ≤ slot) (hsl : slot < ns)
    (hg : (hoF ns hB slot ((K.length - 1 : ℕ) : ℤ) a).1 = true)
    (hv : ∀ e : ℕ → ℝ, Sym e → (∀ k, k < K.length - 1 → e (pre + k) = e' k) → InAF e v a) :
    ∃ s : ℝ, |s| ≤ 1 ∧ ∀ e : ℕ → ℝ, (∀ k, k < K.length - 1 → e (pre + k) = e' k) →
      e slot = s → InFF e v (hoF ns hB slot ((K.length - 1 : ℕ) : ℤ) a).2 := by
  obtain ⟨eb, hebdef⟩ : ∃ eb : ℕ → ℝ, ∀ m, eb m = if pre ≤ m ∧ m < pre + 3 then e' (m - pre) else 0 :=
    ⟨fun m => if pre ≤ m ∧ m < pre + 3 then e' (m - pre) else 0, fun _ => rfl⟩
  have hSym : Sym eb := by
    intro m
    rw [hebdef m]
    by_cases hc : pre ≤ m ∧ m < pre + 3
    · rw [if_pos hc]; exact he' _
    · rw [if_neg hc]; simp
  have hebk : ∀ k, k < K.length - 1 → eb (pre + k) = e' k := by
    intro k hk
    rw [hebdef, if_pos (show pre ≤ pre + k ∧ pre + k < pre + 3 by omega), Nat.add_sub_cancel_left]
  have hvb := hv eb hSym hebk
  rcases hshape with ⟨hK0, hat⟩ | ⟨rest, hat, hrest⟩
  · have hat' : a.t = List.replicate 0 0 ++ ([] : List ℚ) := by simp [hat]
    obtain ⟨s, hs1, hs2⟩ := ho_coord eb hSym v a 0 [] ns hB slot (K.length - 1) hvb hat'
      (by simp) hBs hsl hg
    exact ⟨s, hs1, fun e _ hes => hs2 e (fun k _ hk => absurd hk (by omega)) hes⟩
  · obtain ⟨s, hs1, hs2⟩ := ho_coord eb hSym v a pre rest ns hB slot (K.length - 1) hvb hat hrest
      hBs hsl hg
    refine ⟨s, hs1, fun e hag hes => hs2 e ?_ hes⟩
    intro k hk1 hk2
    have h1 := hag (k - pre) (by omega)
    rw [Nat.add_sub_of_le hk1] at h1
    rw [h1, hebdef k, if_pos (show pre ≤ k ∧ k < pre + 3 by omega)]

theorem headAF_t {δ : ℚ} {h : AHead} {hc : HCert} {d pre q : ℕ} {keys : List ℕ} {o : List AF}
    (hh : headAF δ h hc d pre q keys = some o) :
    ∀ a ∈ o, (keys.length = 0 ∧ a.t = []) ∨
      ∃ rest, a.t = List.replicate pre 0 ++ rest ∧ rest.length ≤ keys.length - 1 := by
  intro a ha
  by_cases hne : keys.length = 0
  · left
    refine ⟨hne, ?_⟩
    unfold headAF at hh
    rw [if_pos hne] at hh
    have h2 := Option.some.inj hh
    rw [← h2] at ha
    obtain ⟨r, _, hra⟩ := List.mem_map.mp ha
    subst hra
    rfl
  · right
    obtain ⟨_, rs, _, ho⟩ := Lane4.LNKC.headAF_open hne hh
    rw [ho] at ha
    obtain ⟨r, _, hra⟩ := List.mem_map.mp ha
    subst hra
    refine ⟨_, Lane4.LNKC.coordAF_t _ _ _ _ _ _ _ _ _, ?_⟩
    rw [List.length_zipWith, List.length_map]
    have href : refRank h hc q keys < keys.length := by
      unfold refRank
      split_ifs
      · have := Lane4.LNKC.argmax_le h hc q keys (keys.length - 1)
        omega
      · omega
    have := Lane4.LNKC.otherRanks_len_le keys.length (refRank h hc q keys) href
    omega

end Lane4.Case
