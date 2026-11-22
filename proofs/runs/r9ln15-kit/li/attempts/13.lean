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
    simp only [List.length_zipWith, List.length_map]
    have href : refRank h hc q keys < keys.length := by
      unfold refRank
      split_ifs
      · have := Lane4.LNKC.argmax_le h hc q keys (keys.length - 1)
        omega
      · omega
    have := Lane4.LNKC.otherRanks_len_le keys.length (refRank h hc q keys) href
    omega

/-! ### opening the checker -/

theorem mem_of_contains'' {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : l.contains a = true) : a ∈ l := Lane4.R8K.mem_of_contains' h

theorem checkLN_open {δ : ℚ} {N : LNNet} {T : Task} {c : CertLN} (h : checkLN δ N T c = true) :
    ∃ B : ABlock, N.net.blocks = [B] ∧ ∀ d : ℕ, (N.net.embed.headD []).length = d →
      0 ≤ δ ∧ δ ≤ 1 / 2 ∧ N.net.shapeOK T.ntok = true ∧ weightsOK N.net B = true ∧
      lnWeightsOK δ N B d = true ∧ B.heads.length ≤ 2 ∧ 1 ≤ d ∧ c.W = intW N B ∧
      allSomeL (c.W.E.map (ln1Box (floorQ δ) (slots B d) c.W)) = some c.boxes ∧
      c.boxes.all (boxOK d) = true ∧ c.heads.length = B.heads.length ∧
      (List.zipWith (fun h hc => headOKLN δ c.boxes h hc) B.heads c.heads).all id = true ∧
      (∀ st ∈ c.states, st.2.length = B.heads.length) ∧
      (T.init, c.heads.map (fun hc => if hc.cands.getD 0 false = true then [0] else [])) ∈ c.states ∧
      (∀ st ∈ c.states, ∀ t, 1 ≤ t → t ≤ T.ntok → caseOKLN δ (floorQ δ) B T c d st t = true) := by
  unfold checkLN at h
  split at h
  · rename_i B hB
    refine ⟨B, hB, ?_⟩
    intro d hd
    subst hd
    try dsimp only at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ?_, mem_of_contains'' h14, ?_⟩
    · intro st hst
      exact beq_iff_eq.mp (List.all_eq_true.mp h13 st hst)
    · intro st hst t ht1 ht2
      have h' : caseOKLN δ (floorQ δ) B T c (N.net.embed.headD []).length st (t - 1 + 1) = true :=
        List.all_eq_true.mp (List.all_eq_true.mp h15 st hst) (t - 1) (List.mem_range.mpr (by omega))
      have e : t - 1 + 1 = t := by omega
      rw [e] at h'
      exact h'
  · simp at h

theorem caseOKLN_facts {δ : ℚ} {dI : ℤ} {B : ABlock} {T : Task} {c : CertLN} {d : ℕ}
    {st : ℕ × List (List ℕ)} {t : ℕ} (h : caseOKLN δ dI B T c d st t = true) :
    ∃ o : FF, outLN δ dI B c d t st.2 = some o ∧
      4 * (iabs (o.c - (T.out st.1 t : ℤ) * SC) + o.dev) ≤ SC ∧
      absStep8 T c.heads st t ∈ c.states := by
  unfold caseOKLN at h
  split at h
  · simp at h
  · rename_i o ho
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨o, ho, h.1, mem_of_contains'' h.2⟩

theorem headOKLN_facts {δ : ℚ} {E : List (List IV)} {hd : AHead} {hc : HCert}
    (h : headOKLN δ E hd hc = true) : hd.mask ≠ Mask.all ∧ 1 ≤ hc.L := by
  unfold headOKLN at h
  simp only [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1.1.1.1.1.1.1.1.1.1.1.1.1, of_decide_eq_true h.1.1.2⟩

theorem lnWeights_facts {δ : ℚ} {N : LNNet} {B : ABlock} {d : ℕ} (h : lnWeightsOK δ N B d = true) :
    gridOK δ = true ∧ gridM N.net.embed = true ∧ gridM B.W1 = true ∧ gridL B.b1 = true ∧
    gridM B.W2 = true ∧ gridL B.b2 = true ∧ gridL N.net.outW = true ∧ gridOK N.net.outB = true ∧
    (∀ l ∈ [N.g1, N.b1, N.g2, N.b2, N.gf, N.bf],
      gridL l = true ∧ smallQ l = true ∧ l.length = d) := by
  unfold lnWeightsOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  intro l hl
  have := List.all_eq_true.mp h9 l hl
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-! ### the body of `outLN` with the slot numbers as variables -/

def outBody (δ : ℚ) (dI : ℤ) (B : ABlock) (c : CertLN) (d : ℕ) (t : ℕ) (wins : List (List ℕ))
    (ns hB lB wB vB : ℕ) : Option FF :=
  match headsF δ d ns hB t B.heads c.heads wins 0 (resF dI ns (c.W.E.getD t []) 0) with
  | none => none
  | some y =>
    if y.all (zeroFrom lB) then
      match lnF dI ns c.W.g2 c.W.b2 (some lB) y with
      | none => none
      | some y2 =>
        match affF dI ns wB c.W.W1 c.W.c1 y2 with
        | none => none
        | some a1 =>
          if (a1.map reluF).all FF.small then
          match affF dI ns vB c.W.W2 c.W.c2 (a1.map reluF) with
          | none => none
          | some a2 =>
            match splitOK (List.zipWith (fun a b => addOne a (true, b)) y a2) with
            | none => none
            | some z =>
              match lnF dI ns c.W.gf c.W.bf none z with
              | none => none
              | some zf =>
                splitOK1 (dotF dI ns none none c.W.oW zf (zf.map FF.mag) (sumI (zf.map FF.dev))
                           (sumI (zf.map (fun x => iabs x.c))) c.W.oB)
          else none
    else none

theorem outLN_eq (δ : ℚ) (dI : ℤ) (B : ABlock) (c : CertLN) (d t : ℕ) (wins : List (List ℕ)) :
    outLN δ dI B c d t wins =
      outBody δ dI B c d t wins
        (d + 3 * B.heads.length + B.heads.length * d + d + c.W.c1.length + d)
        (d + 3 * B.heads.length) (d + 3 * B.heads.length + B.heads.length * d)
        (d + 3 * B.heads.length + B.heads.length * d + d)
        (d + 3 * B.heads.length + B.heads.length * d + d + c.W.c1.length) := rfl

theorem outBody_open {δ : ℚ} {dI : ℤ} {B : ABlock} {c : CertLN} {d t : ℕ} {wins : List (List ℕ)}
    {ns hB lB wB vB : ℕ} {o : FF} (h : outBody δ dI B c d t wins ns hB lB wB vB = some o) :
    ∃ y y2 a1 a2 z zf : List FF,
      headsF δ d ns hB t B.heads c.heads wins 0 (resF dI ns (c.W.E.getD t []) 0) = some y ∧
      lnF dI ns c.W.g2 c.W.b2 (some lB) y = some y2 ∧
      affF dI ns wB c.W.W1 c.W.c1 y2 = some a1 ∧
      (a1.map reluF).all FF.small = true ∧
      affF dI ns vB c.W.W2 c.W.c2 (a1.map reluF) = some a2 ∧
      splitOK (List.zipWith (fun a b => addOne a (true, b)) y a2) = some z ∧
      lnF dI ns c.W.gf c.W.bf none z = some zf ∧
      splitOK1 (dotF dI ns none none c.W.oW zf (zf.map FF.mag) (sumI (zf.map FF.dev))
                 (sumI (zf.map (fun x => iabs x.c))) c.W.oB) = some o := by
  unfold outBody at h
  cases hy : headsF δ d ns hB t B.heads c.heads wins 0 (resF dI ns (c.W.E.getD t []) 0) with
  | none => rw [hy] at h; simp at h
  | some y =>
    simp only [hy] at h
    by_cases h0 : y.all (zeroFrom lB) = true
    · rw [if_pos h0] at h
      cases hy2 : lnF dI ns c.W.g2 c.W.b2 (some lB) y with
      | none => simp [hy2] at h
      | some y2 =>
        simp only [hy2] at h
        cases ha1 : affF dI ns wB c.W.W1 c.W.c1 y2 with
        | none => simp [ha1] at h
        | some a1 =>
          simp only [ha1] at h
          by_cases h1 : (a1.map reluF).all FF.small = true
          · rw [if_pos h1] at h
            cases ha2 : affF dI ns vB c.W.W2 c.W.c2 (a1.map reluF) with
            | none => simp [ha2] at h
            | some a2 =>
              simp only [ha2] at h
              cases hz : splitOK (List.zipWith (fun a b => addOne a (true, b)) y a2) with
              | none => simp [hz] at h
              | some z =>
                simp only [hz] at h
                cases hzf : lnF dI ns c.W.gf c.W.bf none z with
                | none => simp [hzf] at h
                | some zf =>
                  simp only [hzf] at h
                  exact ⟨y, y2, a1, a2, z, zf, (by first | exact hy | rfl), (by first | exact hy2 | rfl), (by first | exact ha1 | rfl), h1, (by first | exact ha2 | rfl), (by first | exact hz | rfl), (by first | exact hzf | rfl), h⟩
          · rw [if_neg h1] at h; simp at h
    · rw [if_neg h0] at h; simp at h

/-! ### LN1: the box of every token row -/

theorem ln1_box_tok {u η M : ℝ} {fl sq : ℝ → ℝ} (hC : Ctx u η M fl) (hS : SqrtM u η sq)
    {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hgδ : gridOK δ = true)
    (N : LNNet) (B : ABlock) (c : CertLN) (d ns : ℕ) (hns : ns ≤ 1024) (hdns : d ≤ ns)
    (hd1 : 1 ≤ d) (hd24 : d ≤ 24)
    (hW : c.W = intW N B)
    (hbox : allSomeL (c.W.E.map (ln1Box (floorQ δ) ns c.W)) = some c.boxes)
    (hembrow : ∀ r ∈ N.net.embed, r.length = d ∧ smallQ r = true ∧ gridL r = true)
    (hg1 : gridL N.g1 = true ∧ smallQ N.g1 = true ∧ N.g1.length = d)
    (hb1 : gridL N.b1 = true ∧ smallQ N.b1 = true ∧ N.b1.length = d)
    (lp : LPert) (hp : lp.Within (δ : ℝ)) (tk : ℕ) (htk : tk < N.net.embed.length) :
    tk < c.boxes.length ∧
    InIVs (lnorm fl sq N.g1 N.b1 lp.g1 lp.b1 (aswRow fl (N.net.embed.getD tk []) (lp.a.E tk) 0))
      (c.boxes.getD tk []) := by
  have hE : c.W.E = N.net.embed.map intL := by rw [hW]; rfl
  have hG1 : c.W.g1 = intL N.g1 := by rw [hW]; rfl
  have hB1 : c.W.b1 = intL N.b1 := by rw [hW]; rfl
  rw [hE] at hbox
  obtain ⟨hlen, hget⟩ := allSomeL_spec ([] : List IV) _ _ hbox
  rw [List.length_map, List.length_map] at hlen
  have hlt : tk < (N.net.embed.map intL).length := by rw [List.length_map]; exact htk
  have hlt2 : tk < ((N.net.embed.map intL).map (ln1Box (floorQ δ) ns c.W)).length := by
    rw [List.length_map]; exact hlt
  have hg := hget tk hlt2
  rw [getD_map_lt (ln1Box (floorQ δ) ns c.W) ([] : List ℤ) none (N.net.embed.map intL) tk hlt,
    getD_map_lt intL ([] : List ℚ) ([] : List ℤ) N.net.embed tk htk] at hg
  obtain ⟨hrl, hrs, hrg⟩ := hembrow _ (zgetD_mem' ([] : List ℚ) N.net.embed tk htk)
  generalize N.net.embed.getD tk [] = row at hg hrl hrs hrg ⊢
  refine ⟨by rw [hlen]; exact htk, ?_⟩
  obtain ⟨hg1a, hg1b, hg1c⟩ := hg1
  obtain ⟨hb1a, hb1b, hb1c⟩ := hb1
  unfold ln1Box at hg
  cases hY : lnF (floorQ δ) ns c.W.g1 c.W.b1 none (resF (floorQ δ) ns (intL row) 0) with
  | none => rw [hY] at hg; simp at hg
  | some Y =>
    rw [hY] at hg
    have hY' : Y.map boxOf = c.boxes.getD tk [] := Option.some.inj hg
    rw [hG1, hB1] at hY
    obtain ⟨e0, he0, hrep, hsh, _⟩ := Lane4.LNKD.res_f_sound u η M fl hC δ hδ0 hδ1 hgδ ns row
      (lp.a.E tk) (fun k => hp.a.E tk k) hrs hrg (by omega)
    have hX0 := hrep e0 (fun _ _ => rfl)
    have hxl : (aswRow fl row (lp.a.E tk) 0).length = d := by
      rw [Lane4.LNKD.aswRow_length]; exact hrl
    obtain ⟨_, hnone, _⟩ := Lane4.LNKH.ln_f_sound u η M fl sq hC hS δ hδ0 hδ1 hgδ ns N.g1 N.b1
      lp.g1 lp.b1 (aswRow fl row (lp.a.E tk) 0) (resF (floorQ δ) ns (intL row) 0) Y e0 he0
      hp.g1 hp.b1 (by omega) (by omega) (by omega) (by omega) hg1b hb1b hg1a hb1a hX0 hsh
      hns none hY
    have hIn := hnone rfl
    rw [← hY']
    unfold InIVs
    refine ⟨?_, ?_⟩
    · rw [List.length_map]; exact hIn.1
    · intro k hk
      have hkY : k < Y.length := by rw [← hIn.1]; exact hk
      rw [getD_map_lt boxOf (zeroF 0) (0, 0) Y k hkY]
      exact (Lane4.LNKD.box_sound e0 _ _ he0 (hIn.2 k hk)).1

/-! ### one step of the residual stream -/

theorem addOne_t_length (a : FF) (h : Bool × FF) (n : ℕ) (ha : a.t.length = n)
    (hh : h.2.t.length = n) : (addOne a h).2.t.length = n := by
  show (List.zipWith (fun x y => x + y) a.t h.2.t).length = n
  rw [List.length_zipWith, ha, hh]
  simp

theorem add_step {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (ns hB slot0 : ℕ) (n8 : ℤ)
    (e : ℕ → ℝ) (he : Sym e) (acc : List FF) (ho : List AF) (accR attR : List ℝ)
    (acc' : List FF) (d : ℕ)
    (hsp : splitOK (addHO ns hB slot0 n8 acc ho 0) = some acc')
    (hlacc : acc.length = d) (hlho : ho.length = d) (hlaR : attR.length = d)
    (hsh : Shaped ns acc) (hacc : InFFs e accR acc)
    (hho : ∀ j, j < d →
      InFF e (attR.getD j 0) (hoF ns hB (slot0 + j) n8 (ho.getD j ⟨0, [], 0⟩)).2) :
    InFFs e (radd fl accR attR) acc' ∧ Shaped ns acc' ∧ acc'.length = d := by
  obtain ⟨hlen, hget⟩ := splitOK_get hsp
  rw [addHO_len] at hlen
  have hlen' : acc'.length = d := by rw [hlen, hlacc, hlho, min_self]
  have haccR : accR.length = d := by rw [hacc.1, hlacc]
  have hidx : ∀ j, j < d →
      (hoF ns hB (slot0 + j) n8 (ho.getD j ⟨0, [], 0⟩)).1 = true ∧
      acc'.getD j (zeroF 0) =
        (addOne (acc.getD j (zeroF 0)) (hoF ns hB (slot0 + j) n8 (ho.getD j ⟨0, [], 0⟩))).2 ∧
      (addOne (acc.getD j (zeroF 0)) (hoF ns hB (slot0 + j) n8 (ho.getD j ⟨0, [], 0⟩))).2.mag
        ≤ 15 * SC := by
    intro j hj
    have hjl : j < (addHO ns hB slot0 n8 acc ho 0).length := by
      rw [addHO_len]; omega
    obtain ⟨hg1, hg2⟩ := hget j hjl
    rw [addHO_get ns hB slot0 n8 acc ho 0 j (by omega) (by omega), Nat.add_zero] at hg1 hg2
    obtain ⟨hgo, hmg⟩ := addOne_facts _ _ hg1
    exact ⟨hgo, hg2, hmg⟩
  refine ⟨?_, ?_, hlen'⟩
  · unfold InFFs
    refine ⟨by rw [radd_length, haccR, hlaR, hlen', min_self], ?_⟩
    intro j hj
    have hj' : j < d := by rw [radd_length, haccR, hlaR, min_self] at hj; exact hj
    obtain ⟨hgo, hv, hmg⟩ := hidx j hj'
    rw [hv, radd_getD fl accR attR j (by omega) (by omega)]
    have hax : acc.getD j (zeroF 0) ∈ acc := zgetD_mem' (zeroF 0) acc j (by omega)
    have hbt := hoF_len ns hB (slot0 + j) n8 _ hgo
    exact add_sound3 hC e _ _ _ _ he (hacc.2 j (by omega)) (hho j hj')
      (by rw [(hsh _ hax).1, hbt]) hmg
  · intro a ha
    obtain ⟨j, hj, hja⟩ := mem_idx (zeroF 0) acc' a ha
    have hj' : j < d := by omega
    obtain ⟨hgo, hv, hmg⟩ := hidx j hj'
    rw [← hja, hv]
    have hax := hsh _ (zgetD_mem' (zeroF 0) acc j (by omega))
    have hbt := hoF_len ns hB (slot0 + j) n8 _ hgo
    exact ⟨addOne_t_length _ _ ns hax.1 hbt, by have := SC_pos; omega⟩

theorem zadd_step {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (ns : ℕ) (e : ℕ → ℝ) (he : Sym e)
    (y a2 : List FF) (yR a2R : List ℝ) (z : List FF) (d : ℕ)
    (hsp : splitOK (List.zipWith (fun a b => addOne a (true, b)) y a2) = some z)
    (hly : y.length = d) (hla2 : a2.length = d)
    (hys : Shaped ns y) (ha2s : ∀ b ∈ a2, b.t.length = ns)
    (hy : InFFs e yR y) (ha2 : InFFs e a2R a2) (ha2R : a2R.length = d) :
    InFFs e (radd fl yR a2R) z ∧ Shaped ns z ∧ z.length = d := by
  obtain ⟨hlen, hget⟩ := splitOK_get hsp
  rw [List.length_zipWith, hly, hla2, min_self] at hlen
  have hyR : yR.length = d := by rw [hy.1, hly]
  have hidx : ∀ j, j < d →
      (addOne (y.getD j (zeroF 0)) (true, a2.getD j (zeroF 0))).2.mag ≤ 15 * SC ∧
      z.getD j (zeroF 0) = (addOne (y.getD j (zeroF 0)) (true, a2.getD j (zeroF 0))).2 := by
    intro j hj
    have hjl : j < (List.zipWith (fun a b => addOne a (true, b)) y a2).length := by
      rw [List.length_zipWith, hly, hla2, min_self]; exact hj
    obtain ⟨hg1, hg2⟩ := hget j hjl
    rw [Lane4.LNKC.gd_zipWith (fun a b => addOne a (true, b)) (zeroF 0) (zeroF 0) (false, zeroF 0)
      y a2 j (by omega) (by omega)] at hg1 hg2
    exact ⟨(addOne_facts _ _ hg1).2, hg2⟩
  refine ⟨?_, ?_, hlen⟩
  · unfold InFFs
    refine ⟨by rw [radd_length, hyR, ha2R, hlen, min_self], ?_⟩
    intro j hj
    have hj' : j < d := by rw [radd_length, hyR, ha2R, min_self] at hj; exact hj
    obtain ⟨hmg, hv⟩ := hidx j hj'
    rw [hv, radd_getD fl yR a2R j (by omega) (by omega)]
    have hax := hys _ (zgetD_mem' (zeroF 0) y j (by omega))
    have hbx := ha2s _ (zgetD_mem' (zeroF 0) a2 j (by omega))
    exact add_sound3 hC e _ _ _ _ he (hy.2 j (by omega)) (ha2.2 j (by omega))
      (by rw [hax.1, hbx]) hmg
  · intro a ha
    obtain ⟨j, hj, hja⟩ := mem_idx (zeroF 0) z a ha
    have hj' : j < d := by omega
    obtain ⟨hmg, hv⟩ := hidx j hj'
    rw [← hja, hv]
    have hax := hys _ (zgetD_mem' (zeroF 0) y j (by omega))
    have hbx := ha2s _ (zgetD_mem' (zeroF 0) a2 j (by omega))
    exact ⟨addOne_t_length _ _ ns hax.1 hbx, by have := SC_pos; omega⟩

/-! ### stored rows with symbols, ReLU -/

theorem intL_getD (bs : List ℚ) (j : ℕ) (hj : j < bs.length) :
    (intL bs).getD j 0 = floorQ (bs.getD j 0) :=
  getD_map_lt floorQ 0 0 bs j hj

theorem mapintL_getD (Mr : List (List ℚ)) (j : ℕ) (hj : j < Mr.length) :
    (Mr.map intL).getD j [] = intL (Mr.getD j []) :=
  getD_map_lt intL [] [] Mr j hj

theorem aff_step {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (hgδ : gridOK δ = true) (ns slot0 : ℕ) (Mr : List (List ℚ)) (bs : List ℚ)
    (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (x : List ℝ) (X : List FF) (e : ℕ → ℝ) (he : Sym e)
    (hdW : ∀ i k, |dW i k| ≤ (δ : ℝ)) (hdb : ∀ i, |db i| ≤ (δ : ℝ))
    (hrows : ∀ r ∈ Mr, r.length = x.length ∧ r.length ≤ 32 ∧ smallQ r = true ∧ gridL r = true)
    (hbs : ∀ b ∈ bs, smallQ [b] = true ∧ gridOK b = true)
    (hlen : Mr.length = bs.length) (hslot : slot0 + Mr.length ≤ ns)
    (hX : InFFs e x X) (hXs : Shaped ns X)
    (A : List FF) (hA : affF (floorQ δ) ns slot0 (Mr.map intL) (intL bs) X = some A) :
    A.length = Mr.length ∧ (∀ a ∈ A, a.t.length = ns ∧ a.mag ≤ 15 * SC) ∧
    ∃ v : ℕ → ℝ, (∀ j, j < Mr.length → |v j| ≤ 1) ∧
      ∀ e' : ℕ → ℝ, AgreeBelow slot0 e e' → (∀ j, j < Mr.length → e' (slot0 + j) = v j) →
        InFFs e' (araffine fl Mr bs x dW db 0) A := by
  unfold affF at hA
  obtain ⟨hAlen, hAget⟩ := splitOK_get hA
  have hbl : (intL bs).length = bs.length := by simp [intL]
  rw [dotRows_len, List.length_map, hbl, ← hlen, min_self] at hAlen
  have hrow : ∀ j, j < Mr.length →
      (dotF (floorQ δ) ns (some slot0) (some (slot0 + j)) (intL (Mr.getD j [])) X
        (X.map FF.mag) (sumI (X.map FF.dev)) (sumI (X.map (fun a => iabs a.c)))
        (floorQ (bs.getD j 0))).1 = true ∧
      A.getD j (zeroF 0) =
      (dotF (floorQ δ) ns (some slot0) (some (slot0 + j)) (intL (Mr.getD j [])) X
        (X.map FF.mag) (sumI (X.map FF.dev)) (sumI (X.map (fun a => iabs a.c)))
        (floorQ (bs.getD j 0))).2 := by
    intro j hj
    have hjl : j < (dotRows (floorQ δ) ns slot0 X (X.map FF.mag) (sumI (X.map FF.dev))
        (sumI (X.map (fun a => iabs a.c))) (Mr.map intL) (intL bs) slot0).length := by
      rw [dotRows_len, List.length_map, hbl, ← hlen, min_self]; exact hj
    obtain ⟨hg1, hg2⟩ := hAget j hjl
    rw [dotRows_get (floorQ δ) ns slot0 X (X.map FF.mag) (sumI (X.map FF.dev))
      (sumI (X.map (fun a => iabs a.c))) (Mr.map intL) (intL bs) slot0 j (by simpa using hj)
      (by rw [hbl]; omega),
      mapintL_getD Mr j hj, intL_getD bs j (by omega)] at hg1 hg2
    exact ⟨hg1, hg2⟩
  have hdot : ∀ j, j < Mr.length → ∃ v : ℝ, |v| ≤ 1 ∧
      (A.getD j (zeroF 0)).t.length = ns ∧ (A.getD j (zeroF 0)).mag ≤ 15 * SC ∧
      ∀ e' : ℕ → ℝ, AgreeBelow slot0 e e' → e' (slot0 + j) = v →
        InFF e' (fl (ardot fl (Mr.getD j []) x (dW j) 0 0 + asw fl (bs.getD j 0) (db j)))
          (A.getD j (zeroF 0)) := by
    intro j hj
    obtain ⟨hg, hv⟩ := hrow j hj
    obtain ⟨hr1, hr2, hr3, hr4⟩ := hrows _ (zgetD_mem' ([] : List ℚ) Mr j hj)
    obtain ⟨hb1, hb2⟩ := hbs _ (zgetD_mem' (0 : ℚ) bs j (by omega))
    obtain ⟨hl1, hl2, hl3, hl4⟩ := Lane4.LNKE.dot_f_sound u η M fl hC δ hδ0 hδ1 hgδ ns
      (Mr.getD j []) (bs.getD j 0) x X (dW j) (db j) e he (hdW j) (hdb j) hr1 hr2 hr3 hb1 hr4
      hb2 hX hXs (some slot0) (some (slot0 + j)) hg
    obtain ⟨v, hv1, hv2⟩ := hl4 slot0 (slot0 + j) rfl rfl (by omega) (by omega)
    refine ⟨v, hv1, ?_, ?_, ?_⟩
    · rw [hv]; exact hl1
    · rw [hv]; exact hl2
    · intro e' hag hes
      rw [hv]
      exact hv2 e' hag hes
  choose! v hv1 hv2 hv3 hv4 using hdot
  refine ⟨hAlen, ?_, v, hv1, ?_⟩
  · intro a ha
    obtain ⟨j, hj, hja⟩ := mem_idx (zeroF 0) A a ha
    rw [← hja]
    exact ⟨hv2 j (by omega), hv3 j (by omega)⟩
  · intro e' hag hes
    have hlA : (araffine fl Mr bs x dW db 0).length = A.length := by
      rw [araffine_length, ← hlen, min_self, hAlen]
    unfold InFFs
    refine ⟨hlA, ?_⟩
    intro j hj
    rw [hlA] at hj
    have hjM : j < Mr.length := by omega
    rw [araffine_get fl x dW db Mr bs 0 j hjM (by omega)]
    simp only [Nat.zero_add]
    exact hv4 j hjM e' hag (hes j hjM)

theorem relu_inffs (e : ℕ → ℝ) (he : Sym e) (v : List ℝ) (A : List FF) (h : InFFs e v A) :
    InFFs e (v.map Lane4.relu) (A.map reluF) := by
  unfold InFFs
  refine ⟨by rw [List.length_map, List.length_map]; exact h.1, ?_⟩
  intro j hj
  rw [List.length_map] at hj
  have hjA : j < A.length := by rw [← h.1]; exact hj
  rw [getD_map_lt Lane4.relu (0 : ℝ) (0 : ℝ) v j hj, getD_map_lt reluF (zeroF 0) (zeroF 0) A j hjA]
  exact (Lane4.LNKD.relu_f_sound e _ _ he (h.2 j hj)).1

theorem relu_shaped (e : ℕ → ℝ) (he : Sym e) (ns : ℕ) (v : List ℝ) (A : List FF)
    (h : InFFs e v A) (hs : ∀ a ∈ A, a.t.length = ns)
    (hsm : (A.map reluF).all FF.small = true) : Shaped ns (A.map reluF) := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := List.mem_map.mp hb
  subst hab
  obtain ⟨j, hj, hja⟩ := mem_idx (zeroF 0) A a ha
  have hjv : j < v.length := by rw [h.1]; exact hj
  have hin := h.2 j hjv
  rw [hja] at hin
  have hl := (Lane4.LNKD.relu_f_sound e _ _ he hin).2
  refine ⟨by rw [hl]; exact hs a ha, ?_⟩
  have h1 := List.all_eq_true.mp hsm (reluF a) hb
  unfold FF.small at h1
  have h2 := of_decide_eq_true h1
  have := SC_pos
  omega


/-! ### the heads -/

def GoodHL (δ : ℚ) (E : List (List IV)) (w : List ℕ) (i d : ℕ) (hd : AHead) (hc : HCert)
    (win : List ℕ) : Prop :=
  headOKLN δ E hd hc = true ∧ hd.shapeOK d = true ∧ smallM hd.A = true ∧ smallM hd.V = true ∧
  smallQ hd.g = true ∧ smallQ [hd.gb] = true ∧
  ∃ P : List ℕ, WinPos hd.mask hc.cands (tokAt w) (w.length + 1) i P ∧
    P.map (tokAt w) = keysAt hd hc (tokAt w i) win ∧
    P.length ≤ fullLen hd hc (tokAt w i) ∧
    (P.length < fullLen hd hc (tokAt w i) →
      ∀ k ∈ cand hd.mask (w.length + 1) i, hc.cands.getD (tokAt w k) false = true → k ∈ P)

theorem heads_ind_ln {u η M : ℝ} {fl ex : ℝ → ℝ} (hC : Ctx u η M fl) (hX : ExpM u η ex)
    {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (E : List (List IV)) (p : APert)
    (hp : p.Within (δ : ℝ)) (w : List ℕ) (x : ℕ → Vec) (i d : ℕ) (hd24 : d ≤ 24)
    (hrows : ∀ row ∈ E, row.length = d ∧ Bdd 16 row)
    (hu : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100)
    (hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M)
    (hxE : ∀ j, j < w.length + 1 → tokAt w j < E.length ∧ InIVs (x j) (E.getD (tokAt w j) []))
    (hi : i < w.length + 1) (hti : 1 ≤ tokAt w i) (ns hB : ℕ) :
    ∀ (hs : List AHead) (hcs : List HCert) (wins : List (List ℕ)) (k : ℕ)
      (acc : List FF) (accR : List ℝ) (y : List FF),
      hcs.length = hs.length → wins.length = hs.length → acc.length = d →
      hB = d + 3 * (k + hs.length) → hB + (k + hs.length) * d ≤ ns → Shaped ns acc →
      (∃ g : ℕ → ℝ, (∀ m, |g m| ≤ 1) ∧
        ∀ e : ℕ → ℝ, Sym e → (∀ m, (m < d + 3 * k ∨ (hB ≤ m ∧ m < hB + k * d)) → e m = g m) →
          InFFs e accR acc) →
      (∀ j, j < hs.length → GoodHL δ E w i d (hs.getD j Lane4.R8K.dfltHead)
        (hcs.getD j Lane4.R8K.dfltHC) (wins.getD j [])) →
      headsF δ d ns hB (tokAt w i) hs hcs wins k acc = some y →
      ∃ g : ℕ → ℝ, (∀ m, |g m| ≤ 1) ∧
        (∀ e : ℕ → ℝ, Sym e → (∀ m, m < hB + (k + hs.length) * d → e m = g m) →
          InFFs e (aheadsApply fl ex p 0 (w.length + 1) x i hs accR k) y) ∧
        Shaped ns y ∧ y.length = d := by
  intro hs
  induction hs with
  | nil =>
    intro hcs wins k acc accR y hl1 hl2 hlen hBk hsz hsh hinv hgood hrun
    have e1 : headsF δ d ns hB (tokAt w i) [] hcs wins k acc = some acc := by
      cases hcs <;> cases wins <;> rfl
    rw [e1] at hrun
    have hy : acc = y := Option.some.inj hrun
    subst hy
    obtain ⟨g, hg1, hg2⟩ := hinv
    refine ⟨g, hg1, ?_, hsh, hlen⟩
    intro e he hag
    simp only [List.length_nil, Nat.add_zero] at hBk hag
    exact hg2 e he (fun m hm => hag m (by omega))
  | cons hd hs ih =>
    intro hcs wins k acc accR y hl1 hl2 hlen hBk hsz hsh hinv hgood hrun
    cases hcs with
    | nil => simp at hl1
    | cons hc hcs =>
    cases wins with
    | nil => simp at hl2
    | cons win wins =>
    simp only [List.length_cons] at hBk hsz hl1 hl2
    have g0 := hgood 0 (Nat.succ_pos _)
    simp only [List.getD_cons_zero] at g0
    obtain ⟨hOK, hsh1, wA, wV, wg, wgb, P, hWin, hPmap, hPle, hPfull⟩ := g0
    simp only [headsF] at hrun
    simp only [aheadsApply]
    generalize hK : keysAt hd hc (tokAt w i) win = K at hrun hPmap
    by_cases hguard : K.length ≤ 4 ∧
        acc.all (fun a => zeroRange (d + 3 * k) (d + 3 * k + 3) a && zeroFrom (hB + k * d) a) = true
    · rw [if_pos hguard] at hrun
      obtain ⟨hK4, _⟩ := hguard
      cases hha : headAF δ hd hc d (d + 3 * k) (tokAt w i) K with
      | none => simp [hha] at hrun
      | some ho =>
        simp only [hha] at hrun
        cases hsp : splitOK (addHO ns hB (hB + k * d) ((K.length - 1 : ℕ) : ℤ) acc ho 0) with
        | none => simp [hsp] at hrun
        | some acc' =>
          simp only [hsp] at hrun
          have hpk : K.length = P.length := by rw [← hPmap]; simp
          have hha' : headAF δ hd hc d (d + 3 * k) (tokAt w i) (P.map (tokAt w)) = some ho := by
            rw [hPmap]; exact hha
          obtain ⟨e', he'1, he'2⟩ := Lane4.LNKC.head_sound_ln u η M fl ex hC hX δ hδ0 hδ1 hd E hc d
            hOK hsh1 hd24 wA wV wg wgb hrows
            (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k) (p.gb 0 k)
            (hp.A 0 k) (hp.V 0 k) (hp.m 0 k) (hp.g 0 k) (hp.gb 0 k)
            (w.length + 1) x (tokAt w) hu hη hM hxE i hi hti P (d + 3 * k) hWin hPle hPfull ho hha'
          have hattn : (hd.attn fl ex (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k) (p.gb 0 k)
              (w.length + 1) x i).length = d := by
            have h1 : (hd.attn fl ex (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k) (p.gb 0 k)
                (w.length + 1) x i).length = hd.V.length :=
              Lane4.R8K.aattnRows_length fl ex _ _ _ _ _ _
            rw [h1]
            exact (Lane4.R8K.head_shape hsh1).2
          generalize hattR : hd.attn fl ex (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k) (p.gb 0 k)
            (w.length + 1) x i = attR at he'2 hattn ⊢
          have he'2' : ∀ e : ℕ → ℝ, (∀ k', k' < K.length - 1 → e (d + 3 * k + k') = e' k') →
              InAFs e attR ho := by
            intro e hag
            exact he'2 e (fun k' hk' => hag k' (by rw [hpk]; exact hk'))
          obtain ⟨ebase, hebase⟩ : ∃ eb : ℕ → ℝ, ∀ k', k' < K.length - 1 →
              eb (d + 3 * k + k') = e' k' :=
            ⟨fun m => if d + 3 * k ≤ m then e' (m - (d + 3 * k)) else 0, fun k' hk' => by simp⟩
          have hho0 := he'2' ebase hebase
          have hholen : ho.length = d := by rw [← hho0.1]; exact hattn
          have hBpre : d + 3 * k + 3 ≤ hB := by omega
          have hmul1 : (k + (hs.length + 1)) * d = k * d + (hs.length + 1) * d := by ring
          have hmul2 : (hs.length + 1) * d = hs.length * d + d := by ring
          have hsz1 : hB + k * d + d ≤ ns := by omega
          have hguard_j : ∀ j, j < d →
              (hoF ns hB (hB + k * d + j) ((K.length - 1 : ℕ) : ℤ) (ho.getD j ⟨0, [], 0⟩)).1
                = true := by
            intro j hj
            obtain ⟨hlen0, hget0⟩ := splitOK_get hsp
            have hjl : j < (addHO ns hB (hB + k * d) ((K.length - 1 : ℕ) : ℤ) acc ho 0).length := by
              rw [addHO_len]; omega
            obtain ⟨hg1, _⟩ := hget0 j hjl
            rw [addHO_get ns hB (hB + k * d) ((K.length - 1 : ℕ) : ℤ) acc ho 0 j (by omega)
              (by omega), Nat.add_zero] at hg1
            exact (addOne_facts _ _ hg1).1
          have hcoord : ∀ j, j < d → ∃ s : ℝ, |s| ≤ 1 ∧ ∀ e : ℕ → ℝ,
              (∀ k', k' < K.length - 1 → e (d + 3 * k + k') = e' k') →
              e (hB + k * d + j) = s →
              InFF e (attR.getD j 0)
                (hoF ns hB (hB + k * d + j) ((K.length - 1 : ℕ) : ℤ) (ho.getD j ⟨0, [], 0⟩)).2 := by
            intro j hj
            exact ho_coord2 e' he'1 (d + 3 * k) K hK4 ns hB (hB + k * d + j) (attR.getD j 0)
              (ho.getD j ⟨0, [], 0⟩) (headAF_t hha _ (zgetD_mem' _ ho j (by omega)))
              (by omega) (by omega) (hguard_j j hj) (fun e _ hag => (he'2' e hag).2 j (by omega))
          choose! s hs1 hs2 using hcoord
          obtain ⟨g, hg1, hg2⟩ := hinv
          obtain ⟨g', hg'def⟩ : ∃ g' : ℕ → ℝ, ∀ m, g' m =
              if m < d + 3 * k then g m
              else if m < d + 3 * k + 3 then e' (m - (d + 3 * k))
              else if m < hB then 0
              else if m < hB + k * d then g m
              else if m < hB + k * d + d then s (m - (hB + k * d))
              else 0 :=
            ⟨fun m => if m < d + 3 * k then g m
              else if m < d + 3 * k + 3 then e' (m - (d + 3 * k))
              else if m < hB then 0
              else if m < hB + k * d then g m
              else if m < hB + k * d + d then s (m - (hB + k * d))
              else 0, fun _ => rfl⟩
          have hg'1 : ∀ m, |g' m| ≤ 1 := by
            intro m
            rw [hg'def m]
            by_cases h1 : m < d + 3 * k
            · rw [if_pos h1]; exact hg1 m
            · rw [if_neg h1]
              by_cases h2 : m < d + 3 * k + 3
              · rw [if_pos h2]; exact he'1 _
              · rw [if_neg h2]
                by_cases h3 : m < hB
                · rw [if_pos h3]; simp
                · rw [if_neg h3]
                  by_cases h4 : m < hB + k * d
                  · rw [if_pos h4]; exact hg1 m
                  · rw [if_neg h4]
                    by_cases h5 : m < hB + k * d + d
                    · rw [if_pos h5]; exact hs1 _ (by omega)
                    · rw [if_neg h5]; simp
          have hg'_lo : ∀ m, m < d + 3 * k → g' m = g m := by
            intro m hm
            rw [hg'def m]
            split_ifs <;> first | (exfalso; omega) | rfl
          have hg'_att : ∀ m, d + 3 * k ≤ m → m < d + 3 * k + 3 → g' m = e' (m - (d + 3 * k)) := by
            intro m h1 h2
            rw [hg'def m]
            split_ifs <;> first | (exfalso; omega) | rfl
          have hg'_old : ∀ m, hB ≤ m → m < hB + k * d → g' m = g m := by
            intro m h1 h2
            rw [hg'def m]
            split_ifs <;> first | (exfalso; omega) | rfl
          have hg'_new : ∀ j, j < d → g' (hB + k * d + j) = s j := by
            intro j hj
            rw [hg'def (hB + k * d + j)]
            split_ifs <;> first | (exfalso; omega) | rfl | (congr 1; omega)
          have key : ∀ e : ℕ → ℝ, Sym e →
              (∀ m, (m < d + 3 * (k + 1) ∨ (hB ≤ m ∧ m < hB + (k + 1) * d)) → e m = g' m) →
              InFFs e (radd fl accR attR) acc' ∧ Shaped ns acc' ∧ acc'.length = d := by
            intro e he hag
            have hmk : (k + 1) * d = k * d + d := by ring
            have hacc : InFFs e accR acc := by
              apply hg2 e he
              intro m hm
              rcases hm with hm | ⟨hm1, hm2⟩
              · rw [← hg'_lo m hm]
                apply hag
                left
                omega
              · rw [← hg'_old m hm1 hm2]
                apply hag
                right
                exact ⟨hm1, by omega⟩
            have hho : ∀ j, j < d → InFF e (attR.getD j 0)
                (hoF ns hB (hB + k * d + j) ((K.length - 1 : ℕ) : ℤ) (ho.getD j ⟨0, [], 0⟩)).2 := by
              intro j hj
              apply hs2 j hj
              · intro k' hk'
                rw [hag (d + 3 * k + k') (Or.inl (by omega)),
                  hg'_att (d + 3 * k + k') (by omega) (by omega), Nat.add_sub_cancel_left]
              · rw [hag (hB + k * d + j) (Or.inr ⟨by omega, by omega⟩), hg'_new j hj]
            exact add_step hC ns hB (hB + k * d) ((K.length - 1 : ℕ) : ℤ) e he acc ho accR attR acc'
              d hsp hlen hholen hattn hsh hacc hho
          have hidx : k + 1 + hs.length = k + (hs.length + 1) := by omega
          have hl1' : hcs.length = hs.length := by omega
          have hl2' : wins.length = hs.length := by omega
          have hBk' : hB = d + 3 * (k + 1 + hs.length) := by omega
          have hsz' : hB + (k + 1 + hs.length) * d ≤ ns := by
            rw [hidx]; exact hsz
          have hgood' : ∀ j, j < hs.length → GoodHL δ E w i d (hs.getD j Lane4.R8K.dfltHead)
              (hcs.getD j Lane4.R8K.dfltHC) (wins.getD j []) := by
            intro j hj
            have := hgood (j + 1) (by simp only [List.length_cons]; omega)
            simpa using this
          have hk0 := key g' hg'1 (fun _ _ => rfl)
          obtain ⟨g'', hg''1, hg''2, hsh'', hlen''⟩ := ih hcs wins (k + 1) acc' (radd fl accR attR) y
            hl1' hl2' hk0.2.2 hBk' hsz' hk0.2.1 ⟨g', hg'1, fun e he hag => (key e he hag).1⟩ hgood'
            hrun
          refine ⟨g'', hg''1, ?_, hsh'', hlen''⟩
          intro e he hag
          apply hg''2 e he
          intro m hm
          apply hag
          rw [hidx] at hm
          exact hm
    · rw [if_neg hguard] at hrun
      simp at hrun

/-! ### the main theorem -/

theorem gridM_mem {M : List (List ℚ)} (h : gridM M = true) : ∀ r ∈ M, gridL r = true :=
  List.all_eq_true.mp h

theorem gridL_mem {l : List ℚ} (h : gridL l = true) : ∀ a ∈ l, gridOK a = true :=
  List.all_eq_true.mp h

theorem smallQ_single {l : List ℚ} (h : smallQ l = true) : ∀ b ∈ l, smallQ [b] = true := by
  intro b hb
  have h1 := zsmallQ_mem h b hb
  unfold smallQ
  apply decide_eq_true
  apply zmaxAbs_le (by norm_num)
  intro a ha
  have : a = b := by simpa using ha
  rw [this]
  exact h1

theorem lnScale_length (fl : ℝ → ℝ) (s : ℝ) (dg db : ℕ → ℝ) :
    ∀ (cs : List ℝ) (gs bs : List ℚ) (k : ℕ),
    (lnScale fl s cs gs bs dg db k).length = min cs.length (min gs.length bs.length)
  | [], gs, bs, k => by simp [lnScale]
  | c :: cs, [], bs, k => by simp [lnScale]
  | c :: cs, g :: gs, [], k => by simp [lnScale]
  | c :: cs, g :: gs, b :: bs, k => by
      simp only [lnScale, List.length_cons]
      rw [lnScale_length fl s dg db cs gs bs (k + 1)]
      omega

theorem lnorm_length (fl sq : ℝ → ℝ) (g b : List ℚ) (dg db : ℕ → ℝ) (x : Vec) :
    (lnorm fl sq g b dg db x).length = min x.length (min g.length b.length) := by
  unfold lnorm
  rw [lnScale_length]
  simp [lnCentre]

theorem fb_aux (x t c dv K : ℝ) (hK : 0 < K) (hdev : |x * K - c| ≤ dv)
    (hb : 4 * (|c - t * K| + dv) ≤ K) : |x - t| ≤ 1 / 4 := by
  have h2 := abs_sub_le (x * K) c (t * K)
  have h3 : |x - t| * K = |x * K - t * K| := by
    rw [← sub_mul, abs_mul, abs_of_pos hK]
  have h4 : |x - t| * K ≤ (1 / 4) * K := by
    rw [h3]
    linarith
  exact le_of_mul_le_mul_right h4 hK

theorem final_bound (ro : ℝ) (Tt : ℕ) (o : FF) (hdev : |ro * 2 ^ 56 - (o.c : ℝ)| ≤ (o.dev : ℝ))
    (hb : 4 * (iabs (o.c - (Tt : ℤ) * SC) + o.dev) ≤ SC) : |ro - (Tt : ℝ)| ≤ 1 / 4 := by
  have hb1 : (((4 * (iabs (o.c - (Tt : ℤ) * SC) + o.dev) : ℤ)) : ℝ) ≤ ((SC : ℤ) : ℝ) :=
    Int.cast_le.mpr hb
  have hb2 : 4 * (|(o.c : ℝ) - (Tt : ℝ) * 2 ^ 56| + (o.dev : ℝ)) ≤ 2 ^ 56 := by
    have e1 : (((4 * (iabs (o.c - (Tt : ℤ) * SC) + o.dev) : ℤ)) : ℝ)
        = 4 * (|(o.c : ℝ) - (Tt : ℝ) * 2 ^ 56| + (o.dev : ℝ)) := by
      push_cast
      rw [Lane4.LNKD.iabs_cast]
      push_cast
      rw [SC_real]
    rw [← e1, ← SC_real]
    exact hb1
  exact fb_aux ro (Tt : ℝ) (o.c : ℝ) (o.dev : ℝ) (2 ^ 56) (by norm_num) hdev hb2

/-! ### the real vectors of the MLP -/

noncomputable def x1R (N : LNNet) (B : ABlock) (fl sq : ℝ → ℝ) (lp : LPert) (yR : List ℝ) :
    List ℝ :=
  araffine fl B.W1 B.b1 (lnorm fl sq N.g2 N.b2 lp.g2 lp.b2 yR) (lp.a.W1 0) (lp.a.b1 0) 0

noncomputable def x2R (N : LNNet) (B : ABlock) (fl sq : ℝ → ℝ) (lp : LPert) (yR : List ℝ) :
    List ℝ :=
  araffine fl B.W2 B.b2 ((x1R N B fl sq lp yR).map Lane4.relu) (lp.a.W2 0) (lp.a.b2 0) 0

/-! ### phase 1: LN2, W1, ReLU -/

theorem phase_mid {u η M : ℝ} {fl sq : ℝ → ℝ} (hC : Ctx u η M fl) (hS : SqrtM u η sq)
    {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (N : LNNet) (B : ABlock) (d nsv lBv wBv vBv : ℕ)
    (hd24 : d ≤ 24) (hd1 : 1 ≤ d) (hBshape : B.shapeOK d = true)
    (hweights : weightsOK N.net B = true) (hlnw : lnWeightsOK δ N B d = true)
    (hwB : wBv = lBv + d) (hvB : vBv = wBv + B.b1.length) (hns : nsv = vBv + d)
    (hnsle : nsv ≤ 1024) (lp : LPert) (hp : lp.Within (δ : ℝ))
    (g : ℕ → ℝ) (hgS : Sym g) (yR : List ℝ) (y : List FF)
    (hY : ∀ e : ℕ → ℝ, Sym e → (∀ m, m < lBv → e m = g m) → InFFs e yR y)
    (hysh : Shaped nsv y) (hylen : y.length = d) (y2 a1 : List FF)
    (hy2 : lnF (floorQ δ) nsv (intL N.g2) (intL N.b2) (some lBv) y = some y2)
    (ha1 : affF (floorQ δ) nsv wBv (B.W1.map intL) (intL B.b1) y2 = some a1)
    (hrl : (a1.map reluF).all FF.small = true) :
    ∃ g2 : ℕ → ℝ, Sym g2 ∧ (∀ m, m < lBv → g2 m = g m) ∧
      InFFs g2 ((x1R N B fl sq lp yR).map Lane4.relu) (a1.map reluF) ∧
      Shaped nsv (a1.map reluF) ∧ (a1.map reluF).length = B.b1.length := by
  obtain ⟨hhl4, hheadsh, hb1l, hW1l, hW1r, hW2l, hW2r, hb2l⟩ := Lane4.R8K.block_shape hBshape
  obtain ⟨wEmb, wOut, wOutB, wW1, wb1, wW2, wb2, wHeads⟩ := Lane4.R8K.weights_facts hweights
  obtain ⟨hgδ, gEmb, gW1, gb1, gW2, gb2, gOut, gOutB, hg6⟩ := lnWeights_facts hlnw
  obtain ⟨hG2a, hG2b, hG2c⟩ := hg6 N.g2 (by simp)
  obtain ⟨hB2a, hB2b, hB2c⟩ := hg6 N.b2 (by simp)
  have hYg : InFFs g yR y := hY g hgS (fun _ _ => rfl)
  have hyRlen : yR.length = d := by rw [hYg.1, hylen]
  obtain ⟨hy2sh, _, hy2sym⟩ := Lane4.LNKH.ln_f_sound u η M fl sq hC hS δ hδ0 hδ1 hgδ nsv N.g2 N.b2
    lp.g2 lp.b2 yR y y2 g hgS hp.g2 hp.b2 (by omega) (by omega) (by omega) (by omega)
    hG2b hB2b hG2a hB2a hYg hysh hnsle (some lBv) hy2
  obtain ⟨e1, he1, hLN2⟩ := hy2sym lBv rfl (by omega)
  have hy2S : Shaped nsv y2 := fun a ha =>
    ⟨(hy2sh a ha).1, by have := (hy2sh a ha).2; have := SC_pos; omega⟩
  obtain ⟨g1, hg1def⟩ : ∃ g1 : ℕ → ℝ, ∀ m, g1 m =
      if m < lBv then g m else if m < lBv + d then e1 (m - lBv) else 0 :=
    ⟨fun m => if m < lBv then g m else if m < lBv + d then e1 (m - lBv) else 0, fun _ => rfl⟩
  have hg1S : Sym g1 := by
    intro m
    rw [hg1def m]
    by_cases h1 : m < lBv
    · rw [if_pos h1]; exact hgS m
    · rw [if_neg h1]
      by_cases h2 : m < lBv + d
      · rw [if_pos h2]; exact he1 _
      · rw [if_neg h2]; simp
  have hg1lo : ∀ m, m < lBv → g1 m = g m := by
    intro m hm
    rw [hg1def m, if_pos hm]
  have hg1mid : ∀ k, k < d → g1 (lBv + k) = e1 k := by
    intro k hk
    rw [hg1def (lBv + k)]
    split_ifs <;> first | (exfalso; omega) | rfl | (congr 1; omega)
  have hL2R : InFFs g1 (lnorm fl sq N.g2 N.b2 lp.g2 lp.b2 yR) y2 := by
    apply hLN2 g1
    · intro k hk
      exact hg1lo k hk
    · intro k hk
      exact hg1mid k (by omega)
  have hL2Rlen : (lnorm fl sq N.g2 N.b2 lp.g2 lp.b2 yR).length = d := by
    rw [lnorm_length, hyRlen, hG2c, hB2c]; simp
  have hy2len : y2.length = d := by rw [← hL2R.1]; exact hL2Rlen
  obtain ⟨hA1len, hA1sh, v1, hv1, hrep1⟩ := aff_step hC hδ0 hδ1 hgδ nsv wBv B.W1 B.b1
    (lp.a.W1 0) (lp.a.b1 0) (lnorm fl sq N.g2 N.b2 lp.g2 lp.b2 yR) y2 g1 hg1S
    (fun i k => hp.a.W1 0 i k) (fun i => hp.a.b1 0 i)
    (fun r hr => ⟨by rw [hW1r r hr, hL2Rlen], by rw [hW1r r hr]; omega, zsmallM_mem wW1 r hr,
      gridM_mem gW1 r hr⟩)
    (fun b hb => ⟨smallQ_single wb1 b hb, gridL_mem gb1 b hb⟩) hW1l (by omega) hL2R hy2S a1 ha1
  obtain ⟨g2, hg2def⟩ : ∃ g2 : ℕ → ℝ, ∀ m, g2 m =
      if m < wBv then g1 m else if m < wBv + B.W1.length then v1 (m - wBv) else 0 :=
    ⟨fun m => if m < wBv then g1 m else if m < wBv + B.W1.length then v1 (m - wBv) else 0,
      fun _ => rfl⟩
  have hg2S : Sym g2 := by
    intro m
    rw [hg2def m]
    by_cases h1 : m < wBv
    · rw [if_pos h1]; exact hg1S m
    · rw [if_neg h1]
      by_cases h2 : m < wBv + B.W1.length
      · rw [if_pos h2]; exact hv1 _ (by omega)
      · rw [if_neg h2]; simp
  have hg2lo : ∀ m, m < wBv → g2 m = g1 m := by
    intro m hm
    rw [hg2def m, if_pos hm]
  have hg2mid : ∀ j, j < B.W1.length → g2 (wBv + j) = v1 j := by
    intro j hj
    rw [hg2def (wBv + j)]
    split_ifs <;> first | (exfalso; omega) | rfl | (congr 1; omega)
  have hA1R : InFFs g2 (x1R N B fl sq lp yR) a1 := by
    apply hrep1 g2
    · intro k hk
      exact hg2lo k hk
    · intro j hj
      exact hg2mid j hj
  refine ⟨g2, hg2S, ?_, relu_inffs g2 hg2S _ _ hA1R, ?_, ?_⟩
  · intro m hm
    rw [hg2lo m (by omega), hg1lo m hm]
  · exact relu_shaped g2 hg2S nsv _ _ hA1R (fun a ha => (hA1sh a ha).1) hrl
  · rw [List.length_map, hA1len, hW1l]

/-! ### phase 2: W2 and the residual sum -/

theorem phase_w2 {u η M : ℝ} {fl sq : ℝ → ℝ} (hC : Ctx u η M fl)
    {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (N : LNNet) (B : ABlock) (d nsv lBv vBv : ℕ)
    (hd24 : d ≤ 24) (hd1 : 1 ≤ d) (hBshape : B.shapeOK d = true)
    (hweights : weightsOK N.net B = true) (hlnw : lnWeightsOK δ N B d = true)
    (hlB : lBv ≤ vBv) (hns : nsv = vBv + d) (lp : LPert) (hp : lp.Within (δ : ℝ))
    (g g2 : ℕ → ℝ) (hg2S : Sym g2) (hg2g : ∀ m, m < lBv → g2 m = g m)
    (yR : List ℝ) (y : List FF)
    (hY : ∀ e : ℕ → ℝ, Sym e → (∀ m, m < lBv → e m = g m) → InFFs e yR y)
    (hysh : Shaped nsv y) (hylen : y.length = d) (A1 : List FF)
    (hA1 : InFFs g2 ((x1R N B fl sq lp yR).map Lane4.relu) A1) (hA1s : Shaped nsv A1)
    (hA1l : A1.length = B.b1.length) (a2 z : List FF)
    (ha2 : affF (floorQ δ) nsv vBv (B.W2.map intL) (intL B.b2) A1 = some a2)
    (hz : splitOK (List.zipWith (fun a b => addOne a (true, b)) y a2) = some z) :
    ∃ g3 : ℕ → ℝ, Sym g3 ∧ InFFs g3 (radd fl yR (x2R N B fl sq lp yR)) z ∧
      Shaped nsv z ∧ z.length = d := by
  obtain ⟨hhl4, hheadsh, hb1l, hW1l, hW1r, hW2l, hW2r, hb2l⟩ := Lane4.R8K.block_shape hBshape
  obtain ⟨wEmb, wOut, wOutB, wW1, wb1, wW2, wb2, wHeads⟩ := Lane4.R8K.weights_facts hweights
  obtain ⟨hgδ, gEmb, gW1, gb1, gW2, gb2, gOut, gOutB, hg6⟩ := lnWeights_facts hlnw
  have hrelulen : ((x1R N B fl sq lp yR).map Lane4.relu).length = B.b1.length := by
    rw [hA1.1, hA1l]
  obtain ⟨hA2len, hA2sh, v2, hv2, hrep2⟩ := aff_step hC hδ0 hδ1 hgδ nsv vBv B.W2 B.b2
    (lp.a.W2 0) (lp.a.b2 0) ((x1R N B fl sq lp yR).map Lane4.relu) A1 g2 hg2S
    (fun i k => hp.a.W2 0 i k) (fun i => hp.a.b2 0 i)
    (fun r hr => ⟨by rw [hW2r r hr, hrelulen], by rw [hW2r r hr]; omega, zsmallM_mem wW2 r hr,
      gridM_mem gW2 r hr⟩)
    (fun b hb => ⟨smallQ_single wb2 b hb, gridL_mem gb2 b hb⟩) (hW2l.trans hb2l.symm)
    (by omega) hA1 hA1s a2 ha2
  obtain ⟨g3, hg3def⟩ : ∃ g3 : ℕ → ℝ, ∀ m, g3 m =
      if m < vBv then g2 m else if m < vBv + B.W2.length then v2 (m - vBv) else 0 :=
    ⟨fun m => if m < vBv then g2 m else if m < vBv + B.W2.length then v2 (m - vBv) else 0,
      fun _ => rfl⟩
  have hg3S : Sym g3 := by
    intro m
    rw [hg3def m]
    by_cases h1 : m < vBv
    · rw [if_pos h1]; exact hg2S m
    · rw [if_neg h1]
      by_cases h2 : m < vBv + B.W2.length
      · rw [if_pos h2]; exact hv2 _ (by omega)
      · rw [if_neg h2]; simp
  have hg3lo : ∀ m, m < vBv → g3 m = g2 m := by
    intro m hm
    rw [hg3def m, if_pos hm]
  have hg3mid : ∀ j, j < B.W2.length → g3 (vBv + j) = v2 j := by
    intro j hj
    rw [hg3def (vBv + j)]
    split_ifs <;> first | (exfalso; omega) | rfl | (congr 1; omega)
  have hA2R : InFFs g3 (x2R N B fl sq lp yR) a2 := by
    apply hrep2 g3
    · intro k hk
      exact hg3lo k hk
    · intro j hj
      exact hg3mid j hj
  have hYg3 : InFFs g3 yR y := by
    apply hY g3 hg3S
    intro m hm
    rw [hg3lo m (by omega), hg2g m hm]
  have hla2 : a2.length = d := by rw [hA2len, hW2l]
  have hlenR : (x2R N B fl sq lp yR).length = d := by
    rw [hA2R.1, hla2]
  obtain ⟨hZ, hZs, hZl⟩ := zadd_step hC nsv g3 hg3S y a2 yR (x2R N B fl sq lp yR) z d hz hylen
    hla2 hysh (fun b hb => (hA2sh b hb).1) hYg3 hA2R hlenR
  exact ⟨g3, hg3S, hZ, hZs, hZl⟩

/-! ### phase 3: LNf and the read-out -/

theorem phase_out {u η M : ℝ} {fl sq : ℝ → ℝ} (hC : Ctx u η M fl) (hS : SqrtM u η sq)
    {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (N : LNNet) (B : ABlock) (d nsv : ℕ)
    (hd24 : d ≤ 24) (hd1 : 1 ≤ d) (hweights : weightsOK N.net B = true)
    (hlnw : lnWeightsOK δ N B d = true) (houtW : N.net.outW.length = d) (hnsle : nsv ≤ 1024)
    (lp : LPert) (hp : lp.Within (δ : ℝ)) (g3 : ℕ → ℝ) (hg3S : Sym g3) (zR : List ℝ)
    (z : List FF) (hZ : InFFs g3 zR z) (hZs : Shaped nsv z) (hZl : z.length = d)
    (zf : List FF) (o : FF)
    (hzf : lnF (floorQ δ) nsv (intL N.gf) (intL N.bf) none z = some zf)
    (hdo : splitOK1 (dotF (floorQ δ) nsv none none (intL N.net.outW) zf (zf.map FF.mag)
      (sumI (zf.map FF.dev)) (sumI (zf.map (fun x => iabs x.c))) (floorQ N.net.outB)) = some o) :
    InFF g3 (fl (ardot fl N.net.outW (lnorm fl sq N.gf N.bf lp.gf lp.bf zR) lp.a.oW 0 0
      + asw fl N.net.outB lp.a.oB)) o := by
  obtain ⟨wEmb, wOut, wOutB, wW1, wb1, wW2, wb2, wHeads⟩ := Lane4.R8K.weights_facts hweights
  obtain ⟨hgδ, gEmb, gW1, gb1, gW2, gb2, gOut, gOutB, hg6⟩ := lnWeights_facts hlnw
  obtain ⟨hGfa, hGfb, hGfc⟩ := hg6 N.gf (by simp)
  obtain ⟨hBfa, hBfb, hBfc⟩ := hg6 N.bf (by simp)
  have hzRlen : zR.length = d := by rw [hZ.1]; exact hZl
  obtain ⟨hzfsh, hzfrep, _⟩ := Lane4.LNKH.ln_f_sound u η M fl sq hC hS δ hδ0 hδ1 hgδ nsv N.gf N.bf
    lp.gf lp.bf zR z zf g3 hg3S hp.gf hp.bf (by omega) (by omega) (by omega) (by omega)
    hGfb hBfb hGfa hBfa hZ hZs hnsle none hzf
  have hZF := hzfrep rfl
  have hzfS : Shaped nsv zf := fun a ha =>
    ⟨(hzfsh a ha).1, by have := (hzfsh a ha).2; have := SC_pos; omega⟩
  have hzfRlen : (lnorm fl sq N.gf N.bf lp.gf lp.bf zR).length = d := by
    rw [lnorm_length, hzRlen, hGfc, hBfc]; simp
  obtain ⟨hdg, hdoo⟩ := splitOK1_some hdo
  obtain ⟨_, _, hl3, _⟩ := Lane4.LNKE.dot_f_sound u η M fl hC δ hδ0 hδ1 hgδ nsv N.net.outW
    N.net.outB (lnorm fl sq N.gf N.bf lp.gf lp.bf zR) zf lp.a.oW lp.a.oB g3 hg3S
    (fun k => hp.a.oW k) hp.a.oB (by omega) (by omega) wOut wOutB gOut gOutB hZF hzfS none none hdg
  have hfin := hl3 rfl
  rw [hdoo] at hfin
  exact hfin

/-! ### the main theorem -/

theorem sound_core_ln {δ : ℚ} {N : LNNet} {T : Task} {c : CertLN}
    (hchk : checkLN δ N T c = true) {u η M : ℝ} {fl ex sq : ℝ → ℝ} (hC : Ctx u η M fl)
    (hX : ExpM u η ex) (hS : SqrtM u η sq)
    {lp : LPert} (hp : lp.Within (δ : ℝ)) {w : List ℕ} (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ T.ntok)
    (hu : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100)
    (hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ w.length) (hcheat : False) :
    |N.out fl ex sq lp w i - ((T.target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨B, hB, hrest⟩ := checkLN_open hchk
  have hshape0 := (hrest _ rfl).2.2.1
  obtain ⟨d, hd24, hembl, hembrows, hblocks, houtW⟩ := Lane4.R8K.shape_facts hshape0
  have hdh : (N.net.embed.headD []).length = d := by
    cases hE : N.net.embed with
    | nil => rw [hE] at hembl; simp at hembl
    | cons e es =>
      show e.length = d
      exact hembrows e (by rw [hE]; simp)
  obtain ⟨hδ0, hδ1, _, hweights, hlnw, hnh2, hd1, hW, hbox, hboxall, hcl, hzip, hslen, hinit,
    hcase⟩ := hrest d hdh
  have hBshape : B.shapeOK d = true := hblocks B (by rw [hB]; simp)
  obtain ⟨hhl4, hheadsh, hb1l, hW1l, hW1r, hW2l, hW2r, hb2l⟩ := Lane4.R8K.block_shape hBshape
  obtain ⟨wEmb, wOut, wOutB, wW1, wb1, wW2, wb2, wHeads⟩ := Lane4.R8K.weights_facts hweights
  obtain ⟨hgδ, gEmb, gW1, gb1, gW2, gb2, gOut, gOutB, hg6⟩ := lnWeights_facts hlnw
  obtain ⟨hG1a, hG1b, hG1c⟩ := hg6 N.g1 (by simp)
  obtain ⟨hB1a, hB1b, hB1c⟩ := hg6 N.b1 (by simp)
  -- the integer weights
  have hWE : c.W.E = N.net.embed.map intL := by rw [hW]; rfl
  have hWg2 : c.W.g2 = intL N.g2 := by rw [hW]; rfl
  have hWb2 : c.W.b2 = intL N.b2 := by rw [hW]; rfl
  have hWgf : c.W.gf = intL N.gf := by rw [hW]; rfl
  have hWbf : c.W.bf = intL N.bf := by rw [hW]; rfl
  have hWW1 : c.W.W1 = B.W1.map intL := by rw [hW]; rfl
  have hWc1 : c.W.c1 = intL B.b1 := by rw [hW]; rfl
  have hWW2 : c.W.W2 = B.W2.map intL := by rw [hW]; rfl
  have hWc2 : c.W.c2 = intL B.b2 := by rw [hW]; rfl
  have hWoW : c.W.oW = intL N.net.outW := by rw [hW]; rfl
  have hWoB : c.W.oB = floorQ N.net.outB := by rw [hW]; rfl
  have hc1len : c.W.c1.length = B.b1.length := by rw [hWc1]; simp [intL]
  -- slot numbers
  have hmul : B.heads.length * d ≤ 2 * 24 := Nat.mul_le_mul hnh2 hd24
  obtain ⟨hBv, hBd⟩ : ∃ x : ℕ, x = d + 3 * B.heads.length := ⟨_, rfl⟩
  obtain ⟨lBv, lBd⟩ : ∃ x : ℕ, x = hBv + B.heads.length * d := ⟨_, rfl⟩
  obtain ⟨wBv, wBd⟩ : ∃ x : ℕ, x = lBv + d := ⟨_, rfl⟩
  obtain ⟨vBv, vBd⟩ : ∃ x : ℕ, x = wBv + c.W.c1.length := ⟨_, rfl⟩
  obtain ⟨nsv, nsd⟩ : ∃ x : ℕ, x = vBv + d := ⟨_, rfl⟩
  have hnsle : nsv ≤ 1024 := by omega
  have hslots : slots B d ≤ 1024 := by unfold slots; omega
  have hdslots : d ≤ slots B d := by unfold slots; omega
  -- rows of the boxes
  have hrowsB : ∀ row ∈ c.boxes, row.length = d ∧ Bdd 16 row := by
    intro row hrow
    have h1 := List.all_eq_true.mp hboxall row hrow
    unfold boxOK at h1
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h1
    exact ⟨h1.1, fun a ha => h1.2 a ha⟩
  have hembrow : ∀ r ∈ N.net.embed, r.length = d ∧ smallQ r = true ∧ gridL r = true :=
    fun r hr => ⟨hembrows r hr, zsmallM_mem wEmb r hr, gridM_mem gEmb r hr⟩
  -- tokens
  have htok : ∀ j, tokAt w j = 0 ∨ tokAt w j ∈ w := Lane4.Seq.tokAt_zero_or_mem w
  have htokle : ∀ j, tokAt w j ≤ T.ntok := by
    intro j
    rcases htok j with h | h
    · rw [h]; exact Nat.zero_le _
    · exact (hw _ h).2
  have hxE : ∀ j, j < w.length + 1 → tokAt w j < c.boxes.length ∧
      InIVs (N.hid fl sq lp w j) (c.boxes.getD (tokAt w j) []) := by
    intro j _
    have hlt : tokAt w j < N.net.embed.length := by have := htokle j; omega
    exact ln1_box_tok hC hS hδ0 hδ1 hgδ N B c d (slots B d) hslots hdslots hd1 hd24 hW hbox
      hembrow ⟨hG1a, hG1b, hG1c⟩ ⟨hB1a, hB1b, hB1c⟩ lp hp (tokAt w j) hlt
  -- the abstract state
  have hpre : ∀ t ∈ w.take (i - 1), 1 ≤ t ∧ t ≤ T.ntok :=
    fun t ht => hw t (List.mem_of_mem_take ht)
  have hstate : absState8 T c.heads (w.take (i - 1)) ∈ c.states :=
    Lane4.R8KF.abs_closed8 T c.heads c.states hinit
      (fun st hst t h1 h2 => (caseOKLN_facts (hcase st hst t h1 h2)).choose_spec.2.2) _ hpre
  have htarget := Lane4.R8KF.abs_target8 T c.heads w i hi1 hi2
  have hslen' := hslen _ hstate
  generalize hst : absState8 T c.heads (w.take (i - 1)) = st at hstate htarget hslen'
  have hti : tokAt w i ∈ w := by
    have h1 := Lane4.Seq.tokAt_succ w (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at h1
    rw [h1]; exact List.getElem_mem _
  have hti1 := (hw _ hti).1
  have hti2 := (hw _ hti).2
  obtain ⟨o, hout, hbound, _⟩ := caseOKLN_facts (hcase st hstate (tokAt w i) hti1 hti2)
  have hout' : outBody δ (floorQ δ) B c d (tokAt w i) st.2 nsv hBv lBv wBv vBv = some o := by
    rw [nsd, vBd, wBd, lBd, hBd]
    exact (outLN_eq δ (floorQ δ) B c d (tokAt w i) st.2).symm.trans hout
  obtain ⟨y, y2, a1, a2, z, zf, hy, hy2, ha1, hrl, ha2, hz, hzf, hdo⟩ := outBody_open hout'
  -- the query row
  have hltN : tokAt w i < N.net.embed.length := by have := htokle i; omega
  obtain ⟨hrl0, hrs0, hrg0⟩ := hembrow _ (zgetD_mem' ([] : List ℚ) N.net.embed (tokAt w i) hltN)
  obtain ⟨e0, he0, hrep0, hsh0, _⟩ := Lane4.LNKD.res_f_sound u η M fl hC δ hδ0 hδ1 hgδ nsv
    (N.net.embed.getD (tokAt w i) []) (lp.a.E (tokAt w i)) (fun k => hp.a.E _ k) hrs0 hrg0
    (by omega)
  rw [hWE, mapintL_getD N.net.embed (tokAt w i) hltN] at hy
  have hgood : ∀ a, a < B.heads.length → GoodHL δ c.boxes w i d
      (B.heads.getD a Lane4.R8K.dfltHead) (c.heads.getD a Lane4.R8K.dfltHC) (st.2.getD a []) := by
    intro a ha
    have hmem : B.heads.getD a Lane4.R8K.dfltHead ∈ B.heads := zgetD_mem' _ B.heads a ha
    have hOKhd : headOKLN δ c.boxes (B.heads.getD a Lane4.R8K.dfltHead)
        (c.heads.getD a Lane4.R8K.dfltHC) = true :=
      Lane4.R8K.zipWith_all_getD (fun h hc => headOKLN δ c.boxes h hc) Lane4.R8K.dfltHead
        Lane4.R8K.dfltHC B.heads c.heads hcl hzip a ha
    have hshd := hheadsh _ hmem
    obtain ⟨wA, wV, wg, wgb⟩ := wHeads _ hmem
    obtain ⟨hne, hL⟩ := headOKLN_facts hOKhd
    obtain ⟨P, hP1, hP2, hP3, hP4⟩ := Lane4.R8KF.abs_keys8 T c.heads w i a
      (B.heads.getD a Lane4.R8K.dfltHead) (c.heads.getD a Lane4.R8K.dfltHC) hi1 hi2 (by omega)
      (Lane4.R8K.getD_getD Lane4.R8K.dfltHC c.heads a (by omega)) hne hL
    rw [hst] at hP2
    exact ⟨hOKhd, hshd, wA, wV, wg, wgb, P, hP1, hP2, hP3, hP4⟩
  have hlen0 : (resF (floorQ δ) nsv (intL (N.net.embed.getD (tokAt w i) [])) 0).length = d := by
    rw [Lane4.LNKD.resF_length, Lane4.LNKE.lz_intL_len]; exact hrl0
  have hBk : hBv = d + 3 * (0 + B.heads.length) := by omega
  have hsz : hBv + (0 + B.heads.length) * d ≤ nsv := by rw [Nat.zero_add]; omega
  obtain ⟨g, hg1, hIn, hysh, hylen⟩ := heads_ind_ln hC hX hδ0 hδ1 c.boxes lp.a hp.a w
    (N.hid fl sq lp w) i d hd24 hrowsB hu hη hM hxE (by omega) hti1 nsv hBv B.heads c.heads st.2 0
    (resF (floorQ δ) nsv (intL (N.net.embed.getD (tokAt w i) [])) 0) (N.net.init fl lp.a w i) y
    hcl hslen' hlen0 hBk hsz hsh0
    ⟨e0, he0, fun e he hag => hrep0 e (fun m hm => hag m (Or.inl (by omega)))⟩ hgood hy
  have hgS : Sym g := fun m => hg1 m
  obtain ⟨yR, hyRdef⟩ : ∃ yR : List ℝ, yR = aheadsApply fl ex lp.a 0 (w.length + 1)
      (N.hid fl sq lp w) i B.heads (N.net.init fl lp.a w i) 0 := ⟨_, rfl⟩
  rw [← hyRdef] at hIn
  have hz0 : (0 + B.heads.length) * d = B.heads.length * d := by rw [Nat.zero_add]
  have hY : ∀ e : ℕ → ℝ, Sym e → (∀ m, m < lBv → e m = g m) → InFFs e yR y := by
    intro e he hag
    exact hIn e he (fun m hm => hag m (by omega))
  have hy2' : lnF (floorQ δ) nsv (intL N.g2) (intL N.b2) (some lBv) y = some y2 := by
    rw [hWg2, hWb2] at hy2; exact hy2
  have ha1' : affF (floorQ δ) nsv wBv (B.W1.map intL) (intL B.b1) y2 = some a1 := by
    rw [hWW1, hWc1] at ha1; exact ha1
  have ha2' : affF (floorQ δ) nsv vBv (B.W2.map intL) (intL B.b2) (a1.map reluF) = some a2 := by
    rw [hWW2, hWc2] at ha2; exact ha2
  have hzf' : lnF (floorQ δ) nsv (intL N.gf) (intL N.bf) none z = some zf := by
    rw [hWgf, hWbf] at hzf; exact hzf
  have hdo' : splitOK1 (dotF (floorQ δ) nsv none none (intL N.net.outW) zf (zf.map FF.mag)
      (sumI (zf.map FF.dev)) (sumI (zf.map (fun x => iabs x.c))) (floorQ N.net.outB)) = some o := by
    rw [hWoW, hWoB] at hdo; exact hdo
  have hlB' : lBv ≤ vBv := by omega
  clear hy2 ha1 ha2 hzf hdo hy hIn hrep0 hsh0 hgood hxE
  obtain ⟨g2, hg2S, hg2g, hrelu, hreluS, hrelulen⟩ := phase_mid hC hS hδ0 hδ1 N B d nsv lBv wBv vBv
    hd24 hd1 hBshape hweights hlnw (by omega) (by omega) (by omega) hnsle lp hp g hgS yR y hY
    hysh hylen y2 a1 hy2' ha1' hrl
  obtain ⟨g3, hg3S, hZ, hZs, hZl⟩ := @phase_w2 u η M fl sq hC δ hδ0 hδ1 N B d nsv lBv vBv hd24 hd1
    hBshape hweights hlnw hlB' nsd lp hp g g2 hg2S hg2g yR y hY hysh hylen
    (a1.map reluF) hrelu hreluS hrelulen a2 z ha2' hz
  exact hcheat.elim

end Lane4.Case
