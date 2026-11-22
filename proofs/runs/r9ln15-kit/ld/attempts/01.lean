set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Lane4.Case
open Lane4.RSeq (Vec pdot radd rsum)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2

/-! ### basic integer lemmas -/

theorem iabs_eq' (a : ℤ) : iabs a = |a| := by
  unfold iabs; exact Int.natCast_natAbs a

theorem iabs_cast (a : ℤ) : ((iabs a : ℤ) : ℝ) = |(a : ℝ)| := by
  rw [iabs_eq', Int.cast_abs]

theorem iabs_nonneg' (a : ℤ) : 0 ≤ iabs a := by
  rw [iabs_eq']; exact abs_nonneg a

theorem foldl_iabs (l : List ℤ) : ∀ s : ℤ, l.foldl (fun s v => s + iabs v) s = s + (l.map iabs).sum := by
  induction l with
  | nil => intro s; simp
  | cons a l ih => intro s; simp [List.foldl, ih]; ring

theorem linI_eq (t : List ℤ) : linI t = (t.map iabs).sum := by
  unfold linI; rw [foldl_iabs]; simp

theorem linI_cons (a : ℤ) (l : List ℤ) : linI (a :: l) = iabs a + linI l := by
  rw [linI_eq, linI_eq]; simp

theorem linI_nil' : linI [] = 0 := by simp [linI_eq]

theorem linI_append (l1 l2 : List ℤ) : linI (l1 ++ l2) = linI l1 + linI l2 := by
  simp [linI_eq]

theorem linI_nonneg (t : List ℤ) : 0 ≤ linI t := by
  induction t with
  | nil => rw [linI_nil']
  | cons a l ih => rw [linI_cons]; have := iabs_nonneg' a; omega

theorem linValI_abs_le (e : ℕ → ℝ) (he : Sym e) (t : List ℤ) :
    ∀ k, |linValI t e k| ≤ ((linI t : ℤ) : ℝ) := by
  induction t with
  | nil => intro k; simp [linValI, linI_nil']
  | cons a l ih =>
    intro k
    rw [linI_cons]
    simp only [linValI]
    push_cast
    rw [iabs_cast]
    have h1 := he k
    have h2 := ih (k + 1)
    have h3 : |(a : ℝ)| * |e k| ≤ |(a : ℝ)| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    calc _ ≤ |(a : ℝ) * e k| + |linValI l e (k + 1)| := abs_add_le _ _
      _ ≤ |(a : ℝ)| + ((linI l : ℤ) : ℝ) := by
          rw [abs_mul]; linarith

theorem linValI_zipWith_add (e : ℕ → ℝ) : ∀ (a b : List ℤ) (k : ℕ), a.length = b.length →
    linValI (List.zipWith (fun x y => x + y) a b) e k = linValI a e k + linValI b e k := by
  intro a
  induction a with
  | nil =>
    intro b k h
    cases b with
    | nil => simp [linValI]
    | cons _ _ => simp at h
  | cons x a ih =>
    intro b k h
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.zipWith_cons_cons, linValI]
      rw [ih b (k + 1) (by simpa using h)]
      push_cast; ring

theorem linValI_frame (e e' : ℕ → ℝ) : ∀ (t : List ℤ) (k : ℕ),
    (∀ i, k ≤ i → e' i ≠ e i → t.getD (i - k) 0 = 0) → linValI t e' k = linValI t e k := by
  intro t
  induction t with
  | nil => intro k h; simp [linValI]
  | cons a l ih =>
    intro k h
    simp only [linValI]
    have h0 : (a : ℝ) * e' k = (a : ℝ) * e k := by
      by_cases hk : e' k = e k
      · rw [hk]
      · have := h k le_rfl hk
        simp at this
        simp [this]
    rw [h0, ih (k + 1)]
    intro i hi hne
    have := h i (by omega) hne
    have hi' : i - k = (i - (k + 1)) + 1 := by omega
    rw [hi'] at this
    simpa using this

theorem linValI_append (e : ℕ → ℝ) : ∀ (l1 l2 : List ℤ) (s : ℕ),
    linValI (l1 ++ l2) e s = linValI l1 e s + linValI l2 e (s + l1.length) := by
  intro l1
  induction l1 with
  | nil => intro l2 s; simp [linValI]
  | cons a l ih =>
    intro l2 s
    simp only [List.cons_append, linValI, ih, List.length_cons]
    rw [show s + 1 + l.length = s + (l.length + 1) by omega]
    ring

theorem linValI_replicate (e : ℕ → ℝ) : ∀ n k, linValI (List.replicate n (0 : ℤ)) e k = 0 := by
  intro n
  induction n with
  | zero => intro k; simp [linValI]
  | succ n ih => intro k; simp [List.replicate_succ, linValI, ih]

theorem linValI_pre (e : ℕ → ℝ) (rest : List ℤ) : ∀ pre k,
    linValI (List.replicate pre 0 ++ rest) e k = linValI rest e (k + pre) := by
  intro pre
  induction pre with
  | zero => intro k; simp
  | succ pre ih =>
    intro k
    simp only [List.replicate_succ, List.cons_append, linValI, ih]
    rw [show k + 1 + pre = k + (pre + 1) by omega]
    simp

theorem linVal_pre (e : ℕ → ℝ) (rest : List ℚ) : ∀ pre k,
    linVal (List.replicate pre 0 ++ rest) e k = linVal rest e (k + pre) := by
  intro pre
  induction pre with
  | zero => intro k; simp
  | succ pre ih =>
    intro k
    simp only [List.replicate_succ, List.cons_append, linVal, ih]
    rw [show k + 1 + pre = k + (pre + 1) by omega]
    simp

/-! ### frame, zero facts -/

theorem frame_ff : FrameFF := by
  intro a e e' v h hv
  unfold InFF at *
  rw [linValI_frame e e' a.t 0 (fun i _ hne => by simpa using h i hne)]
  exact hv

theorem zf_aux : ∀ (t : List ℤ) (m k : ℕ), (t.drop m).all (fun v => v == 0) = true → m ≤ k →
    t.getD k 0 = 0 := by
  intro t
  induction t with
  | nil => intro m k _ _; simp
  | cons a l ih =>
    intro m k h hk
    cases m with
    | zero =>
      simp at h
      cases k with
      | zero => simpa using h.1
      | succ k' =>
        simp only [List.getD_cons_succ]
        exact ih 0 k' (by simpa using h.2) (Nat.zero_le _)
    | succ m' =>
      cases k with
      | zero => omega
      | succ k' =>
        simp only [List.getD_cons_succ]
        exact ih m' k' (by simpa using h) (by omega)

theorem zf_of : ∀ (t : List ℤ) (m : ℕ), (∀ k, m ≤ k → t.getD k 0 = 0) →
    (t.drop m).all (fun v => v == 0) = true := by
  intro t
  induction t with
  | nil => intro m _; simp
  | cons a l ih =>
    intro m h
    cases m with
    | zero =>
      simp only [List.drop_zero, List.all_cons, Bool.and_eq_true, beq_iff_eq]
      refine ⟨?_, ?_⟩
      · simpa using h 0 (Nat.zero_le _)
      · have := ih 0 (fun k _ => by simpa using h (k + 1) (by omega))
        simpa using this
    | succ m' =>
      simp only [List.drop_succ_cons]
      exact ih m' (fun k hk => by simpa using h (k + 1) (by omega))

theorem zr_aux : ∀ (t : List ℤ) (lo n k : ℕ), ((t.drop lo).take n).all (fun v => v == 0) = true →
    lo ≤ k → k < lo + n → t.getD k 0 = 0 := by
  intro t
  induction t with
  | nil => intros; simp
  | cons a l ih =>
    intro lo n k h h1 h2
    cases lo with
    | zero =>
      cases n with
      | zero => omega
      | succ n' =>
        simp at h
        cases k with
        | zero => simpa using h.1
        | succ k' =>
          simp only [List.getD_cons_succ]
          exact ih 0 n' k' (by simpa using h.2) (Nat.zero_le _) (by omega)
    | succ lo' =>
      cases k with
      | zero => omega
      | succ k' =>
        simp only [List.getD_cons_succ]
        exact ih lo' n k' (by simpa using h) (by omega) (by omega)

theorem zero_facts : ZeroFacts := by
  refine ⟨?_, ?_⟩
  · intro m a h k hk
    exact zf_aux a.t m k h hk
  · intro lo hi a h k hk1 hk2
    exact zr_aux a.t lo (hi - lo) k h hk1 (by omega)

/-! ### floors -/

theorem floor_facts (a b : ℤ) (hb : 0 < b) :
    (((a / b : ℤ)) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b < (((a / b : ℤ)) : ℝ) + 1 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (a / b) * b ≤ a := Int.ediv_mul_le a hb.ne'
  have h2 : a < (a / b + 1) * b := Int.lt_ediv_add_one_mul_self a hb
  have h1' : (((a / b : ℤ)) : ℝ) * b ≤ a := by exact_mod_cast h1
  have h2' : (a : ℝ) < ((((a / b : ℤ)) : ℝ) + 1) * b := by exact_mod_cast h2
  constructor
  · rw [le_div_iff₀ hb']; exact h1'
  · rw [div_lt_iff₀ hb']; exact h2'

theorem cdiv_facts (a b : ℤ) (hb : 0 < b) :
    (a : ℝ) / b ≤ ((cdiv a b : ℤ) : ℝ) ∧ ((cdiv a b : ℤ) : ℝ) < (a : ℝ) / b + 1 := by
  have h := floor_facts (-a) b hb
  have e1 : ((cdiv a b : ℤ) : ℝ) = -((((-a) / b : ℤ)) : ℝ) := by
    show ((-((-a) / b) : ℤ) : ℝ) = _
    rw [Int.cast_neg]
  rw [e1]
  simp only [Int.cast_neg, neg_div] at h
  constructor <;> linarith [h.1, h.2]

theorem chg_facts (m : ℤ) (hm : 0 ≤ m) :
    (m : ℝ) / 2 ^ 22 < ((chg m : ℤ) : ℝ) ∧ (1 : ℝ) ≤ ((chg m : ℤ) : ℝ) := by
  have h := floor_facts m (2 ^ 22) (by norm_num)
  have h0 : 0 ≤ m / 2 ^ 22 := Int.ediv_nonneg hm (by norm_num)
  have h0' : (0 : ℝ) ≤ ((m / 2 ^ 22 : ℤ) : ℝ) := by exact_mod_cast h0
  have hchg : chg m = m / 2 ^ 22 + 1 := rfl
  have e : ((2 ^ 22 : ℤ) : ℝ) = 2 ^ 22 := by norm_num
  rw [e] at h
  rw [hchg, Int.cast_add, Int.cast_one]
  constructor <;> linarith [h.2]

theorem round_chg {u η : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149)
    (X : ℝ) (m : ℤ) (hX : |X| * 2 ^ 56 ≤ (m : ℝ)) :
    (u * |X| + η) * 2 ^ 56 ≤ ((chg m : ℤ) : ℝ) := by
  have hm : 0 ≤ m := by
    have : (0 : ℝ) ≤ m := le_trans (by positivity) hX
    exact_mod_cast this
  obtain ⟨h1, h2⟩ := chg_facts m hm
  have h3 : u * (|X| * 2 ^ 56) ≤ (1 / 2 ^ 24) * (m : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hu (by positivity)) (mul_le_mul_of_nonneg_left hX (by norm_num))
  have h4 : η * 2 ^ 56 ≤ 1 / 2 ^ 93 := by
    calc η * 2 ^ 56 ≤ (1 / 2 ^ 149) * 2 ^ 56 := mul_le_mul_of_nonneg_right hη (by norm_num)
      _ = 1 / 2 ^ 93 := by norm_num
  have : (u * |X| + η) * 2 ^ 56 = u * (|X| * 2 ^ 56) + η * 2 ^ 56 := by ring
  rw [this]
  linarith

theorem floorQ_facts (q : ℚ) :
    ((floorQ q : ℤ) : ℝ) ≤ (q : ℝ) * 2 ^ 56 ∧ (q : ℝ) * 2 ^ 56 < ((floorQ q : ℤ) : ℝ) + 1 := by
  have h := floor_facts (q.num * SC) (q.den : ℤ) (by exact_mod_cast q.den_pos)
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hq : (q : ℝ) * 2 ^ 56 = ((q.num * SC : ℤ) : ℝ) / (((q.den : ℤ)) : ℝ) := by
    rw [Rat.cast_def, Int.cast_mul, hSC, Int.cast_natCast]
    field_simp
  rw [hq]
  exact h

theorem floorQ_grid (q : ℚ) (h : gridOK q = true) : ((floorQ q : ℤ) : ℝ) = (q : ℝ) * 2 ^ 56 := by
  unfold gridOK at h
  have hdvd : (q.den : ℤ) ∣ SC := Int.dvd_of_emod_eq_zero (of_decide_eq_true h)
  have hd : (q.den : ℤ) ∣ q.num * SC := Dvd.dvd.mul_left hdvd _
  have h1 : q.num * SC / (q.den : ℤ) * (q.den : ℤ) = q.num * SC := Int.ediv_mul_cancel hd
  have h2 : ((floorQ q : ℤ) : ℝ) * (q.den : ℝ) = (q.num : ℝ) * 2 ^ 56 := by
    have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
    have : ((q.num * SC / (q.den : ℤ) * (q.den : ℤ) : ℤ) : ℝ) = ((q.num * SC : ℤ) : ℝ) := by
      rw [h1]
    rw [Int.cast_mul, Int.cast_mul, hSC, Int.cast_natCast] at this
    exact this
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [Rat.cast_def]
  field_simp
  linarith

theorem ceilQ_facts (q : ℚ) : (q : ℝ) * 2 ^ 56 ≤ ((ceilQ q : ℤ) : ℝ) := by
  have h := (floorQ_facts (-q)).1
  have e1 : ((ceilQ q : ℤ) : ℝ) = -((floorQ (-q) : ℤ) : ℝ) := by
    show ((-(floorQ (-q)) : ℤ) : ℝ) = _
    rw [Int.cast_neg]
  rw [e1]
  rw [Rat.cast_neg] at h
  linarith

theorem floorQ_zero : floorQ 0 = 0 := by simp [floorQ]

/-! ### box, forms -/

theorem inff_dev (e : ℕ → ℝ) (v : ℝ) (a : FF) (he : Sym e) (h : InFF e v a) :
    |v * 2 ^ 56 - (a.c : ℝ)| ≤ (a.dev : ℝ) := by
  have hl := linValI_abs_le e he a.t 0
  unfold InFF at h
  have hdev : (a.dev : ℝ) = (linI a.t : ℝ) + a.r := by simp [FF.dev]
  have e1 : v * 2 ^ 56 - (a.c : ℝ)
      = (v * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0)) + linValI a.t e 0 := by ring
  rw [e1, hdev]
  calc _ ≤ |v * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0)| + |linValI a.t e 0| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem inff_r_nonneg (e : ℕ → ℝ) (v : ℝ) (a : FF) (h : InFF e v a) : 0 ≤ a.r := by
  unfold InFF at h
  have : (0 : ℝ) ≤ (a.r : ℝ) := le_trans (abs_nonneg _) h
  exact_mod_cast this

theorem box_sound : BoxSound := by
  intro e v a he h
  have hd := inff_dev e v a he h
  have hr := inff_r_nonneg e v a h
  have hlI := linI_nonneg a.t
  have hdev0 : 0 ≤ a.dev := by unfold FF.dev; omega
  have hmag : (a.mag : ℝ) = |(a.c : ℝ)| + a.dev := by
    unfold FF.mag; push_cast; rw [iabs_cast]
  have hpos : (0 : ℝ) < 2 ^ 56 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · have e1 : (((a.c : ℚ) / SCq : ℚ) : ℝ) = (a.c : ℝ) / 2 ^ 56 := by simp [SCq]
    have e2 : (((a.dev : ℚ) / SCq : ℚ) : ℝ) = (a.dev : ℝ) / 2 ^ 56 := by simp [SCq]
    show |v - (((a.c : ℚ) / SCq : ℚ) : ℝ)| ≤ (((a.dev : ℚ) / SCq : ℚ) : ℝ)
    rw [e1, e2]
    have : v - (a.c : ℝ) / 2 ^ 56 = (v * 2 ^ 56 - (a.c : ℝ)) / 2 ^ 56 := by field_simp
    rw [this, abs_div, abs_of_pos hpos]
    gcongr
  · show (0 : ℚ) ≤ (a.dev : ℚ) / SCq
    have : (0 : ℚ) ≤ (a.dev : ℚ) := by exact_mod_cast hdev0
    exact div_nonneg this (by unfold SCq; positivity)
  · rw [hmag]
    have e3 : |v| * 2 ^ 56 = |v * 2 ^ 56| := by rw [abs_mul, abs_of_pos hpos]
    rw [e3]
    have e4 : v * 2 ^ 56 = (a.c : ℝ) + (v * 2 ^ 56 - (a.c : ℝ)) := by ring
    calc |v * 2 ^ 56| = |(a.c : ℝ) + (v * 2 ^ 56 - (a.c : ℝ))| := by rw [← e4]
      _ ≤ |(a.c : ℝ)| + |v * 2 ^ 56 - (a.c : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith

/-! ### add -/

theorem wide_round {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (e : ℕ → ℝ) (he : Sym e) (z f : ℝ)
    (s : FF) (hs : InFF e z s) (hf : |f - z| ≤ u * |z| + η) :
    InFF e f (s.wide (chg s.mag)) := by
  have hb := box_sound e z s he hs
  have h1 := round_chg hC.u0 hC.u1 hC.h0 hC.h1 z s.mag hb.2.2
  unfold InFF at hs ⊢
  simp only [FF.wide]
  push_cast
  have e1 : f * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)
      = (f - z) * 2 ^ 56 + (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)) := by ring
  rw [e1]
  have h2 : |(f - z) * 2 ^ 56| = |f - z| * 2 ^ 56 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
  have h3 : |f - z| * 2 ^ 56 ≤ (u * |z| + η) * 2 ^ 56 := mul_le_mul_of_nonneg_right hf (by norm_num)
  have h4 := abs_add_le ((f - z) * 2 ^ 56) (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0))
  linarith

theorem add_f_sound : AddFSound := by
  intro u η M fl hC e x y a b he hx hy hlen ha hb
  have hbx := box_sound e x a he hx
  have hby := box_sound e y b he hy
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have ha' : (a.mag : ℝ) ≤ 16 * 2 ^ 56 := by
    have := (show ((a.mag : ℤ) : ℝ) ≤ (((16 * SC : ℤ)) : ℝ) by exact_mod_cast ha)
    rw [Int.cast_mul, hSC] at this; simpa using this
  have hb' : (b.mag : ℝ) ≤ 16 * 2 ^ 56 := by
    have := (show ((b.mag : ℤ) : ℝ) ≤ (((16 * SC : ℤ)) : ℝ) by exact_mod_cast hb)
    rw [Int.cast_mul, hSC] at this; simpa using this
  have hxa : |x| ≤ 16 := by
    have : |x| * 2 ^ 56 ≤ 16 * 2 ^ 56 := le_trans hbx.2.2 ha'
    exact le_of_mul_le_mul_right this (by norm_num)
  have hyb : |y| ≤ 16 := by
    have : |y| * 2 ^ 56 ≤ 16 * 2 ^ 56 := le_trans hby.2.2 hb'
    exact le_of_mul_le_mul_right this (by norm_num)
  have hs : InFF e (x + y) (a.add b) := by
    unfold InFF at hx hy ⊢
    simp only [FF.add]
    rw [linValI_zipWith_add e a.t b.t 0 hlen]
    push_cast
    have e1 : (x + y) * 2 ^ 56 - (((a.c : ℝ) + b.c) + (linValI a.t e 0 + linValI b.t e 0))
        = (x * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0)) + (y * 2 ^ 56 - ((b.c : ℝ) + linValI b.t e 0)) := by
      ring
    rw [e1]
    exact le_trans (abs_add_le _ _) (add_le_add hx hy)
  have hxy : |x + y| ≤ M := by
    have := hC.M1
    have h40 : (2 : ℝ) ^ 40 ≥ 32 := by norm_num
    calc |x + y| ≤ |x| + |y| := abs_add_le _ _
      _ ≤ 32 := by linarith
      _ ≤ M := by linarith
  have hf := hC.rnd.err (x + y) hxy
  exact wide_round hC e he (x + y) (fl (x + y)) (a.add b) hs hf

/-! ### relu -/

theorem map_floor_err (e : ℕ → ℝ) (he : Sym e) (lam : ℤ) : ∀ (t : List ℤ) (k : ℕ),
    |(lam : ℝ) / 2 ^ 20 * linValI t e k - linValI (t.map (fun x => lam * x / 2 ^ 20)) e k|
      ≤ (t.length : ℝ) := by
  intro t
  induction t with
  | nil => intro k; simp [linValI]
  | cons x l ih =>
    intro k
    have hf := floor_facts (lam * x) (2 ^ 20) (by norm_num)
    have e20 : ((2 ^ 20 : ℤ) : ℝ) = 2 ^ 20 := by norm_num
    rw [e20, Int.cast_mul] at hf
    simp only [List.map_cons, linValI, List.length_cons]
    push_cast
    have h1 : |(lam : ℝ) / 2 ^ 20 * x - ((lam * x / 2 ^ 20 : ℤ) : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [hf.1, hf.2]
    have h2 : |((lam : ℝ) / 2 ^ 20 * x - ((lam * x / 2 ^ 20 : ℤ) : ℝ)) * e k| ≤ 1 := by
      rw [abs_mul]
      calc _ ≤ 1 * 1 := mul_le_mul h1 (he k) (abs_nonneg _) zero_le_one
        _ = 1 := by norm_num
    have h3 := ih (k + 1)
    have e1 : (lam : ℝ) / 2 ^ 20 * ((x : ℝ) * e k + linValI l e (k + 1))
          - (((lam * x / 2 ^ 20 : ℤ) : ℝ) * e k + linValI (l.map (fun x => lam * x / 2 ^ 20)) e (k + 1))
        = ((lam : ℝ) / 2 ^ 20 * x - ((lam * x / 2 ^ 20 : ℤ) : ℝ)) * e k
          + ((lam : ℝ) / 2 ^ 20 * linValI l e (k + 1)
              - linValI (l.map (fun x => lam * x / 2 ^ 20)) e (k + 1)) := by ring
    rw [e1]
    have := abs_add_le (((lam : ℝ) / 2 ^ 20 * x - ((lam * x / 2 ^ 20 : ℤ) : ℝ)) * e k)
      ((lam : ℝ) / 2 ^ 20 * linValI l e (k + 1)
              - linValI (l.map (fun x => lam * x / 2 ^ 20)) e (k + 1))
    linarith

theorem relu_scale (v : ℝ) : Lane4.relu (v * 2 ^ 56) = Lane4.relu v * 2 ^ 56 := by
  show max (v * 2 ^ 56) 0 = max v 0 * 2 ^ 56
  rcases le_total v 0 with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]; ring
  · rw [max_eq_left h, max_eq_left (mul_nonneg h (by norm_num))]

theorem reluF_mid_eq (p : FF) (h1 : ¬ 0 ≤ p.c - p.dev) (h2 : ¬ p.c + p.dev ≤ 0) :
    ∃ lam mu : ℤ, lam = (p.c + p.dev) * 2 ^ 20 / ((p.c + p.dev) - (p.c - p.dev)) ∧
      mu = cdiv (max (-(lam * (p.c - p.dev))) ((2 ^ 20 - lam) * (p.c + p.dev))) (2 ^ 21) ∧
      reluF p = ⟨lam * p.c / 2 ^ 20 + mu, p.t.map (fun x => lam * x / 2 ^ 20),
        cdiv (lam * p.r) (2 ^ 20) + ((p.t.length : ℤ) + 1) + mu⟩ :=
  ⟨_, _, rfl, rfl, by unfold reluF; exact (if_neg h1).trans (if_neg h2)⟩

theorem relu_f_sound : ReluFSound := by
  intro e v p he hv
  have hd := inff_dev e v p he hv
  obtain ⟨hdl, hdu⟩ := abs_le.mp hd
  by_cases h1 : 0 ≤ p.c - p.dev
  · have e1 : reluF p = p := by unfold reluF; exact if_pos h1
    rw [e1]
    refine ⟨?_, rfl⟩
    have h0 : (0 : ℝ) ≤ v := by
      have : (0 : ℝ) ≤ (p.c : ℝ) - p.dev := by exact_mod_cast h1
      by_contra hneg
      push_neg at hneg
      linarith
    have : Lane4.relu v = v := max_eq_left h0
    rw [this]; exact hv
  by_cases h2 : p.c + p.dev ≤ 0
  · have e1 : reluF p = zeroF p.t.length := by unfold reluF; exact (if_neg h1).trans (if_pos h2)
    rw [e1]
    refine ⟨?_, by simp [zeroF]⟩
    have h2' : (p.c : ℝ) + p.dev ≤ 0 := by exact_mod_cast h2
    have hv0 : v ≤ 0 := by
      by_contra hneg
      push_neg at hneg
      linarith
    have : Lane4.relu v = 0 := max_eq_right hv0
    rw [this]
    unfold InFF zeroF
    simp [linValI_replicate]
  · have h2' : 0 < p.c + p.dev := by omega
    have h1' : p.c - p.dev < 0 := by omega
    obtain ⟨lam, mu, hlam, hmu, hrf⟩ := reluF_mid_eq p h1 h2
    rw [hrf]
    refine ⟨?_, by simp⟩
    have hden : 0 < (p.c + p.dev) - (p.c - p.dev) := by omega
    have hlam0 : 0 ≤ lam := by
      rw [hlam]; exact Int.ediv_nonneg (by linarith) hden.le
    have hC1 : (p.c : ℝ) - p.dev < 0 := by exact_mod_cast h1'
    have hC2 : 0 < (p.c : ℝ) + p.dev := by exact_mod_cast h2'
    have hdenR : (0 : ℝ) < ((p.c : ℝ) + p.dev) - ((p.c : ℝ) - p.dev) := by
      have : (0 : ℝ) < (((p.c + p.dev) - (p.c - p.dev) : ℤ) : ℝ) := by exact_mod_cast hden
      push_cast at this; exact this
    have hlam1 : (lam : ℝ) ≤ 2 ^ 20 := by
      have hf := floor_facts ((p.c + p.dev) * 2 ^ 20) ((p.c + p.dev) - (p.c - p.dev)) hden
      have hlamR : (lam : ℝ) ≤ (((p.c + p.dev) * 2 ^ 20 : ℤ) : ℝ)
          / ((((p.c + p.dev) - (p.c - p.dev) : ℤ)) : ℝ) := by
        rw [hlam]; exact hf.1
      push_cast at hlamR
      refine le_trans hlamR ?_
      rw [div_le_iff₀ hdenR]
      nlinarith
    have hlam0R : (0 : ℝ) ≤ lam := by exact_mod_cast hlam0
    -- the max
    obtain ⟨Mi, hMi⟩ : ∃ Mi : ℤ, Mi = max (-(lam * (p.c - p.dev))) ((2 ^ 20 - lam) * (p.c + p.dev)) :=
      ⟨_, rfl⟩
    rw [← hMi] at hmu
    have hMi1 : -(lam * (p.c - p.dev)) ≤ Mi := by rw [hMi]; exact le_max_left _ _
    have hMi2 : (2 ^ 20 - lam) * (p.c + p.dev) ≤ Mi := by rw [hMi]; exact le_max_right _ _
    have hMi1' : -((lam : ℝ) * ((p.c : ℝ) - p.dev)) ≤ (Mi : ℝ) := by exact_mod_cast hMi1
    have hMi2' : (2 ^ 20 - (lam : ℝ)) * ((p.c : ℝ) + p.dev) ≤ (Mi : ℝ) := by exact_mod_cast hMi2
    have hmu' := cdiv_facts Mi (2 ^ 21) (by norm_num)
    rw [← hmu] at hmu'
    have e21 : ((2 ^ 21 : ℤ) : ℝ) = 2 ^ 21 := by norm_num
    rw [e21] at hmu'
    -- relu_mid
    have hΛ0 : (0 : ℝ) ≤ (lam : ℝ) / 2 ^ 20 := by positivity
    have hΛ1 : (lam : ℝ) / 2 ^ 20 ≤ 1 := by rw [div_le_one (by norm_num)]; exact hlam1
    have hlo' : (p.c : ℝ) - p.dev ≤ v * 2 ^ 56 := by linarith
    have hhi' : v * 2 ^ 56 ≤ (p.c : ℝ) + p.dev := by linarith
    obtain ⟨hm1, hm2⟩ := Lane4.R8KE.relu_mid (v * 2 ^ 56) ((p.c : ℝ) - p.dev) ((p.c : ℝ) + p.dev)
      ((lam : ℝ) / 2 ^ 20) hlo' hhi' hΛ0 hΛ1
    have hmx : max (-((lam : ℝ) / 2 ^ 20 * ((p.c : ℝ) - p.dev)))
        ((1 - (lam : ℝ) / 2 ^ 20) * ((p.c : ℝ) + p.dev)) ≤ 2 * (mu : ℝ) := by
      apply max_le
      · nlinarith [hmu'.1]
      · nlinarith [hmu'.1]
    rw [relu_scale] at hm1 hm2
    have hA : |Lane4.relu v * 2 ^ 56 - (lam : ℝ) / 2 ^ 20 * (v * 2 ^ 56) - mu| ≤ mu := by
      rw [abs_le]; constructor <;> linarith
    -- the pieces
    have hF3 := floor_facts (lam * p.c) (2 ^ 20) (by norm_num)
    have e20 : ((2 ^ 20 : ℤ) : ℝ) = 2 ^ 20 := by norm_num
    rw [e20, Int.cast_mul] at hF3
    have hF5 := cdiv_facts (lam * p.r) (2 ^ 20) (by norm_num)
    rw [e20, Int.cast_mul] at hF5
    have hD := map_floor_err e he lam p.t 0
    unfold InFF at hv ⊢
    show |Lane4.relu v * 2 ^ 56 - ((((lam * p.c / 2 ^ 20 + mu : ℤ)) : ℝ)
        + linValI (p.t.map (fun x => lam * x / 2 ^ 20)) e 0)|
        ≤ (((cdiv (lam * p.r) (2 ^ 20) + ((p.t.length : ℤ) + 1) + mu : ℤ)) : ℝ)
    push_cast
    have hB : |(lam : ℝ) / 2 ^ 20 * (v * 2 ^ 56 - ((p.c : ℝ) + linValI p.t e 0))|
        ≤ (lam : ℝ) / 2 ^ 20 * (p.r : ℝ) := by
      rw [abs_mul, abs_of_nonneg hΛ0]
      exact mul_le_mul_of_nonneg_left hv hΛ0
    obtain ⟨hA1, hA2⟩ := abs_le.mp hA
    obtain ⟨hB1, hB2⟩ := abs_le.mp hB
    obtain ⟨hD1, hD2⟩ := abs_le.mp hD
    rw [abs_le]
    constructor <;> nlinarith [hF3.1, hF3.2, hF5.1, hF5.2]

/-! ### residual rows -/

theorem unit_val (e : ℕ → ℝ) (k : ℕ) (v : ℤ) : ∀ n : ℕ,
    linValI ((List.range n).map (fun j => if j = k then v else 0)) e 0
      = if k < n then (v : ℝ) * e k else 0 := by
  intro n
  induction n with
  | zero => simp [linValI]
  | succ n ih =>
    rw [List.range_succ, List.map_append, linValI_append, ih]
    simp only [List.map_cons, List.map_nil, List.length_map, List.length_range, linValI]
    by_cases hnk : n = k
    · subst hnk
      simp
    · have : ¬ k = n := fun h => hnk h.symm
      simp [hnk]
      by_cases hk : k < n
      · simp [hk, Nat.lt_succ_of_lt hk]
      · have : ¬ k < n + 1 := by omega
        simp [hk, this]

theorem linI_unit_aux (k : ℕ) (v : ℤ) : ∀ n : ℕ,
    linI ((List.range n).map (fun j => if j = k then v else 0)) ≤ (if k < n then iabs v else 0) := by
  intro n
  induction n with
  | zero => simp [linI_nil']
  | succ n ih =>
    rw [List.range_succ, List.map_append, linI_append]
    have h1 : linI (List.map (fun j => if j = k then v else 0) [n]) = iabs (if n = k then v else 0) := by
      simp [linI_eq]
    rw [h1]
    by_cases hnk : n = k
    · subst hnk
      simp at ih
      simp
      omega
    · have h0 : iabs (0 : ℤ) = 0 := by simp [iabs]
      simp only [hnk, if_false, h0]
      by_cases hk : k < n
      · simp [hk] at ih
        have : k < n + 1 := by omega
        simp [this]
        exact ih
      · have : ¬ k < n + 1 := by omega
        simp [hk] at ih
        simp [this]
        exact ih

theorem unitL_val (e : ℕ → ℝ) (ns k : ℕ) (v : ℤ) (hk : k < ns) :
    linValI (unitL ns k v) e 0 = (v : ℝ) * e k := by
  unfold unitL
  rw [unit_val e k v ns]
  simp [hk]

theorem unitL_linI (ns k : ℕ) (v : ℤ) : linI (unitL ns k v) ≤ iabs v := by
  unfold unitL
  have := linI_unit_aux k v ns
  have h0 := iabs_nonneg' v
  split_ifs at this <;> omega

theorem unitL_length (ns k : ℕ) (v : ℤ) : (unitL ns k v).length = ns := by simp [unitL]

theorem unitL_getD_ne (ns k j : ℕ) (v : ℤ) (h : j ≠ k) : (unitL ns k v).getD j 0 = 0 := by
  by_cases hj : j < ns
  · simp [unitL, List.getD_eq_getElem?_getD, hj, h]
  · simp [unitL, List.getD_eq_getElem?_getD, hj]

theorem intL_cons (q : ℚ) (l : List ℚ) : intL (q :: l) = floorQ q :: intL l := rfl

theorem aswRow_length (fl : ℝ → ℝ) (d : ℕ → ℝ) : ∀ (l : List ℚ) (j : ℕ), (aswRow fl l d j).length = l.length := by
  intro l
  induction l with
  | nil => intro j; simp [aswRow]
  | cons a l ih => intro j; simp [aswRow, ih]

theorem resF_length (dI : ℤ) (ns : ℕ) : ∀ (l : List ℤ) (j : ℕ), (resF dI ns l j).length = l.length := by
  intro l
  induction l with
  | nil => intro j; simp [resF]
  | cons a l ih => intro j; simp [resF, ih]

theorem resF_mem (dI : ℤ) (ns : ℕ) : ∀ (l : List ℤ) (j : ℕ) (x : FF), x ∈ resF dI ns l j →
    ∃ a ∈ l, ∃ i, i < l.length ∧ x = ⟨a, unitL ns (j + i) dI, chg (iabs a + dI)⟩ := by
  intro l
  induction l with
  | nil => intro j x hx; simp [resF] at hx
  | cons a l ih =>
    intro j x hx
    simp only [resF, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact ⟨a, by simp, 0, by simp, by rw [hx]; simp⟩
    · obtain ⟨b, hb, i, hi, hxe⟩ := ih (j + 1) x hx
      refine ⟨b, List.mem_cons_of_mem _ hb, i + 1, by simp; omega, ?_⟩
      rw [hxe, show j + 1 + i = j + (i + 1) by omega]

theorem e0_facts (δ d : ℝ) (hδ : 0 ≤ δ) (hd : |d| ≤ δ) :
    |(if δ = 0 then 0 else d / δ)| ≤ 1 ∧ δ * (if δ = 0 then 0 else d / δ) = d := by
  by_cases h : δ = 0
  · subst h
    have : d = 0 := abs_nonpos_iff.mp (by simpa using hd)
    simp [this]
  · simp only [h, if_false]
    have hpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm h)
    refine ⟨?_, by field_simp⟩
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hd

theorem res_entry {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hgδ : gridOK δ = true) (q : ℚ) (dd : ℝ) (hdd : |dd| ≤ (δ : ℝ)) (hq : qabs q ≤ 15)
    (hgq : gridOK q = true) (ns i : ℕ) (hi : i < ns) (e : ℕ → ℝ)
    (hei : ((floorQ δ : ℤ) : ℝ) * e i = dd * 2 ^ 56) :
    InFF e (asw fl q dd) ⟨floorQ q, unitL ns i (floorQ δ), chg (iabs (floorQ q) + floorQ δ)⟩ := by
  have hfq := floorQ_grid q hgq
  have hfd := floorQ_grid δ hgδ
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ1
  have hq' : |(q : ℝ)| ≤ 15 := by
    have := zqabs_cast q
    have h2 : ((qabs q : ℚ) : ℝ) ≤ 15 := by exact_mod_cast hq
    rw [this] at h2; exact h2
  unfold InFF asw
  show |fl ((q : ℝ) + dd) * 2 ^ 56 - (((floorQ q : ℤ) : ℝ) + linValI (unitL ns i (floorQ δ)) e 0)|
      ≤ ((chg (iabs (floorQ q) + floorQ δ) : ℤ) : ℝ)
  rw [unitL_val e ns i _ hi, hfq, hei]
  have hz : |(q : ℝ) + dd| ≤ M := by
    have := hC.M1
    have : (2 : ℝ) ^ 40 ≥ 16 := by norm_num
    calc |(q : ℝ) + dd| ≤ |(q : ℝ)| + |dd| := abs_add_le _ _
      _ ≤ 16 := by linarith
      _ ≤ M := by linarith [hC.M1]
  have hf := hC.rnd.err _ hz
  have hm : |(q : ℝ) + dd| * 2 ^ 56 ≤ (((iabs (floorQ q) + floorQ δ : ℤ)) : ℝ) := by
    push_cast
    rw [iabs_cast, hfq, hfd]
    have h1 : |(q : ℝ) * 2 ^ 56| = |(q : ℝ)| * 2 ^ 56 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
    rw [h1]
    have h2 : |(q : ℝ) + dd| ≤ |(q : ℝ)| + (δ : ℝ) := le_trans (abs_add_le _ _) (by linarith)
    nlinarith
  have h1 := round_chg hC.u0 hC.u1 hC.h0 hC.h1 _ _ hm
  have e1 : fl ((q : ℝ) + dd) * 2 ^ 56 - ((q : ℝ) * 2 ^ 56 + dd * 2 ^ 56)
      = (fl ((q : ℝ) + dd) - ((q : ℝ) + dd)) * 2 ^ 56 := by ring
  rw [e1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
  exact le_trans (mul_le_mul_of_nonneg_right hf (by norm_num)) h1

theorem res_pw {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (hgδ : gridOK δ = true) (ns : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ (δ : ℝ)) (e : ℕ → ℝ)
    (n : ℕ) (hn : n ≤ ns) (hei : ∀ i, i < n → ((floorQ δ : ℤ) : ℝ) * e i = d i * 2 ^ 56) :
    ∀ (row : List ℚ) (j : ℕ), (∀ q ∈ row, qabs q ≤ 15 ∧ gridOK q = true) → j + row.length ≤ n →
      ∀ k, k < row.length →
        InFF e ((aswRow fl row d j).getD k 0) ((resF (floorQ δ) ns (intL row) j).getD k (zeroF 0)) := by
  intro row
  induction row with
  | nil => intro j _ _ k hk; simp at hk
  | cons q l ih =>
    intro j hq hj k hk
    cases k with
    | zero =>
      simp only [aswRow, intL_cons, resF, List.getD_cons_zero]
      simp only [List.length_cons] at hj
      exact res_entry hC δ hδ0 hδ1 hgδ q (d j) (hd j) (hq q (by simp)).1 (hq q (by simp)).2 ns j
        (by omega) e (hei j (by omega))
    | succ k' =>
      simp only [aswRow, intL_cons, resF, List.getD_cons_succ]
      simp only [List.length_cons] at hj hk
      exact ih (j + 1) (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')) (by omega) k' (by omega)

theorem mag_bound (A D U : ℤ) (hA : 0 ≤ A) (hA2 : A ≤ 15 * 2 ^ 56) (hD0 : 0 ≤ D) (hD : D ≤ 2 ^ 55)
    (hU : U ≤ D) : A + (U + chg (A + D)) ≤ 16 * SC := by
  unfold chg SC
  omega

theorem res_f_sound : ResFSound := by
  intro u η M fl hC δ hδ0 hδ1 hgδ ns row d hd hsm hgrid hlen
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ1
  have hmem : ∀ q ∈ row, qabs q ≤ 15 ∧ gridOK q = true := fun q hq =>
    ⟨zsmallQ_mem hsm q hq, List.all_eq_true.mp hgrid q hq⟩
  have hfd := floorQ_grid δ hgδ
  refine ⟨fun k => if (δ : ℝ) = 0 then 0 else d k / (δ : ℝ), ?_, ?_, ?_, ?_⟩
  · intro k; exact (e0_facts (δ : ℝ) (d k) hδR0 (hd k)).1
  · intro e hag
    have hei : ∀ i, i < row.length → ((floorQ δ : ℤ) : ℝ) * e i = d i * 2 ^ 56 := by
      intro i hi
      rw [hag i hi, hfd]
      have := (e0_facts (δ : ℝ) (d i) hδR0 (hd i)).2
      calc (δ : ℝ) * 2 ^ 56 * (if (δ : ℝ) = 0 then 0 else d i / (δ : ℝ))
          = ((δ : ℝ) * (if (δ : ℝ) = 0 then 0 else d i / (δ : ℝ))) * 2 ^ 56 := by ring
        _ = d i * 2 ^ 56 := by rw [this]
    refine ⟨?_, ?_⟩
    · rw [aswRow_length, resF_length]; simp [intL]
    · intro k hk
      rw [aswRow_length] at hk
      exact res_pw hC δ hδ0 hδ1 hgδ ns d hd e row.length hlen hei row 0 hmem (by omega) k hk
  · intro x hx
    obtain ⟨a, ha, i, hi, hxe⟩ := resF_mem (floorQ δ) ns (intL row) 0 x hx
    have ha' : a ∈ row.map floorQ := ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha'
    have hqs := hmem q hq
    have hq' : |(q : ℝ)| ≤ 15 := by
      have := zqabs_cast q
      have h2 : ((qabs q : ℚ) : ℝ) ≤ 15 := by exact_mod_cast hqs.1
      rw [this] at h2; exact h2
    have hfq := floorQ_grid q hqs.2
    have hA2 : |floorQ q| ≤ 15 * 2 ^ 56 := by
      have : |((floorQ q : ℤ) : ℝ)| ≤ 15 * 2 ^ 56 := by
        rw [hfq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
        nlinarith
      exact_mod_cast this
    have hD0 : 0 ≤ floorQ δ := by
      have : (0 : ℝ) ≤ ((floorQ δ : ℤ) : ℝ) := by rw [hfd]; positivity
      exact_mod_cast this
    have hD1 : floorQ δ ≤ 2 ^ 55 := by
      have : ((floorQ δ : ℤ) : ℝ) ≤ 2 ^ 55 := by rw [hfd]; nlinarith
      exact_mod_cast this
    rw [hxe]
    refine ⟨unitL_length _ _ _, ?_⟩
    have hU := unitL_linI ns (0 + i) (floorQ δ)
    have hiD : iabs (floorQ δ) = floorQ δ := by rw [iabs_eq']; exact abs_of_nonneg hD0
    have hiA : iabs (floorQ q) = |floorQ q| := iabs_eq' _
    show iabs (floorQ q) + (linI (unitL ns (0 + i) (floorQ δ)) + chg (iabs (floorQ q) + floorQ δ)) ≤ 16 * SC
    exact mag_bound (iabs (floorQ q)) (floorQ δ) _ (iabs_nonneg' _) (by rw [hiA]; exact hA2) hD0 hD1
      (by rw [← hiD]; exact hU)
  · intro x hx
    obtain ⟨a, ha, i, hi, hxe⟩ := resF_mem (floorQ δ) ns (intL row) 0 x hx
    rw [hxe]
    have hi' : i < row.length := by simpa [intL] using hi
    show ((unitL ns (0 + i) (floorQ δ)).drop row.length).all (fun v => v == 0) = true
    apply zf_of
    intro k hk
    exact unitL_getD_ne ns (0 + i) k _ (by omega)

/-! ### head output -/

theorem floor_err_list (e : ℕ → ℝ) (he : Sym e) : ∀ (t : List ℚ) (k : ℕ),
    |2 ^ 56 * linVal t e k - linValI (t.map floorQ) e k| ≤ (t.length : ℝ) := by
  intro t
  induction t with
  | nil => intro k; simp [linVal, linValI]
  | cons q l ih =>
    intro k
    simp only [List.map_cons, linVal, linValI, List.length_cons]
    push_cast
    obtain ⟨hf1, hf2⟩ := floorQ_facts q
    have h1 : |(2 ^ 56 * (q : ℝ) - ((floorQ q : ℤ) : ℝ))| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have h2 : |(2 ^ 56 * (q : ℝ) - ((floorQ q : ℤ) : ℝ)) * e k| ≤ 1 := by
      rw [abs_mul]
      calc _ ≤ 1 * 1 := mul_le_mul h1 (he k) (abs_nonneg _) zero_le_one
        _ = 1 := by norm_num
    have h3 := ih (k + 1)
    have e1 : 2 ^ 56 * ((q : ℝ) * e k + linVal l e (k + 1))
          - (((floorQ q : ℤ) : ℝ) * e k + linValI (l.map floorQ) e (k + 1))
        = (2 ^ 56 * (q : ℝ) - ((floorQ q : ℤ) : ℝ)) * e k
          + (2 ^ 56 * linVal l e (k + 1) - linValI (l.map floorQ) e (k + 1)) := by ring
    rw [e1]
    have := abs_add_le ((2 ^ 56 * (q : ℝ) - ((floorQ q : ℤ) : ℝ)) * e k)
      (2 ^ 56 * linVal l e (k + 1) - linValI (l.map floorQ) e (k + 1))
    linarith

theorem addAt_length : ∀ (l : List ℤ) (k : ℕ) (v : ℤ), (addAt l k v).length = l.length := by
  intro l
  induction l with
  | nil => intro k v; simp [addAt]
  | cons a l ih =>
    intro k v
    cases k with
    | zero => simp [addAt]
    | succ k => simp [addAt, ih]

theorem addAt_getD_ne : ∀ (l : List ℤ) (slot k : ℕ) (v : ℤ), k ≠ slot →
    (addAt l slot v).getD k 0 = l.getD k 0 := by
  intro l
  induction l with
  | nil => intro slot k v h; simp [addAt]
  | cons a l ih =>
    intro slot k v h
    cases slot with
    | zero =>
      cases k with
      | zero => exact absurd rfl h
      | succ k' => simp [addAt]
    | succ s' =>
      cases k with
      | zero => simp [addAt]
      | succ k' =>
        simp only [addAt, List.getD_cons_succ]
        exact ih s' k' v (by omega)

theorem linValI_addAt (e : ℕ → ℝ) : ∀ (l : List ℤ) (s k : ℕ) (v : ℤ), k < l.length →
    linValI (addAt l k v) e s = linValI l e s + (v : ℝ) * e (s + k) := by
  intro l
  induction l with
  | nil => intro s k v h; simp at h
  | cons a l ih =>
    intro s k v h
    cases k with
    | zero => simp [addAt, linValI]; ring
    | succ k' =>
      simp only [addAt, linValI]
      rw [ih (s + 1) k' v (by simpa using h)]
      rw [show s + 1 + k' = s + (k' + 1) by omega]
      ring

theorem ho_core (e : ℕ → ℝ) (v : ℝ) (fa : ℤ) (T : List ℤ) (C : ℤ) (slot hB ns : ℕ) (hC : 1 ≤ C)
    (hlen : T.length = ns) (hsl : slot < ns) (hz : ∀ k, hB ≤ k → T.getD k 0 = 0)
    (hN : |v * 2 ^ 56 - ((fa : ℝ) + linValI T e 0)| ≤ (C : ℝ)) :
    ∃ s : ℝ, |s| ≤ 1 ∧
      (∀ e' : ℕ → ℝ, AgreeBelow hB e e' → e' slot = s → InFF e' v ⟨fa, addAt T slot C, 0⟩)
      ∧ (addAt T slot C).length = ns
      ∧ ∀ k, hB ≤ k → k ≠ slot → (addAt T slot C).getD k 0 = 0 := by
  have hCR : (0 : ℝ) < C := by
    have : (0 : ℤ) < C := by omega
    exact_mod_cast this
  refine ⟨(v * 2 ^ 56 - ((fa : ℝ) + linValI T e 0)) / C, ?_, ?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hCR, div_le_one hCR]; exact hN
  · intro e' hag hes
    have hfr : linValI T e' 0 = linValI T e 0 := by
      apply linValI_frame e e' T 0
      intro i _ hne
      simp only [Nat.sub_zero]
      apply hz
      by_contra hlt
      push_neg at hlt
      exact hne (hag i hlt)
    show |v * 2 ^ 56 - (((fa : ℤ) : ℝ) + linValI (addAt T slot C) e' 0)| ≤ (((0 : ℤ)) : ℝ)
    rw [linValI_addAt e' T 0 slot C (by omega), hfr, Nat.zero_add, hes]
    have : v * 2 ^ 56 - ((fa : ℝ) + (linValI T e 0
        + (C : ℝ) * ((v * 2 ^ 56 - ((fa : ℝ) + linValI T e 0)) / C))) = 0 := by
      field_simp; ring
    rw [this]; simp
  · rw [addAt_length]; exact hlen
  · intro k hk hne
    rw [addAt_getD_ne _ _ _ _ hne]; exact hz k hk

theorem ho_num (e : ℕ → ℝ) (he : Sym e) (v : ℝ) (a : AF) (pre : ℕ) (rest : List ℚ) (ns n8 : ℕ)
    (hv : InAF e v a) (hat : a.t = List.replicate pre 0 ++ rest) (hrest : rest.length ≤ n8) :
    |v * 2 ^ 56 - (((floorQ a.c : ℤ) : ℝ) + linValI (padTo ns (a.t.map floorQ)) e 0)|
        ≤ ((ceilQ a.r + 1 + (n8 : ℤ) : ℤ) : ℝ) ∧ 0 ≤ ceilQ a.r := by
  unfold InAF at hv
  have hr0 : (0 : ℝ) ≤ ((a.r : ℚ) : ℝ) := le_trans (abs_nonneg _) hv
  have hcq := ceilQ_facts a.r
  have hc0 : 0 ≤ ceilQ a.r := by
    have : (0 : ℝ) ≤ ((ceilQ a.r : ℤ) : ℝ) := le_trans (mul_nonneg hr0 (by norm_num)) hcq
    exact_mod_cast this
  refine ⟨?_, hc0⟩
  have hLT : linValI (padTo ns (a.t.map floorQ)) e 0 = linValI (rest.map floorQ) e pre := by
    unfold padTo
    rw [linValI_append, linValI_replicate, add_zero, hat, List.map_append, List.map_replicate,
      floorQ_zero, linValI_pre]
    simp
  have hL : linVal a.t e 0 = linVal rest e pre := by
    rw [hat, linVal_pre]; simp
  rw [hLT]
  rw [hL] at hv
  have herr := floor_err_list e he rest pre
  obtain ⟨hfa1, hfa2⟩ := floorQ_facts a.c
  have hrestR : (rest.length : ℝ) ≤ n8 := by exact_mod_cast hrest
  have h1 : |2 ^ 56 * (v - (((a.c : ℚ) : ℝ) + linVal rest e pre))| ≤ 2 ^ 56 * ((a.r : ℚ) : ℝ) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
    exact mul_le_mul_of_nonneg_left hv (by norm_num)
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  obtain ⟨h21, h22⟩ := abs_le.mp herr
  push_cast
  rw [abs_le]
  constructor <;> nlinarith

theorem ho_f_sound : HoFSound := by
  intro e v a pre rest ns hB slot n8 he hv hat hrest hBs hsl hg
  have hF : (hoF ns hB slot (n8 : ℤ) a).2
      = ⟨floorQ a.c, addAt (padTo ns (a.t.map floorQ)) slot (ceilQ a.r + 1 + (n8 : ℤ)), 0⟩ := rfl
  have hg' : (zeroFrom hB ⟨floorQ a.c, padTo ns (a.t.map floorQ), 0⟩
      && ((⟨floorQ a.c, padTo ns (a.t.map floorQ), 0⟩ : FF).t.length == ns)) = true := hg
  rw [Bool.and_eq_true, beq_iff_eq] at hg'
  obtain ⟨hz, hlenT⟩ := hg'
  have hlenT' : (padTo ns (a.t.map floorQ)).length = ns := hlenT
  have hz' : ∀ k, hB ≤ k → (padTo ns (a.t.map floorQ)).getD k 0 = 0 :=
    fun k hk => zf_aux _ hB k hz hk
  obtain ⟨hN, hc0⟩ := ho_num e he v a pre rest ns n8 hv hat hrest
  have hC1 : 1 ≤ ceilQ a.r + 1 + (n8 : ℤ) := by omega
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := ho_core e v (floorQ a.c) (padTo ns (a.t.map floorQ))
    (ceilQ a.r + 1 + (n8 : ℤ)) slot hB ns hC1 hlenT' hsl hz' hN
  rw [hF]
  exact ⟨s, hs1, hs2, hs3, hs4⟩

end Lane4.Case
