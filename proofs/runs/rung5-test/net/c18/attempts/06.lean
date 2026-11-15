namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.style.longLine false

def z10 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def embRows : List (List ℚ) :=
  [[0, 0, 0, 0, 0, 0, 0],
   [0, 1, 1, 0, 1, 0, 0],
   [1, 0, 0, 1, 2, 0, 0],
   [1, 0, 0, 1, 2, 0, 0],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 1, 0, 1, 2, 0, 0]]

def rowS : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 20, 0]
def rowP : List ℚ := [0, -50, 0, 0, 0, 0, 0, 0, 0, 0]
def rowT : List ℚ := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z10, z10, z10, z10, z10, z10, z10, rowS, z10, rowP],
    V := [z10, z10, z10, z10, z10, rowT, z10, z10, z10, z10],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd],
    W1 := [[0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0]],
    b1 := [-2, -2],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, -2], [0, 0], [0, 0], [0, 0]],
    b2 := z10 }

def net : TNet :=
  { embed := embRows,
    blocks := [blk],
    outW := [0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    outB := 0 }

def embq (t c : ℕ) : ℚ := (embRows.getD t []).getD c 0

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (t c : ℕ) : ℝ := sw fl (embq t c) (p.E t c)

def gq (t : ℕ) : ℕ := if t = 2 ∨ t = 3 then 1 else 0

theorem tok_le5 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ev fl p (tokAt w j) 0, ev fl p (tokAt w j) 1, ev fl p (tokAt w j) 2,
      ev fl p (tokAt w j) 3, ev fl p (tokAt w j) 4, 0, 0, 1, fl (j : ℝ),
      fl (((w.length + 1 : ℕ)) : ℝ)] := by
  have h6 := tok_le5 w hw j
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨ tokAt w j = 5 := by omega
  rcases h3 with h | h | h | h | h | h <;>
    simp [TNet.init, net, embRows, swRow, pos, ev, embq, h, sw_zero hr, hr.one]


theorem carry_snoc (l : List ℕ) (t : ℕ) :
    carry (l ++ [t]) = if cls t = 2 then carry l else cls t := by
  simp [carry, List.foldl_append]

theorem carry_win (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ m, m ≤ w.length → ∃ j, j < m + 1 ∧ ¬ (tokAt w j = 1 ∨ tokAt w j = 5) ∧
      (∀ k, j < k → k < m + 1 → (tokAt w k = 1 ∨ tokAt w k = 5)) ∧
      gq (tokAt w j) = carry (w.take m) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, by omega, ?_, ?_, ?_⟩
    · simp [Lane4.Seq.tokAt_zero]
    · intro k h1 h2; omega
    · simp [Lane4.Seq.tokAt_zero, gq, carry]
  | succ m ih =>
    intro hle
    obtain ⟨j, hj, hnp, hall, hc⟩ := ih (by omega)
    have hm : m < w.length := by omega
    have htk : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m hm
    have htake : w.take (m + 1) = w.take m ++ [w[m]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hm]
      rfl
    have hb := hw _ (List.getElem_mem hm)
    have hcar : carry (w.take (m + 1)) = if cls w[m] = 2 then carry (w.take m) else cls w[m] := by
      rw [htake, carry_snoc]
    by_cases hp : w[m] = 1 ∨ w[m] = 5
    · have h2 : cls w[m] = 2 := by
        rcases hp with h | h <;> simp [cls, h]
      refine ⟨j, by omega, hnp, ?_, ?_⟩
      · intro k hk1 hk2
        by_cases hk : k = m + 1
        · subst hk; rw [htk]; exact hp
        · exact hall k hk1 (by omega)
      · rw [hcar, if_pos h2]; exact hc
    · refine ⟨m + 1, by omega, ?_, ?_, ?_⟩
      · rw [htk]; exact hp
      · intro k hk1 hk2; omega
      · rw [hcar, htk]
        have h4 : w[m] = 2 ∨ w[m] = 3 ∨ w[m] = 4 := by omega
        rcases h4 with h | h | h <;> simp [cls, gq, h]

theorem tok_get (w : List ℕ) (m : ℕ) : w.getD m 0 = tokAt w (m + 1) := by
  simp [tokAt]


structure Env (u η M : ℝ) (fl : ℝ → ℝ) (n : ℕ) : Prop where
  hr : Rnd u η M fl
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη : η ≤ 1 / 2 ^ 149
  hn : u * (n : ℝ) ≤ 1 / 256
  hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M
  hn1 : 1 ≤ n

theorem Env.rin {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ 2 ^ 40) : C * (n : ℝ) ≤ M := range_lin E.hM E.hn1 hC0 hC

theorem Env.rc {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {C : ℝ}
    (hC : C ≤ 2 ^ 40) : C ≤ M := range_const E.hM E.hn1 hC

theorem Env.nR {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) : (1 : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast E.hn1

/-- rounding error of a small number -/
theorem Env.fs {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x : ℝ} (hx : |x| ≤ 100) :
    |fl x - x| ≤ 1 / 1000 := by
  have h := E.hr.abs E.hu0 hx (E.rc (by norm_num))
  have h1 := eta_tiny E.hη
  have h2 : u * 100 ≤ 1 / 2 ^ 24 * 100 := mul_le_mul_of_nonneg_right E.hu1 (by norm_num)
  have h3 : (1 : ℝ) / 2 ^ 24 * 100 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

/-- rounding error of a number of size at most C*n -/
theorem Env.fsn {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ 100) (hx : |x| ≤ C * n) : |fl x - x| ≤ 1 / 2 := by
  have h := E.hr.abs E.hu0 hx (E.rin hC0 (by linarith))
  have h1 := eta_tiny E.hη
  have h2 : u * (C * (n : ℝ)) = C * (u * n) := by ring
  have h3 : C * (u * (n : ℝ)) ≤ C * (1 / 256) := mul_le_mul_of_nonneg_left E.hn hC0
  have h4 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

/-- fl of fl is fl, for small numbers -/
theorem Env.id100 {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x : ℝ} (hx : |x| ≤ 100) :
    fl (fl x) = fl x := E.hr.idem x (le_trans hx (E.rc (by norm_num)))

theorem Env.idn {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x C : ℝ} (hC0 : 0 ≤ C)
    (hx : |x| ≤ C * n) (hC : C ≤ 2 ^ 40) : fl (fl x) = fl x :=
  E.hr.idem x (le_trans hx (E.rin hC0 hC))

/-- stored weights -/
theorem Env.swa {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) (w : ℚ) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hw : |(w : ℝ)| ≤ 100) :
    |sw fl w d - (w : ℝ)| ≤ 1 / 199 * |(w : ℝ)| + 1 / 10 ^ 40 := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by
    have := E.hu1
    linarith
  have h200 : (200 : ℝ) ≤ M := E.rc (by norm_num)
  have h := sw_near E.hr E.hu0 w hd (by norm_num) (by linarith) hε
  have := eta_tiny E.hη
  linarith

theorem Env.swfix {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) (w : ℚ) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hw : |(w : ℝ)| ≤ 100) : fl (sw fl w d) = sw fl w d := by
  have h200 : (200 : ℝ) ≤ M := E.rc (by norm_num)
  exact fl_sw E.hr w hd (by norm_num) (by linarith)

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 a5 a6 qi qn b0 b1 b2 b3 b4 b5 b6 qk qn' : ℝ)
    (hI1 : fl (fl (sw fl 20 (dA 7 8) * qk)) = fl (sw fl 20 (dA 7 8) * qk))
    (hI2 : fl (fl (sw fl (-50) (dA 9 1) * b1)) = fl (sw fl (-50) (dA 9 1) * b1)) :
    hd.score fl dA [a0, a1, a2, a3, a4, a5, a6, 1, qi, qn] [b0, b1, b2, b3, b4, b5, b6, 1, qk, qn'] =
      fl (fl (sw fl 20 (dA 7 8) * qk) + fl (qn * fl (sw fl (-50) (dA 9 1) * b1))) := by
  simp [Head.score, hd, z10, rowS, rowP, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (b0 b1 b2 b3 b4 b5 b6 qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * b0)) = fl (sw fl 1 (dV 0) * b0)) :
    rdot fl rowT [b0, b1, b2, b3, b4, b5, b6, 1, qk, qn] dV 0 0
      = fl (sw fl 1 (dV 0) * b0) := by
  simp [rowT, rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e f g h i j : ℝ) :
    rdot fl z10 [a, b, c, d, e, f, g, h, i, j] dV 0 0 = 0 := by
  simp [z10, rdot, sw_zero hr, hr.zero]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0, 0, savg fl ex (cand Mask.strict (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl rowT (net.init fl p w j) (p.V 0 0 5) 0 0),
         0, 0, 0, 0] := by
  have hV : hd.V = [z10, z10, z10, z10, z10, rowT, z10, z10, z10, z10] := rfl
  have hm : hd.mask = Mask.strict := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z10 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw]
    exact zrow_eq hr d _ _ _ _ _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ) (i : ℕ)
    (g pf U V A fi fn c hUv hVv : ℝ)
    (hinit : net.init fl p w i = [g, pf, U, V, A, 0, 0, 1, fi, fn])
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0, 0, c, 0, 0, 0, 0])
    (hc : fl c = c) (hu : fl U = U) (hv : fl V = V) (ha : fl A = A)
    (hU1 : fl (fl (sw fl 2 (p.W1 0 0 2) * U)) = fl (sw fl 2 (p.W1 0 0 2) * U))
    (hU2 : fl (fl (fl (sw fl 2 (p.W1 0 0 2) * U) + fl (sw fl 1 (p.W1 0 0 5) * c)))
      = fl (fl (sw fl 2 (p.W1 0 0 2) * U) + fl (sw fl 1 (p.W1 0 0 5) * c)))
    (hV1 : fl (fl (sw fl 2 (p.W1 0 1 3) * V)) = fl (sw fl 2 (p.W1 0 1 3) * V))
    (hV2 : fl (fl (fl (sw fl 2 (p.W1 0 1 3) * V) + fl (sw fl 1 (p.W1 0 1 5) * c)))
      = fl (fl (sw fl 2 (p.W1 0 1 3) * V) + fl (sw fl 1 (p.W1 0 1 5) * c)))
    (hhU : relu (fl (fl (fl (sw fl 2 (p.W1 0 0 2) * U) + fl (sw fl 1 (p.W1 0 0 5) * c))
      + sw fl (-2) (p.b1 0 0))) = hUv)
    (hhV : relu (fl (fl (fl (sw fl 2 (p.W1 0 1 3) * V) + fl (sw fl 1 (p.W1 0 1 5) * c))
      + sw fl (-2) (p.b1 0 1))) = hVv)
    (hW1 : fl (fl (sw fl 1 (p.W2 0 6 0) * hUv)) = fl (sw fl 1 (p.W2 0 6 0) * hUv))
    (hW2 : fl (fl (fl (sw fl 1 (p.W2 0 6 0) * hUv) + fl (sw fl (-2) (p.W2 0 6 1) * hVv)))
      = fl (fl (sw fl 1 (p.W2 0 6 0) * hUv) + fl (sw fl (-2) (p.W2 0 6 1) * hVv)))
    (hO1 : fl (fl (sw fl 1 (p.oW 4) * A)) = fl (sw fl 1 (p.oW 4) * A))
    (hO2 : fl (fl (fl (sw fl 1 (p.oW 4) * A) + fl (sw fl 1 (p.oW 6) *
        fl (fl (sw fl 1 (p.W2 0 6 0) * hUv) + fl (sw fl (-2) (p.W2 0 6 1) * hVv)))))
      = fl (fl (sw fl 1 (p.oW 4) * A) + fl (sw fl 1 (p.oW 6) *
        fl (fl (sw fl 1 (p.W2 0 6 0) * hUv) + fl (sw fl (-2) (p.W2 0 6 1) * hVv))))) :
    sout net fl ex p w i = fl (fl (sw fl 1 (p.oW 4) * A) + fl (sw fl 1 (p.oW 6) *
        fl (fl (sw fl 1 (p.W2 0 6 0) * hUv) + fl (sw fl (-2) (p.W2 0 6 1) * hVv)))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 0, 0, 1, 0, 1, 0, 0, 0] := rfl
  have hc0 : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc0]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn, hinit]
  simp [z10, radd, raffine, rdot, sw_zero hr, hr.zero, hr.one, hc, hu, hv, ha, hU1, hU2, hV1,
    hV2, hhU, hhV, hW1, hW2, hO1, hO2]

theorem Env.nM {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) : (n : ℝ) ≤ M := by
  have := E.rin (C := 1) (by norm_num) (by norm_num)
  linarith

theorem Env.swk {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) (w : ℚ) (x a : ℝ)
    (hwx : (w : ℝ) = x) {d : ℝ} (hd : |d| ≤ 1 / 200) (ha : |x| ≤ a) (ha1 : a ≤ 100) :
    |sw fl w d - x| ≤ 1 / 199 * a + 1 / 10 ^ 40 := by
  have h := E.swa w hd (by rw [hwx]; linarith)
  rw [hwx] at h
  have h2 : 1 / 199 * |x| ≤ 1 / 199 * a := mul_le_mul_of_nonneg_left ha (by norm_num)
  linarith

noncomputable def Aterm (fl : ℝ → ℝ) (Sw : ℝ) (k : ℕ) : ℝ := fl (Sw * fl (k : ℝ))
noncomputable def Bterm (fl : ℝ → ℝ) (Pw : ℝ) (n : ℕ) (pf : ℝ) : ℝ :=
  fl (fl (n : ℝ) * fl (Pw * pf))
noncomputable def sc (fl : ℝ → ℝ) (Sw Pw : ℝ) (n k : ℕ) (pf : ℝ) : ℝ :=
  fl (Aterm fl Sw k + Bterm fl Pw n pf)

theorem Aterm_bd {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Sw : ℝ}
    (hS1 : 19 ≤ Sw) (hS2 : Sw ≤ 21) {k : ℕ} (hk : k ≤ n) :
    0 ≤ Aterm fl Sw k ∧ Aterm fl Sw k ≤ 21 * n + 71 / 100 ∧ |Aterm fl Sw k| ≤ 23 * n ∧
      fl (Aterm fl Sw k) = Aterm fl Sw k := by
  obtain ⟨hk0, hk1⟩ := E.hr.pos_le E.hu0 E.hη hk E.hn E.nM
  have hn1 := E.nR
  have hx0 : 0 ≤ Sw * fl (k : ℝ) := mul_nonneg (by linarith) hk0
  have hx1 : Sw * fl (k : ℝ) ≤ 21 * ((n : ℝ) + 1 / 100) := mul_le_mul hS2 hk1 hk0 (by norm_num)
  have hxa : |Sw * fl (k : ℝ)| ≤ 22 * n := by
    rw [abs_of_nonneg hx0]; linarith
  have hf := abs_le.mp (E.fsn (by norm_num) (by norm_num) hxa)
  have hxM : Sw * fl (k : ℝ) ≤ M := le_trans (by linarith) (E.rin (C := 22) (by norm_num) (by norm_num))
  unfold Aterm
  refine ⟨E.hr.nonneg hx0 hxM, by linarith, ?_, E.idn (by norm_num) hxa (by norm_num)⟩
  rw [abs_le]; constructor <;> linarith [E.hr.nonneg hx0 hxM]

theorem A_gap {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Sw : ℝ}
    (hS1 : 19 ≤ Sw) (hS2 : Sw ≤ 21) {a b : ℕ} (hab : a < b) (hbn : b ≤ n) :
    Aterm fl Sw a ≤ Aterm fl Sw b - 16 * ((b : ℝ) - a) := by
  obtain ⟨ha0, ha1⟩ := E.hr.pos_le E.hu0 E.hη (le_trans (le_of_lt hab) hbn) E.hn E.nM
  obtain ⟨hb0, hb1⟩ := E.hr.pos_le E.hu0 E.hη hbn E.hn E.nM
  have hg := E.hr.pos_gap E.hu0 E.hη (le_of_lt hab) hbn E.hn E.nM
  have hd1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have hn1 := E.nR
  have hxa : |Sw * fl (a : ℝ)| ≤ 22 * n := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) ha0)]
    have := mul_le_mul hS2 ha1 ha0 (by norm_num)
    linarith
  have hxb : |Sw * fl (b : ℝ)| ≤ 22 * n := by
    rw [abs_of_nonneg (mul_nonneg (by linarith) hb0)]
    have := mul_le_mul hS2 hb1 hb0 (by norm_num)
    linarith
  have hgp := E.hr.gap E.hu0 hxa hxb (E.rin (C := 22) (by norm_num) (by norm_num))
  have hD0 : 0 ≤ fl (b : ℝ) - fl (a : ℝ) := by linarith
  have hSD := mul_le_mul_of_nonneg_right hS1 hD0
  have hun : u * (22 * (n : ℝ)) = 22 * (u * n) := by ring
  have hη1 := eta_tiny E.hη
  have hn2 := E.hn
  unfold Aterm
  nlinarith [hgp, hSD, hg, hd1, hun, hη1, hn2]

theorem B_core {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {t1 : ℝ}
    (h1 : -53 ≤ t1) (h2 : t1 ≤ 0) :
    fl (fl (n : ℝ) * t1) ≤ 0 ∧ |fl (fl (n : ℝ) * t1)| ≤ 55 * n ∧
      (t1 ≤ -48 → fl (fl (n : ℝ) * t1) ≤ -48 * n + 1) := by
  obtain ⟨hf0, hf1⟩ := E.hr.pos_le E.hu0 E.hη (le_refl n) E.hn E.nM
  have hfn := abs_le.mp (E.hr.pos_near E.hu0 E.hη (le_refl n) E.hn E.nM)
  have hn1 := E.nR
  have hx2a : fl (n : ℝ) * t1 ≤ 0 := by nlinarith
  have hx2b : -(54 * (n : ℝ)) ≤ fl (n : ℝ) * t1 := by nlinarith
  have hx2 : |fl (n : ℝ) * t1| ≤ 54 * n := by
    rw [abs_le]; constructor <;> linarith
  have hf := abs_le.mp (E.fsn (by norm_num) (by norm_num) hx2)
  have hM54 := E.rin (C := 54) (by norm_num) (by norm_num)
  refine ⟨E.hr.nonpos hx2a (by linarith), ?_, ?_⟩
  · have := E.hr.nonpos hx2a (by linarith)
    rw [abs_le]; constructor <;> linarith
  · intro h
    have : fl (n : ℝ) * t1 ≤ -48 * (n : ℝ) + 1 / 4 := by nlinarith
    linarith

theorem Bterm_facts {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Pw pf : ℝ}
    (hP1 : -51 ≤ Pw) (hP2 : Pw ≤ -49) (hpf0 : 0 ≤ pf) (hpf1 : pf ≤ 101 / 100) :
    Bterm fl Pw n pf ≤ 0 ∧ |Bterm fl Pw n pf| ≤ 55 * n ∧
      (99 / 100 ≤ pf → Bterm fl Pw n pf ≤ -48 * n + 1) := by
  have hx1a : Pw * pf ≤ 0 := by nlinarith
  have hx1b : -52 ≤ Pw * pf := by nlinarith
  have hx1 : |Pw * pf| ≤ 100 := by rw [abs_le]; constructor <;> linarith
  have ht1 := abs_le.mp (E.fs hx1)
  have h100 : (100 : ℝ) ≤ M := E.rc (by norm_num)
  have ht1n := E.hr.nonpos hx1a (by linarith)
  have hc := B_core E (t1 := fl (Pw * pf)) (by linarith) ht1n
  unfold Bterm
  refine ⟨hc.1, hc.2.1, ?_⟩
  intro hpf
  apply hc.2.2
  have : Pw * pf ≤ -485 / 10 := by nlinarith
  linarith

theorem sc_le_A {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Sw Pw pf : ℝ}
    (hS1 : 19 ≤ Sw) (hS2 : Sw ≤ 21) (hP1 : -51 ≤ Pw) (hP2 : Pw ≤ -49) (hpf0 : 0 ≤ pf)
    (hpf1 : pf ≤ 101 / 100) {k : ℕ} (hk : k ≤ n) :
    sc fl Sw Pw n k pf ≤ Aterm fl Sw k := by
  obtain ⟨hA0, hA1, hA2, hA3⟩ := Aterm_bd E hS1 hS2 hk
  obtain ⟨hB0, hB1, hB2⟩ := Bterm_facts E hP1 hP2 hpf0 hpf1
  have hn1 := E.nR
  have hM78 := E.rin (C := 78) (by norm_num) (by norm_num)
  have hM23 := E.rin (C := 23) (by norm_num) (by norm_num)
  have hy : |Aterm fl Sw k + Bterm fl Pw n pf| ≤ M := by
    rw [abs_le] at hA2 hB1 ⊢
    constructor <;> linarith [hA2.1, hA2.2, hB1.1, hB1.2]
  have hAM : |Aterm fl Sw k| ≤ M := le_trans hA2 hM23
  have := E.hr.mono _ _ hy hAM (by linarith : Aterm fl Sw k + Bterm fl Pw n pf ≤ Aterm fl Sw k)
  unfold sc
  rw [hA3] at this
  exact this

theorem sc_np {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Sw Pw : ℝ}
    (hS1 : 19 ≤ Sw) (hS2 : Sw ≤ 21) {k : ℕ} (hk : k ≤ n) :
    sc fl Sw Pw n k 0 = Aterm fl Sw k := by
  obtain ⟨hA0, hA1, hA2, hA3⟩ := Aterm_bd E hS1 hS2 hk
  unfold sc Bterm
  simp [E.hr.zero, hA3]

theorem sc_pr {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Sw Pw pf : ℝ}
    (hS1 : 19 ≤ Sw) (hS2 : Sw ≤ 21) (hP1 : -51 ≤ Pw) (hP2 : Pw ≤ -49) (hpf0 : 99 / 100 ≤ pf)
    (hpf1 : pf ≤ 101 / 100) {k : ℕ} (hk : k ≤ n) :
    sc fl Sw Pw n k pf ≤ -16 * n := by
  obtain ⟨hA0, hA1, hA2, hA3⟩ := Aterm_bd E hS1 hS2 hk
  obtain ⟨hB0, hB1, hB2⟩ := Bterm_facts E hP1 hP2 (by linarith) hpf1
  have hB3 := hB2 hpf0
  have hn1 := E.nR
  have hy : |Aterm fl Sw k + Bterm fl Pw n pf| ≤ 78 * n := by
    rw [abs_le] at hA2 hB1 ⊢
    constructor <;> linarith [hA2.1, hA2.2, hB1.1, hB1.2]
  have hf := abs_le.mp (E.fsn (by norm_num) (by norm_num) hy)
  unfold sc
  linarith

theorem sc_abs {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Sw Pw pf : ℝ}
    (hS1 : 19 ≤ Sw) (hS2 : Sw ≤ 21) (hP1 : -51 ≤ Pw) (hP2 : Pw ≤ -49) (hpf0 : 0 ≤ pf)
    (hpf1 : pf ≤ 101 / 100) {k : ℕ} (hk : k ≤ n) :
    |sc fl Sw Pw n k pf| ≤ 100 * n := by
  obtain ⟨hA0, hA1, hA2, hA3⟩ := Aterm_bd E hS1 hS2 hk
  obtain ⟨hB0, hB1, hB2⟩ := Bterm_facts E hP1 hP2 hpf0 hpf1
  have hn1 := E.nR
  have hy : |Aterm fl Sw k + Bterm fl Pw n pf| ≤ 78 * n := by
    rw [abs_le] at hA2 hB1 ⊢
    constructor <;> linarith [hA2.1, hA2.2, hB1.1, hB1.2]
  have hf := abs_le.mp (E.fsn (by norm_num) (by norm_num) hy)
  have hy' := abs_le.mp hy
  unfold sc
  rw [abs_le]; constructor <;> linarith

theorem Env.fl_ap {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x t e : ℝ}
    (hx : |x - t| ≤ e) (ht : |t| ≤ 50) (he : e ≤ 40) : |fl x - t| ≤ e + 1 / 100000 := by
  have hx100 : |x| ≤ 100 := by
    have := abs_sub_abs_le_abs_sub x t
    linarith
  have h := E.hr.abs E.hu0 hx100 (E.rc (by norm_num))
  have h1 := eta_tiny E.hη
  have h2 : u * 100 ≤ 1 / 2 ^ 24 * 100 := mul_le_mul_of_nonneg_right E.hu1 (by norm_num)
  have h3 : (1 : ℝ) / 2 ^ 24 * 100 + 1 / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  have h4 := abs_add_le (fl x - x) (x - t)
  have h5 : fl x - x + (x - t) = fl x - t := by ring
  rw [h5] at h4
  linarith

theorem Env.mul_ap {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x y s t a b S T : ℝ}
    (hx : |x - s| ≤ a) (hy : |y - t| ≤ b) (hS : |s| ≤ S) (hT : |t| ≤ T) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (hS5 : S ≤ 5) (hT5 : T ≤ 5) (ha : a ≤ 1) (hb : b ≤ 1) :
    |fl (x * y) - s * t| ≤ a * T + b * S + a * b + 1 / 100000 := by
  have m := mul_near hx hy
  have h1 : a * |t| ≤ a * T := mul_le_mul_of_nonneg_left hT ha0
  have h2 : b * |s| ≤ b * S := mul_le_mul_of_nonneg_left hS hb0
  have hst : |s * t| ≤ 25 := by
    rw [abs_mul]
    have := mul_le_mul (le_trans hS hS5) (le_trans hT hT5) (abs_nonneg _) (by norm_num)
    linarith
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) hS
  have hT0 : 0 ≤ T := le_trans (abs_nonneg _) hT
  have hab : a * b ≤ 1 := by nlinarith
  have h3 : a * T ≤ 5 := by nlinarith
  have h4 : b * S ≤ 5 := by nlinarith
  have := E.fl_ap (x := x * y) (t := s * t) (e := a * T + b * S + a * b) (by linarith) (by linarith) (by linarith)
  exact this

theorem Env.add_ap {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x y s t a b z : ℝ}
    (hx : |x - s| ≤ a) (hy : |y - t| ≤ b) (hz : s + t = z) (hzb : |z| ≤ 50) (hab : a + b ≤ 40) :
    |fl (x + y) - z| ≤ a + b + 1 / 100000 := by
  have h1 : |x + y - z| ≤ a + b := by
    have e : x + y - z = (x - s) + (y - t) := by rw [← hz]; ring
    rw [e]
    have := abs_add_le (x - s) (y - t)
    linarith
  exact E.fl_ap h1 hzb hab

theorem relu_ap {x g e : ℝ} (hg : 0 ≤ g) (h : |x - g| ≤ e) : |Lane4.relu x - g| ≤ e := by
  rcases le_total 0 x with h0 | h0
  · rw [Lane4.relu_of_nonneg h0]; exact h
  · rw [Lane4.relu_of_nonpos h0]
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]

theorem pre_active {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n)
    {Wm Cm Bm X c gc : ℝ} (h1 : |Wm - 2| ≤ 2 / 190) (h2 : |X - 1| ≤ 1 / 190)
    (h3 : |Cm - 1| ≤ 1 / 190) (h4 : |c - gc| ≤ 1 / 40) (hB : |Bm - (-2)| ≤ 2 / 190)
    (hg0 : 0 ≤ gc) (hg1 : gc ≤ 1) :
    |fl (fl (fl (Wm * X) + fl (Cm * c)) + Bm) - gc| ≤ 13 / 200 := by
  have m1 := E.mul_ap h1 h2 (S := 2) (T := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have m2 := E.mul_ap h3 h4 (S := 1) (T := 1) (s := 1) (t := gc) (by norm_num)
    (by rw [abs_of_nonneg hg0]; exact hg1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have a1 := E.add_ap (z := 2 * 1 + 1 * gc) m1 m2 rfl
    (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  have a2 := E.add_ap (z := gc) a1 hB (by ring)
    (by rw [abs_of_nonneg hg0]; linarith) (by norm_num)
  linarith

theorem pre_zero {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n)
    {Wm Cm Bm c gc : ℝ} (h3 : |Cm - 1| ≤ 1 / 190) (h4 : |c - gc| ≤ 1 / 40)
    (hB : |Bm - (-2)| ≤ 2 / 190) (hg0 : 0 ≤ gc) (hg1 : gc ≤ 1) :
    Lane4.relu (fl (fl (fl (Wm * 0) + fl (Cm * c)) + Bm)) = 0 := by
  have m2 := E.mul_ap h3 h4 (S := 1) (T := 1) (s := 1) (t := gc) (by norm_num)
    (by rw [abs_of_nonneg hg0]; exact hg1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have a1 := E.add_ap (x := fl (Wm * 0)) (s := 0) (a := 0) (z := gc) (by simp [E.hr.zero]) m2
    (by ring) (by rw [abs_of_nonneg hg0]; linarith) (by norm_num)
  have a2 := E.add_ap (z := gc + -2) a1 hB rfl
    (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  apply Lane4.relu_of_nonpos
  rw [abs_le] at a2
  linarith [a2.2]

theorem resU {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {W2a W2b hU gc : ℝ}
    (h1 : |W2a - 1| ≤ 1 / 190) (h2 : |hU - gc| ≤ 13 / 200) (hg0 : 0 ≤ gc) (hg1 : gc ≤ 1) :
    |fl (fl (W2a * hU) + fl (W2b * 0)) - gc| ≤ 71 / 1000 := by
  have m1 := E.mul_ap h1 h2 (S := 1) (T := 1) (s := 1) (t := gc) (by norm_num)
    (by rw [abs_of_nonneg hg0]; exact hg1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have a1 := E.add_ap (y := fl (W2b * 0)) (t := 0) (b := 0) (z := gc) m1 (by simp [E.hr.zero])
    (by ring) (by rw [abs_of_nonneg hg0]; linarith) (by norm_num)
  linarith

theorem resV {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {W2a W2b hV gc : ℝ}
    (h1 : |W2b - (-2)| ≤ 2 / 190) (h2 : |hV - gc| ≤ 13 / 200) (hg0 : 0 ≤ gc) (hg1 : gc ≤ 1) :
    |fl (fl (W2a * 0) + fl (W2b * hV)) - (-2 * gc)| ≤ 71 / 500 := by
  have m1 := E.mul_ap h1 h2 (S := 2) (T := 1) (s := -2) (t := gc) (by norm_num)
    (by rw [abs_of_nonneg hg0]; exact hg1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have a1 := E.add_ap (x := fl (W2a * 0)) (s := 0) (a := 0) (z := -2 * gc) (by simp [E.hr.zero]) m1
    (by ring) (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  linarith

theorem outU {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Wa Wr A Q Aid gc : ℝ}
    (hWa : |Wa - 1| ≤ 1 / 190) (hWr : |Wr - 1| ≤ 1 / 190) (hA : |A - Aid| ≤ 1 / 190)
    (hQ : |Q - gc| ≤ 71 / 1000) (hg0 : 0 ≤ gc) (hg1 : gc ≤ 1) (hA0 : 0 ≤ Aid) (hA1 : Aid ≤ 1) :
    |fl (fl (Wa * A) + fl (Wr * Q)) - (Aid + gc)| ≤ 1 / 10 := by
  have m1 := E.mul_ap hWa hA (S := 1) (T := 1) (s := 1) (t := Aid) (by norm_num)
    (by rw [abs_of_nonneg hA0]; exact hA1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have m2 := E.mul_ap hWr hQ (S := 1) (T := 1) (s := 1) (t := gc) (by norm_num)
    (by rw [abs_of_nonneg hg0]; exact hg1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have a1 := E.add_ap (z := Aid + gc) m1 m2 (by ring)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  linarith

theorem outV {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {Wa Wr A Q gc : ℝ}
    (hWa : |Wa - 1| ≤ 1 / 190) (hWr : |Wr - 1| ≤ 1 / 190) (hA : |A - 2| ≤ 2 / 190)
    (hQ : |Q - (-2 * gc)| ≤ 71 / 500) (hg0 : 0 ≤ gc) (hg1 : gc ≤ 1) :
    |fl (fl (Wa * A) + fl (Wr * Q)) - (2 - 2 * gc)| ≤ 1 / 5 := by
  have m1 := E.mul_ap hWa hA (S := 1) (T := 2) (s := 1) (t := 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have m2 := E.mul_ap hWr hQ (S := 1) (T := 2) (s := 1) (t := -2 * gc) (by norm_num)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have a1 := E.add_ap (z := 2 - 2 * gc) m1 m2 (by ring)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  linarith

end Lane4.Case
