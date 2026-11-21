namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSeq (pdot radd)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000
set_option linter.all false

/-! ### Rows and the network -/

def rowf (a : ℕ → ℚ) : List ℚ := [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9]
def z10 : List ℚ := rowf (fun _ => 0)
def urow (c : ℕ) : List ℚ := rowf (fun k => if k = c then 1 else 0)
def vrow : List ℚ := rowf (fun k => if k = 1 ∨ k = 2 then 2 else 0)
def gGate (c : ℕ) : List ℚ := rowf (fun k => if k = 3 + c then -1 else 0)
def w1row (c : ℕ) : List ℚ := rowf (fun k => if k = c then 5 / 2 else if k = 6 + c then 1 else 0)
def outRow : List ℚ := rowf (fun k => if k = 9 then 1 else 0)
def erow (t : ℕ) : List ℚ := rowf (fun k => if k < 3 ∧ t = k + 1 then 1 else 0)
def zrows : List (List ℚ) := [z10, z10, z10, z10, z10, z10, z10, z10, z10, z10]

def head1 : AHead :=
  { A := zrows, V := [z10, z10, z10, urow 0, urow 1, urow 2, z10, z10, z10, z10],
    mask := Mask.strict, m := 24, g := z10, gb := -1 / 2 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [], b1 := [],
    W2 := [[], [], [], [], [], [], [], [], [], []], b2 := z10 }

def head2 (c : ℕ) : AHead :=
  { A := zrows,
    V := [if 0 = 6 + c then vrow else z10, if 1 = 6 + c then vrow else z10,
          if 2 = 6 + c then vrow else z10, if 3 = 6 + c then vrow else z10,
          if 4 = 6 + c then vrow else z10, if 5 = 6 + c then vrow else z10,
          if 6 = 6 + c then vrow else z10, if 7 = 6 + c then vrow else z10,
          if 8 = 6 + c then vrow else z10, if 9 = 6 + c then vrow else z10],
    mask := Mask.causal, m := 24, g := gGate c, gb := 1 / 2 }

def blk2 : ABlock :=
  { heads := [head2 0, head2 1, head2 2],
    W1 := [w1row 0, w1row 1, w1row 2],
    b1 := [-5 / 2, -5 / 2, -5 / 2],
    W2 := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0],
           [0, 0, 0], [0, 0, 0], [1, 1, 1]],
    b2 := z10 }

def net : ANet :=
  { embed := [erow 0, erow 1, erow 2, erow 3], blocks := [blk1, blk2],
    outW := outRow, outB := 0 }

/-! ### Ten-vectors and generic list lemmas -/

noncomputable def vec10 (f : ℕ → ℝ) : List ℝ := [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9]
noncomputable def vec3 (f : ℕ → ℝ) : List ℝ := [f 0, f 1, f 2]
noncomputable def sum10 (f : ℕ → ℝ) : ℝ := f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9

theorem rowf_getD (a : ℕ → ℚ) {k : ℕ} (hk : k < 10) : (rowf a).getD k 0 = a k := by
  unfold rowf
  interval_cases k <;> rfl

theorem vec10_getD (f : ℕ → ℝ) {k : ℕ} (hk : k < 10) : (vec10 f).getD k 0 = f k := by
  unfold vec10
  interval_cases k <;> rfl

theorem vec3_getD (f : ℕ → ℝ) {k : ℕ} (hk : k < 3) : (vec3 f).getD k 0 = f k := by
  unfold vec3
  interval_cases k <;> rfl

theorem vec10_length (f : ℕ → ℝ) : (vec10 f).length = 10 := rfl
theorem vec3_length (f : ℕ → ℝ) : (vec3 f).length = 3 := rfl

theorem sum10_const (c : ℝ) : sum10 (fun _ => c) = 10 * c := by
  unfold sum10; ring

theorem close_vec10 {x : List ℝ} (hx : x.length = 10) {hh : ℕ → ℝ} {e X : ℝ}
    (hent : ∀ k, k < 10 → |x.getD k 0 - hh k| ≤ e ∧ |hh k| ≤ X) : Close x (vec10 hh) e X := by
  refine ⟨by rw [hx]; rfl, ?_⟩
  intro k hk
  have hk10 : k < 10 := by omega
  rw [vec10_getD hh hk10]
  exact hent k hk10

theorem radd_length (fl : ℝ → ℝ) (x y : List ℝ) (hl : x.length = y.length) :
    (radd fl x y).length = x.length := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b y => simp at hl
  | cons a x ih =>
    cases y with
    | nil => simp at hl
    | cons b y =>
      have hl' : x.length = y.length := by simpa using hl
      show (fl (a + b) :: radd fl x y).length = (a :: x).length
      simp [ih y hl']

theorem radd_getD (fl : ℝ → ℝ) (x y : List ℝ) (k : ℕ) (hx : k < x.length) (hy : k < y.length) :
    (radd fl x y).getD k 0 = fl (x.getD k 0 + y.getD k 0) := by
  induction x generalizing y k with
  | nil => simp at hx
  | cons a x ih =>
    cases y with
    | nil => simp at hy
    | cons b y =>
      cases k with
      | zero =>
        show (fl (a + b) :: radd fl x y).getD 0 0 = _
        simp
      | succ k =>
        have ih' := ih y k (by simpa using hx) (by simpa using hy)
        show (fl (a + b) :: radd fl x y).getD (k + 1) 0 = _
        simpa using ih'

theorem aswRow_length (fl : ℝ → ℝ) (r : List ℚ) (d : ℕ → ℝ) (j : ℕ) :
    (aswRow fl r d j).length = r.length := by
  induction r generalizing j with
  | nil => rfl
  | cons a r ih =>
    show (asw fl a (d j) :: aswRow fl r d (j + 1)).length = (a :: r).length
    simp [ih]

theorem aswRow_getD (fl : ℝ → ℝ) (r : List ℚ) (d : ℕ → ℝ) (j k : ℕ) (hk : k < r.length) :
    (aswRow fl r d j).getD k 0 = asw fl (r.getD k 0) (d (j + k)) := by
  induction r generalizing j k with
  | nil => simp at hk
  | cons a r ih =>
    cases k with
    | zero =>
      show (asw fl a (d j) :: aswRow fl r d (j + 1)).getD 0 0 = _
      simp
    | succ k =>
      have ih' := ih (j + 1) k (by simpa using hk)
      show (asw fl a (d j) :: aswRow fl r d (j + 1)).getD (k + 1) 0 = _
      simp only [List.getD_cons_succ]
      rw [ih']
      have e : j + 1 + k = j + (k + 1) := by omega
      rw [e]

theorem aattnRows_length (fl ex : ℝ → ℝ) (dV : ℕ → ℕ → ℝ) (c : List ℕ) (s : ℕ → ℝ)
    (x : ℕ → Vec) (M : List (List ℚ)) (i0 : ℕ) :
    (aattnRows fl ex M dV c s x i0).length = M.length := by
  induction M generalizing i0 with
  | nil => rfl
  | cons r M ih =>
    show (savg fl ex c s (fun j => ardot fl r (x j) (dV i0) 0 0) ::
      aattnRows fl ex M dV c s x (i0 + 1)).length = (r :: M).length
    simp [ih]

theorem aattnRows_getD (fl ex : ℝ → ℝ) (dV : ℕ → ℕ → ℝ) (c : List ℕ) (s : ℕ → ℝ)
    (x : ℕ → Vec) (M : List (List ℚ)) (i0 k : ℕ) (hk : k < M.length) :
    (aattnRows fl ex M dV c s x i0).getD k 0 =
      savg fl ex c s (fun j => ardot fl (M.getD k []) (x j) (dV (i0 + k)) 0 0) := by
  induction M generalizing i0 k with
  | nil => simp at hk
  | cons r M ih =>
    cases k with
    | zero =>
      show (savg fl ex c s (fun j => ardot fl r (x j) (dV i0) 0 0) ::
        aattnRows fl ex M dV c s x (i0 + 1)).getD 0 0 = _
      simp
    | succ k =>
      have ih' := ih (i0 + 1) k (by simpa using hk)
      show (savg fl ex c s (fun j => ardot fl r (x j) (dV i0) 0 0) ::
        aattnRows fl ex M dV c s x (i0 + 1)).getD (k + 1) 0 = _
      simp only [List.getD_cons_succ]
      rw [ih']
      have e : i0 + 1 + k = i0 + (k + 1) := by omega
      rw [e]

theorem araffine_length (fl : ℝ → ℝ) (x : Vec) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ)
    (M : List (List ℚ)) (b : List ℚ) (hl : M.length = b.length) (i0 : ℕ) :
    (araffine fl M b x dW db i0).length = M.length := by
  induction M generalizing b i0 with
  | nil =>
    cases b with
    | nil => rfl
    | cons c b => simp at hl
  | cons r M ih =>
    cases b with
    | nil => simp at hl
    | cons c b =>
      have hl' : M.length = b.length := by simpa using hl
      show (fl (ardot fl r x (dW i0) 0 0 + asw fl c (db i0)) ::
        araffine fl M b x dW db (i0 + 1)).length = (r :: M).length
      simp [ih b hl']

theorem araffine_getD (fl : ℝ → ℝ) (x : Vec) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ)
    (M : List (List ℚ)) (b : List ℚ) (i0 k : ℕ) (hM : k < M.length) (hb : k < b.length) :
    (araffine fl M b x dW db i0).getD k 0 =
      fl (ardot fl (M.getD k []) x (dW (i0 + k)) 0 0 + asw fl (b.getD k 0) (db (i0 + k))) := by
  induction M generalizing b i0 k with
  | nil => simp at hM
  | cons r M ih =>
    cases b with
    | nil => simp at hb
    | cons c b =>
      cases k with
      | zero =>
        show (fl (ardot fl r x (dW i0) 0 0 + asw fl c (db i0)) ::
          araffine fl M b x dW db (i0 + 1)).getD 0 0 = _
        simp
      | succ k =>
        have ih' := ih b (i0 + 1) k (by simpa using hM) (by simpa using hb)
        show (fl (ardot fl r x (dW i0) 0 0 + asw fl c (db i0)) ::
          araffine fl M b x dW db (i0 + 1)).getD (k + 1) 0 = _
        simp only [List.getD_cons_succ]
        rw [ih']
        have e : i0 + 1 + k = i0 + (k + 1) := by omega
        rw [e]

theorem armat_length (fl : ℝ → ℝ) (x : Vec) (d : ℕ → ℕ → ℝ) (M : List (List ℚ)) (i0 : ℕ) :
    (armat fl M x d i0).length = M.length := by
  induction M generalizing i0 with
  | nil => rfl
  | cons r M ih =>
    show (ardot fl r x (d i0) 0 0 :: armat fl M x d (i0 + 1)).length = (r :: M).length
    simp [ih]

theorem armat_getD (fl : ℝ → ℝ) (x : Vec) (d : ℕ → ℕ → ℝ) (M : List (List ℚ)) (i0 k : ℕ)
    (hk : k < M.length) :
    (armat fl M x d i0).getD k 0 = ardot fl (M.getD k []) x (d (i0 + k)) 0 0 := by
  induction M generalizing i0 k with
  | nil => simp at hk
  | cons r M ih =>
    cases k with
    | zero =>
      show (ardot fl r x (d i0) 0 0 :: armat fl M x d (i0 + 1)).getD 0 0 = _
      simp
    | succ k =>
      have ih' := ih (i0 + 1) k (by simpa using hk)
      show (ardot fl r x (d i0) 0 0 :: armat fl M x d (i0 + 1)).getD (k + 1) 0 = _
      simp only [List.getD_cons_succ]
      rw [ih']
      have e : i0 + 1 + k = i0 + (k + 1) := by omega
      rw [e]

theorem map_relu_getD (l : List ℝ) (k : ℕ) (hk : k < l.length) :
    (l.map Lane4.relu).getD k 0 = Lane4.relu (l.getD k 0) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k => simpa using ih k (by simpa using hk)

theorem ardot_nil' (fl : ℝ → ℝ) (d : ℕ → ℝ) : ardot fl [] ([] : List ℝ) d 0 0 = 0 := rfl

theorem attn_getD (hd : AHead) (fl ex : ℝ → ℝ) (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ)
    (dgb : ℝ) (n : ℕ) (x : ℕ → Vec) (i k : ℕ) (hk : k < hd.V.length) :
    (hd.attn fl ex dA dV dm dg dgb n x i).getD k 0 =
      savg fl ex (hd.cands fl dg dgb n x i) (fun j => hd.score fl dA dm x i j)
        (fun j => ardot fl (hd.V.getD k []) (x j) (dV k) 0 0) := by
  unfold AHead.attn
  rw [aattnRows_getD fl ex dV _ _ x hd.V 0 k hk, zero_add]

theorem attn_length (hd : AHead) (fl ex : ℝ → ℝ) (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ)
    (dgb : ℝ) (n : ℕ) (x : ℕ → Vec) (i : ℕ) :
    (hd.attn fl ex dA dV dm dg dgb n x i).length = hd.V.length := by
  unfold AHead.attn
  exact aattnRows_length fl ex dV _ _ x hd.V 0

/-! ### Closeness helpers -/

theorem closeL_of_getD (x xh es Xs : List ℝ) (n : ℕ) (hx : x.length = n) (hxh : xh.length = n)
    (hes : es.length = n) (hXs : Xs.length = n)
    (hent : ∀ k, k < n → |x.getD k 0 - xh.getD k 0| ≤ es.getD k 0 ∧ |xh.getD k 0| ≤ Xs.getD k 0) :
    CloseL x xh es Xs :=
  ⟨by omega, by omega, by omega, fun k hk => hent k (by omega)⟩

theorem relu_near {a b e : ℝ} (hab : |a - b| ≤ e) : |Lane4.relu a - Lane4.relu b| ≤ e := by
  have he : 0 ≤ e := le_trans (abs_nonneg _) hab
  obtain ⟨h1, h2⟩ := abs_le.mp hab
  unfold Lane4.relu
  rw [abs_le]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_right ha, max_eq_left hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_left hb]; constructor <;> linarith

/-! ### Ideal values -/

noncomputable def ind (t c : ℕ) : ℝ := if t = c then 1 else 0

theorem ind_nonneg (t c : ℕ) : 0 ≤ ind t c := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one (t c : ℕ) : ind t c ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem ind_sum (t : ℕ) : ind t 1 + ind t 2 + ind t 3 ≤ 1 := by
  by_cases h1 : t = 1
  · subst h1; norm_num [ind]
  · by_cases h2 : t = 2
    · subst h2; norm_num [ind]
    · by_cases h3 : t = 3
      · subst h3; norm_num [ind]
      · simp [ind, h1, h2, h3]

theorem ind_zero_succ (c : ℕ) : ind 0 (c + 1) = 0 := by
  unfold ind; rw [if_neg (by omega)]

noncomputable def idt (t k : ℕ) : ℝ :=
  if k = 0 then ind t 1 else if k = 1 then ind t 2 else if k = 2 then ind t 3 else 0

theorem idt_nonneg (t k : ℕ) : 0 ≤ idt t k := by
  unfold idt; split_ifs <;> first | exact ind_nonneg _ _ | norm_num

theorem idt_le_one (t k : ℕ) : idt t k ≤ 1 := by
  unfold idt; split_ifs <;> first | exact ind_le_one _ _ | norm_num

theorem idt_sum (t : ℕ) : sum10 (idt t) ≤ 1 := by
  have := ind_sum t
  unfold sum10
  simp [idt]
  linarith

theorem idt_c (t c : ℕ) (hc : c < 3) : idt t c = ind t (c + 1) := by
  interval_cases c <;> simp [idt]

theorem idt_large (t k : ℕ) (hk : 3 ≤ k) : idt t k = 0 := by
  unfold idt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

noncomputable def id0 (w : List ℕ) (j k : ℕ) : ℝ := idt (tokAt w j) k

noncomputable def id1 (w : List ℕ) (j k : ℕ) : ℝ :=
  if k < 3 then idt (tokAt w j) k else if k < 6 then idt (tokAt w (j - 1)) (k - 3) else 0

theorem id0_nonneg (w : List ℕ) (j k : ℕ) : 0 ≤ id0 w j k := idt_nonneg _ _
theorem id0_le_one (w : List ℕ) (j k : ℕ) : id0 w j k ≤ 1 := idt_le_one _ _
theorem id0_sum' (w : List ℕ) (j : ℕ) : sum10 (id0 w j) ≤ 1 := idt_sum _

theorem id1_nonneg (w : List ℕ) (j k : ℕ) : 0 ≤ id1 w j k := by
  unfold id1; split_ifs <;> first | exact idt_nonneg _ _ | norm_num

theorem id1_le_one (w : List ℕ) (j k : ℕ) : id1 w j k ≤ 1 := by
  unfold id1; split_ifs <;> first | exact idt_le_one _ _ | norm_num

theorem id1_sum' (w : List ℕ) (j : ℕ) : sum10 (id1 w j) ≤ 2 := by
  have h1 := ind_sum (tokAt w j)
  have h2 := ind_sum (tokAt w (j - 1))
  unfold sum10
  simp [id1, idt]
  linarith

theorem id1_O (w : List ℕ) (j c : ℕ) (hc : c < 3) : id1 w j c = ind (tokAt w j) (c + 1) := by
  unfold id1
  rw [if_pos hc]
  exact idt_c _ _ hc

theorem id1_P (w : List ℕ) (j c : ℕ) (hc : c < 3) :
    id1 w j (3 + c) = ind (tokAt w (j - 1)) (c + 1) := by
  unfold id1
  rw [if_neg (by omega), if_pos (by omega)]
  have e : 3 + c - 3 = c := by omega
  rw [e]
  exact idt_c _ _ hc

theorem id1_V (w : List ℕ) (j k : ℕ) (hk : 6 ≤ k) : id1 w j k = 0 := by
  unfold id1
  rw [if_neg (by omega), if_neg (by omega)]

theorem id1_split (w : List ℕ) (i k : ℕ) (hk : k < 10) :
    id1 w i k = id0 w i k + (if 3 ≤ k ∧ k < 6 then id0 w (i - 1) (k - 3) else 0) := by
  interval_cases k <;> simp [id1, id0, idt]

theorem id0_zero_tok (w : List ℕ) (k : ℕ) : id0 w 0 k = 0 := by
  unfold id0 idt
  rw [Lane4.Seq.tokAt_zero]
  simp [ind]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with hh | hh
  · omega
  · exact (hw _ hh).2

/-! ### The context -/

structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη1 : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 1000)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3
  hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256
  hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M

section Steps

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

theorem Ctx.range (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : c ≤ 2 ^ 40) : c ≤ M :=
  range_const ev.hM (by omega) hc

theorem Ctx.rangeN (ev : Ctx u η M fl ex p w) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ 40) :
    c * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
  range_lin ev.hM (by omega) hc0 hc

theorem u_mul (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : 0 ≤ c) :
    u * (c * ((w.length + 1 : ℕ) : ℝ)) ≤ c / 256 := by
  have h : u * (c * ((w.length + 1 : ℕ) : ℝ)) = c * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  rw [h]
  have := mul_le_mul_of_nonneg_left ev.hn hc
  linarith

theorem Ctx.fl16 (ev : Ctx u η M fl ex p w) {x : ℝ} (hx : |x| ≤ 16) :
    |fl x - x| ≤ 1 / 10 ^ 6 := by
  have hM16 : (16 : ℝ) ≤ M := ev.range 16 (by norm_num)
  have h := ev.hr.abs ev.hu0 hx hM16
  have h1 : u * 16 ≤ 1 / 2 ^ 24 * 16 := mul_le_mul_of_nonneg_right ev.hu1 (by norm_num)
  have h2 := eta_tiny ev.hη1
  have h3 : (1 : ℝ) / 2 ^ 24 * 16 + 1 / 10 ^ 40 ≤ 1 / 10 ^ 6 := by norm_num
  linarith

theorem asw_c (ev : Ctx u η M fl ex p w) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000)
    (ha : |(a : ℝ)| ≤ 3) : |asw fl a d - (a : ℝ)| ≤ 1 / 990 := by
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have h := asw_near ev.hr ev.hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 4 :=
    mul_le_mul ev.hu1 (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny ev.hη1
  have h3 : (1 : ℝ) / 2 ^ 24 * 4 + 1 / 10 ^ 40 + 1 / 1000 ≤ 1 / 990 := by norm_num
  linarith

theorem small_ent (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl (0 : ℚ) d)| ≤ 1 / 980 := by
  have h1 := asw_c ev (0 : ℚ) hd (by simp)
  have h1' : |asw fl (0 : ℚ) d| ≤ 1 / 990 := by simpa using h1
  have h2 : |(0 : ℝ) + asw fl (0 : ℚ) d| ≤ 1 / 990 := by rw [zero_add]; exact h1'
  have h3 := ev.hr.bound ev.hu0 h2 (ev.range (1 / 990) (by norm_num))
  have h4 : u * (1 / 990) ≤ 1 / 2 ^ 24 * (1 / 990) :=
    mul_le_mul_of_nonneg_right ev.hu1 (by norm_num)
  have h5 := eta_tiny ev.hη1
  have h6 : (1 : ℝ) / 990 + (1 / 2 ^ 24 * (1 / 990) + 1 / 10 ^ 40) ≤ 1 / 980 := by norm_num
  linarith

theorem add1 (ev : Ctx u η M fl ex p w) {a b hh f ea eb : ℝ} (ha : |a - hh| ≤ ea)
    (hb : |b - f| ≤ eb) (ba : |a| ≤ 3) (bb : |b| ≤ 3) :
    |fl (a + b) - (hh + f)| ≤ ea + eb + 1 / 10 ^ 6 := by
  obtain ⟨a1, a2⟩ := abs_le.mp ba
  obtain ⟨b1, b2⟩ := abs_le.mp bb
  have r1 := ev.fl16 (x := a + b) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨r11, r12⟩ := abs_le.mp r1
  obtain ⟨h4, h5⟩ := abs_le.mp ha
  obtain ⟨h6, h7⟩ := abs_le.mp hb
  rw [abs_le]; constructor <;> linarith

theorem add2 (ev : Ctx u η M fl ex p w) {x a m hh f e ea em : ℝ} (hx : |x - hh| ≤ e)
    (ha : |a - f| ≤ ea) (hm : |m| ≤ em) (bx : |x| ≤ 3) (ba : |a| ≤ 3) (bm : |m| ≤ 3) :
    |fl (fl (x + a) + m) - (hh + f)| ≤ e + ea + em + 2 / 10 ^ 6 := by
  obtain ⟨x1, x2⟩ := abs_le.mp bx
  obtain ⟨a1, a2⟩ := abs_le.mp ba
  obtain ⟨m1, m2⟩ := abs_le.mp bm
  have r1 := ev.fl16 (x := x + a) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨r11, r12⟩ := abs_le.mp r1
  have r2 := ev.fl16 (x := fl (x + a) + m) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨r21, r22⟩ := abs_le.mp r2
  obtain ⟨h4, h5⟩ := abs_le.mp hx
  obtain ⟨h6, h7⟩ := abs_le.mp ha
  obtain ⟨h8, h9⟩ := abs_le.mp hm
  rw [abs_le]; constructor <;> linarith

theorem y_chain (ev : Ctx u η M fl ex p w) {x a0 a1 a2 hh f0 f1 f2 e e0 e1 e2 : ℝ}
    (hx : |x - hh| ≤ e) (h0 : |a0 - f0| ≤ e0) (h1 : |a1 - f1| ≤ e1) (h2 : |a2 - f2| ≤ e2)
    (bx : |x| ≤ 3) (b0 : |a0| ≤ 3) (b1 : |a1| ≤ 3) (b2 : |a2| ≤ 3) :
    |fl (fl (fl (x + a0) + a1) + a2) - (hh + f0 + f1 + f2)| ≤ e + e0 + e1 + e2 + 3 / 10 ^ 6 := by
  obtain ⟨x1, x2⟩ := abs_le.mp bx
  obtain ⟨c1, c2⟩ := abs_le.mp b0
  obtain ⟨d1, d2⟩ := abs_le.mp b1
  obtain ⟨g1, g2⟩ := abs_le.mp b2
  have r1 := ev.fl16 (x := x + a0) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨r11, r12⟩ := abs_le.mp r1
  have r2 := ev.fl16 (x := fl (x + a0) + a1) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨r21, r22⟩ := abs_le.mp r2
  have r3 := ev.fl16 (x := fl (fl (x + a0) + a1) + a2) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨r31, r32⟩ := abs_le.mp r3
  obtain ⟨h4, h5⟩ := abs_le.mp hx
  obtain ⟨h6, h7⟩ := abs_le.mp h0
  obtain ⟨h8, h9⟩ := abs_le.mp h1
  obtain ⟨h10, h11⟩ := abs_le.mp h2
  rw [abs_le]; constructor <;> linarith

/-! ### Dot products with per-coordinate errors -/

theorem dotQ_rowf (a : ℕ → ℚ) (hh : ℕ → ℝ) :
    dotQ (rowf a) (vec10 hh) = sum10 (fun k => ((a k : ℚ) : ℝ) * hh k) := by
  simp [dotQ, rowf, vec10, sum10] <;> ring

theorem wErr_rowf (a : ℕ → ℚ) (e X : ℕ → ℝ) :
    wErr (1 / 1000) (rowf a) (vec10 e) (vec10 X) =
      sum10 (fun k => |((a k : ℚ) : ℝ)| * e k) + 1 / 1000 * (sum10 X + sum10 e) := by
  simp [wErr, rowf, vec10, sum10] <;> ring

theorem dotW (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr10 : r.length = 10) {W : ℝ}
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (x : List ℝ) (hx : x.length = 10)
    (hh e X : ℕ → ℝ) (hent : ∀ k, k < 10 → |x.getD k 0 - hh k| ≤ e k ∧ |hh k| ≤ X k)
    {E Xb : ℝ} (hE : ∀ k, k < 10 → e k ≤ E ∧ X k ≤ Xb) (hE0 : 0 ≤ E) (hX0 : 0 ≤ Xb)
    (hT : (W + 1) * (Xb + E + 1) ≤ 2 ^ 20) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r (vec10 hh)| ≤
      wErr (1 / 1000) r (vec10 e) (vec10 X) + 10 * (W + 1) * (Xb + E + 1) / 2 ^ 16 + 1 / 2 ^ 100 ∧
    |ardot fl r x d 0 0| ≤ 10 * (W + 1) * (Xb + E + 1) * 2 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have hC : CloseL x (vec10 hh) (vec10 e) (vec10 X) := by
    refine ⟨by rw [hx]; rfl, by rw [hx]; rfl, by rw [hx]; rfl, ?_⟩
    intro k hk
    have hk10 : k < 10 := by omega
    rw [vec10_getD hh hk10, vec10_getD e hk10, vec10_getD X hk10]
    exact hent k hk10
  have hb : ∀ k, k < x.length → (vec10 e).getD k 0 ≤ E ∧ (vec10 X).getD k 0 ≤ Xb := by
    intro k hk
    have hk10 : k < 10 := by omega
    rw [vec10_getD e hk10, vec10_getD X hk10]
    exact hE k hk10
  have key := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) r x (vec10 hh) (vec10 e) (vec10 X) d W Xb E (by omega) (by omega) hC hb hd hW
    hW0 hX0 hE0 hT hM30
  rw [hr10] at key
  have h10 : ((10 : ℕ) : ℝ) = 10 := by norm_num
  rw [h10] at key
  exact key

theorem dot_gen (ev : Ctx u η M fl ex p w) (r : List ℚ) (a : ℕ → ℚ) (hr : r = rowf a) {W : ℝ}
    (hW : ∀ k, k < 10 → |((a k : ℚ) : ℝ)| ≤ W) (hW0 : 0 ≤ W) (x : List ℝ) (hx : x.length = 10)
    (hh e X : ℕ → ℝ) (hent : ∀ k, k < 10 → |x.getD k 0 - hh k| ≤ e k ∧ |hh k| ≤ X k)
    {E Xb : ℝ} (hE : ∀ k, k < 10 → e k ≤ E ∧ X k ≤ Xb) (hE0 : 0 ≤ E) (hX0 : 0 ≤ Xb)
    (hT : (W + 1) * (Xb + E + 1) ≤ 2 ^ 20) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - sum10 (fun k => ((a k : ℚ) : ℝ) * hh k)| ≤
      sum10 (fun k => |((a k : ℚ) : ℝ)| * e k) + 1 / 1000 * (sum10 X + sum10 e)
        + 10 * (W + 1) * (Xb + E + 1) / 2 ^ 16 + 1 / 2 ^ 100 ∧
    |ardot fl r x d 0 0| ≤ 10 * (W + 1) * (Xb + E + 1) * 2 := by
  subst hr
  have hW' : ∀ b ∈ rowf a, |(b : ℝ)| ≤ W := by
    intro b hb
    simp [rowf] at hb
    rcases hb with h | h | h | h | h | h | h | h | h | h <;>
      (rw [h]; exact hW _ (by norm_num))
  have key := dotW ev (rowf a) rfl hW' hW0 x hx hh e X hent hE hE0 hX0 hT d hd
  rw [dotQ_rowf, wErr_rowf] at key
  obtain ⟨k1, k2⟩ := key
  exact ⟨by linarith, k2⟩

theorem dot3 (ev : Ctx u η M fl ex p w) (a0 a1 a2 : ℚ) {W : ℝ}
    (hW : |(a0 : ℝ)| ≤ W ∧ |(a1 : ℝ)| ≤ W ∧ |(a2 : ℝ)| ≤ W) (hW0 : 0 ≤ W)
    (x : List ℝ) (hx : x.length = 3) (hh e X : ℕ → ℝ)
    (hent : ∀ k, k < 3 → |x.getD k 0 - hh k| ≤ e k ∧ |hh k| ≤ X k)
    {E Xb : ℝ} (hE : ∀ k, k < 3 → e k ≤ E ∧ X k ≤ Xb) (hE0 : 0 ≤ E) (hX0 : 0 ≤ Xb)
    (hT : (W + 1) * (Xb + E + 1) ≤ 2 ^ 20) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl [a0, a1, a2] x d 0 0 -
        ((a0 : ℝ) * hh 0 + (a1 : ℝ) * hh 1 + (a2 : ℝ) * hh 2)| ≤
      |(a0 : ℝ)| * e 0 + |(a1 : ℝ)| * e 1 + |(a2 : ℝ)| * e 2
        + 1 / 1000 * ((X 0 + X 1 + X 2) + (e 0 + e 1 + e 2))
        + 3 * (W + 1) * (Xb + E + 1) / 2 ^ 16 + 1 / 2 ^ 100 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have hC : CloseL x (vec3 hh) (vec3 e) (vec3 X) := by
    refine ⟨by rw [hx]; rfl, by rw [hx]; rfl, by rw [hx]; rfl, ?_⟩
    intro k hk
    have hk3 : k < 3 := by omega
    rw [vec3_getD hh hk3, vec3_getD e hk3, vec3_getD X hk3]
    exact hent k hk3
  have hb : ∀ k, k < x.length → (vec3 e).getD k 0 ≤ E ∧ (vec3 X).getD k 0 ≤ Xb := by
    intro k hk
    have hk3 : k < 3 := by omega
    rw [vec3_getD e hk3, vec3_getD X hk3]
    exact hE k hk3
  have hW' : ∀ b ∈ [a0, a1, a2], |(b : ℝ)| ≤ W := by
    intro b hb
    simp at hb
    rcases hb with h | h | h <;> (rw [h]; tauto)
  have key := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) [a0, a1, a2] x (vec3 hh) (vec3 e) (vec3 X) d W Xb E (by simp [hx])
    (by simp) hC hb hd hW' hW0 hX0 hE0 hT hM30
  obtain ⟨k1, -⟩ := key
  have hl : (([a0, a1, a2] : List ℚ).length : ℝ) = 3 := by simp
  rw [hl] at k1
  have e1 : dotQ [a0, a1, a2] (vec3 hh) =
      (a0 : ℝ) * hh 0 + (a1 : ℝ) * hh 1 + (a2 : ℝ) * hh 2 := by
    simp [dotQ, vec3] <;> ring
  have e2 : wErr (1 / 1000) [a0, a1, a2] (vec3 e) (vec3 X) =
      |(a0 : ℝ)| * e 0 + |(a1 : ℝ)| * e 1 + |(a2 : ℝ)| * e 2
        + 1 / 1000 * ((X 0 + X 1 + X 2) + (e 0 + e 1 + e 2)) := by
    simp [wErr, vec3] <;> ring
  rw [e1, e2] at k1
  exact k1

/-! ### Sums of the rows -/

theorem sum10_unit (c : ℕ) (hc : c < 10) (f : ℕ → ℝ) :
    sum10 (fun k => ((if k = c then (1 : ℚ) else 0 : ℚ) : ℝ) * f k) = f c := by
  interval_cases c <;> simp [sum10]

theorem sum10_unit_abs (c : ℕ) (hc : c < 10) (f : ℕ → ℝ) :
    sum10 (fun k => |((if k = c then (1 : ℚ) else 0 : ℚ) : ℝ)| * f k) = f c := by
  interval_cases c <;> simp [sum10]

theorem sum10_zero (f : ℕ → ℝ) : sum10 (fun k => (((fun _ => (0 : ℚ)) k : ℚ) : ℝ) * f k) = 0 := by
  simp [sum10]

theorem sum10_zero_abs (f : ℕ → ℝ) :
    sum10 (fun k => |(((fun _ => (0 : ℚ)) k : ℚ) : ℝ)| * f k) = 0 := by
  simp [sum10]

theorem sum10_vrow (f : ℕ → ℝ) :
    sum10 (fun k => ((if k = 1 ∨ k = 2 then (2 : ℚ) else 0 : ℚ) : ℝ) * f k) = 2 * f 1 + 2 * f 2 := by
  simp [sum10] <;> ring

theorem sum10_vrow_abs (f : ℕ → ℝ) :
    sum10 (fun k => |((if k = 1 ∨ k = 2 then (2 : ℚ) else 0 : ℚ) : ℝ)| * f k) =
      2 * f 1 + 2 * f 2 := by
  simp [sum10] <;> ring

theorem sum10_gate (c : ℕ) (hc : c < 3) (f : ℕ → ℝ) :
    sum10 (fun k => ((if k = 3 + c then (-1 : ℚ) else 0 : ℚ) : ℝ) * f k) = -f (3 + c) := by
  interval_cases c <;> simp [sum10]

theorem sum10_gate_abs (c : ℕ) (hc : c < 3) (f : ℕ → ℝ) :
    sum10 (fun k => |((if k = 3 + c then (-1 : ℚ) else 0 : ℚ) : ℝ)| * f k) = f (3 + c) := by
  interval_cases c <;> simp [sum10]

theorem sum10_w1 (c : ℕ) (hc : c < 3) (f : ℕ → ℝ) :
    sum10 (fun k => ((if k = c then (5 / 2 : ℚ) else if k = 6 + c then 1 else 0 : ℚ) : ℝ) * f k) =
      5 / 2 * f c + f (6 + c) := by
  interval_cases c <;> simp [sum10] <;> ring

theorem abs_w1 (c k : ℕ) :
    |((if k = c then (5 / 2 : ℚ) else if k = 6 + c then 1 else 0 : ℚ) : ℝ)| =
      ((if k = c then (5 / 2 : ℚ) else if k = 6 + c then 1 else 0 : ℚ) : ℝ) := by
  apply abs_of_nonneg
  split_ifs <;> norm_num

theorem sum10_w1_abs (c : ℕ) (hc : c < 3) (f : ℕ → ℝ) :
    sum10 (fun k => |((if k = c then (5 / 2 : ℚ) else if k = 6 + c then 1 else 0 : ℚ) : ℝ)| * f k) =
      5 / 2 * f c + f (6 + c) := by
  simp only [abs_w1]
  exact sum10_w1 c hc f

theorem sum10_out (f : ℕ → ℝ) :
    sum10 (fun k => ((if k = 9 then (1 : ℚ) else 0 : ℚ) : ℝ) * f k) = f 9 := by
  simp [sum10]

theorem sum10_out_abs (f : ℕ → ℝ) :
    sum10 (fun k => |((if k = 9 then (1 : ℚ) else 0 : ℚ) : ℝ)| * f k) = f 9 := by
  simp [sum10]

/-! ### Embedding and the initial state -/

theorem embed_ent {t : ℕ} (ht : t ≤ 3) (k : ℕ) (hk : k < 10) :
    (((net.embed.getD t []).getD k 0 : ℚ) : ℝ) = idt t k := by
  have h1 : net.embed.getD t [] = erow t := by
    interval_cases t <;> rfl
  have h2 : (erow t).getD k 0 = (if k < 3 ∧ t = k + 1 then 1 else 0 : ℚ) := rowf_getD _ hk
  rw [h1, h2]
  interval_cases t <;> interval_cases k <;> simp [idt, ind]

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 10 ∧
    ∀ k, k < 10 → |(net.init fl p w j).getD k 0 - id0 w j k| ≤ 1 / 990 := by
  have ht := tok_le w ev.hw j
  have hrow : net.init fl p w j =
      aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 := rfl
  have hlen : (net.embed.getD (tokAt w j) []).length = 10 := by
    generalize tokAt w j = t at ht ⊢
    interval_cases t <;> rfl
  refine ⟨by rw [hrow, aswRow_length, hlen], ?_⟩
  intro k hk
  rw [hrow, aswRow_getD fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 k
    (by rw [hlen]; exact hk)]
  have hq := embed_ent ht k hk
  have hq1 : |(((net.embed.getD (tokAt w j) []).getD k 0 : ℚ) : ℝ)| ≤ 3 := by
    rw [hq, abs_of_nonneg (idt_nonneg _ _)]
    have := idt_le_one (tokAt w j) k
    linarith
  have := asw_c ev ((net.embed.getD (tokAt w j) []).getD k 0) (ev.hp.E (tokAt w j) (0 + k)) hq1
  rw [hq] at this
  exact this

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    Close (net.init fl p w j) (vec10 (id0 w j)) (1 / 60) 1 := by
  obtain ⟨hl, hk⟩ := init_ent ev j
  apply close_vec10 hl
  intro k hk'
  refine ⟨le_trans (hk k hk') (by norm_num), ?_⟩
  rw [abs_of_nonneg (id0_nonneg w j k)]
  exact id0_le_one w j k

/-! ### Zero rows and content -/

theorem ardot_z10 (ev : Ctx u η M fl ex p w) {x : List ℝ} {hh : ℕ → ℝ}
    (hC : Close x (vec10 hh) (1 / 60) 1) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl z10 x d 0 0| ≤ 1 / 90 := by
  obtain ⟨hC1, hC2⟩ := hC
  have hxl : x.length = 10 := by
    simpa [vec10] using hC1
  have hent : ∀ k, k < 10 → |x.getD k 0 - hh k| ≤ (fun _ => (1 / 60 : ℝ)) k ∧
      |hh k| ≤ (fun _ => (1 : ℝ)) k := by
    intro k hk
    have := hC2 k (by omega)
    rw [vec10_getD hh hk] at this
    exact this
  have key := dot_gen ev z10 (fun _ => (0 : ℚ)) rfl (W := 0) (by intro k hk; simp) (le_refl _) x
    hxl hh (fun _ => 1 / 60) (fun _ => 1) hent (E := 1 / 60) (Xb := 1)
    (fun k hk => ⟨le_refl _, le_refl _⟩) (by norm_num) (by norm_num) (by norm_num) d hd
  obtain ⟨k1, -⟩ := key
  rw [sum10_zero, sum10_zero_abs, sum10_const, sum10_const] at k1
  rw [sub_zero] at k1
  refine le_trans k1 ?_
  norm_num

theorem content_zero (ev : Ctx u η M fl ex p w) (hd : AHead) (hA : hd.A = zrows)
    (x : ℕ → Vec) (hh : ℕ → ℕ → ℝ)
    (hC : ∀ j, j ≤ w.length → Close (x j) (vec10 (hh j)) (1 / 60) 1)
    (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (i k : ℕ) (hi : i ≤ w.length)
    (hk : k ≤ w.length) :
    |pdot fl (x i) (armat fl hd.A (x k) dA 0) 0| ≤ 1 / 5 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have hxi : (x i).length = 10 := by
    obtain ⟨hq1, -⟩ := hC i hi
    simpa [vec10] using hq1
  have hyl : (armat fl hd.A (x k) dA 0).length = 10 := by
    rw [armat_length, hA]; rfl
  have hCy : Close (armat fl hd.A (x k) dA 0) (vec10 (fun _ => 0)) (1 / 90) 0 := by
    apply close_vec10 hyl
    intro r hr
    refine ⟨?_, by simp⟩
    rw [armat_getD fl (x k) dA hd.A 0 r (by rw [hA]; show r < 10; exact hr), hA]
    have hz : zrows.getD r [] = z10 := by
      interval_cases r <;> rfl
    rw [hz, zero_add]
    have := ardot_z10 ev (hC k hk) (dA r) (hdA r)
    simpa using this
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (x i) (vec10 (hh i))
    (armat fl hd.A (x k) dA 0) (vec10 (fun _ => 0)) 1 0 (1 / 60) (1 / 90) (by rw [hxi, hyl])
    (by rw [hxi]; norm_num) (hC i hi) hCy (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hM30
  have hdR : dotR (vec10 (hh i)) (vec10 (fun _ => 0)) = 0 := by
    simp [dotR, vec10]
  rw [hdR, sub_zero, hxi] at p1
  refine le_trans p1 ?_
  norm_num

/-! ### Scores (generic head with slope 24 and zero score matrix) -/

theorem bias_abs (ev : Ctx u η M fl ex p w) (hd : AHead) (hm : ((hd.m : ℚ) : ℝ) = 24)
    {dm : ℝ} (hdm : |dm| ≤ 1 / 1000) (i t : ℕ) (hi : i ≤ w.length + 1)
    (ht : t ≤ w.length + 1) :
    |hd.bias fl dm i t| ≤ 26 * ((w.length + 1 : ℕ) : ℝ) := by
  have habs : |((hd.m : ℚ) : ℝ)| = 24 := by rw [hm]; exact abs_of_nonneg (by norm_num)
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM4 : (25 : ℝ) ≤ M := ev.range 25 (by norm_num)
  have hS := asw_bound ev.hr ev.hu0 hd.m hdm (by rw [habs]; linarith)
  rw [habs] at hS
  have hu25 : u * (24 + 1 / 1000) ≤ 1 / 2 ^ 24 * 25 :=
    mul_le_mul ev.hu1 (by norm_num) (by norm_num) (by positivity)
  have hη' := eta_tiny ev.hη1
  have hS2 : |asw fl hd.m dm| ≤ 25 := by
    have h1 : (1 : ℝ) / 2 ^ 24 * 25 + 1 / 10 ^ 40 ≤ 1 / 2 := by norm_num
    linarith
  have hbias : hd.bias fl dm i t
      = fl (asw fl hd.m dm * ((t : ℝ) - (i : ℝ))) := by
    simp [AHead.bias]
  rw [hbias]
  generalize asw fl hd.m dm = S at hS2 ⊢
  have ht' : (t : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast ht
  have hi' : (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hi
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hti : |(t : ℝ) - (i : ℝ)| ≤ ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hab : |S * ((t : ℝ) - (i : ℝ))| ≤ 25 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hS2 hti (abs_nonneg _) (by norm_num)
  have hB := ev.rangeN 25 (by norm_num) (by norm_num)
  have h := ev.hr.bound ev.hu0 hab hB
  have hu25n := u_mul ev 25 (by norm_num)
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem score_abs (ev : Ctx u η M fl ex p w) (hd : AHead) (hm : ((hd.m : ℚ) : ℝ) = 24)
    {dm : ℝ} (hdm : |dm| ≤ 1 / 1000) (dA : ℕ → ℕ → ℝ) (x : ℕ → Vec)
    (hcont : ∀ i k, i ≤ w.length → k ≤ w.length →
      |pdot fl (x i) (armat fl hd.A (x k) dA 0) 0| ≤ 1 / 5)
    (i k : ℕ) (hi : i ≤ w.length) (hk : k ≤ w.length) :
    |hd.score fl dA dm x i k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hbk := bias_abs ev hd hm hdm i k (by omega) (by omega)
  have hck := hcont i k hi hk
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |hd.bias fl dm i k + pdot fl (x i) (armat fl hd.A (x k) dA 0) 0| ≤
      27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have h := ev.hr.bound ev.hu0 ha hB
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hu27 := u_mul ev 27 (by norm_num)
  unfold AHead.score
  linarith

theorem score_gap (ev : Ctx u η M fl ex p w) (hd : AHead) (hm : ((hd.m : ℚ) : ℝ) = 24)
    {dm : ℝ} (hdm : |dm| ≤ 1 / 1000) (dA : ℕ → ℕ → ℝ) (x : ℕ → Vec)
    (hcont : ∀ i k, i ≤ w.length → k ≤ w.length →
      |pdot fl (x i) (armat fl hd.A (x k) dA 0) 0| ≤ 1 / 5)
    (i j k : ℕ) (hi : i ≤ w.length) (hj : j ≤ w.length) (hkj : k < j) :
    hd.score fl dA dm x i k ≤
      hd.score fl dA dm x i j - 16 * ((j : ℝ) - (k : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
    have := ev.rangeN 8192 (by norm_num) (by norm_num)
    have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [h12]; linarith
  obtain ⟨hg1, -⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) hd dm hdm (by rw [hm]; norm_num)
    (by rw [hm]; norm_num) (w.length + 1) i j k hkj (by omega) (by omega) ev.hn ev.hnη hM12
  rw [hm] at hg1
  obtain ⟨hcj1, hcj2⟩ := abs_le.mp (hcont i j hi hj)
  obtain ⟨hck1, hck2⟩ := abs_le.mp (hcont i k hi (by omega))
  have hbj := bias_abs ev hd hm hdm i j (by omega) (by omega)
  have hbk := bias_abs ev hd hm hdm i k (by omega) (by omega)
  have hcj := hcont i j hi hj
  have hck := hcont i k hi (by omega)
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |hd.bias fl dm i k + pdot fl (x i) (armat fl hd.A (x k) dA 0) 0| ≤
      27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hb : |hd.bias fl dm i j + pdot fl (x i) (armat fl hd.A (x j) dA 0) 0| ≤
      27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hgap := ev.hr.gap ev.hu0 ha hb hB
  have hu27 := u_mul ev 27 (by norm_num)
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hjk : (k : ℝ) + 1 ≤ (j : ℝ) := by
    have h : k + 1 ≤ j := hkj
    exact_mod_cast h
  unfold AHead.score
  linarith

/-- Softmax with a clear winner, with a per-key value error `ε` against ideal values `F`. -/
theorem soft_win (ev : Ctx u η M fl ex p w) (cs : List ℕ) (sc f F : ℕ → ℝ)
    (hnd : cs.Nodup) (hlen : cs.length ≤ w.length + 1) (j : ℕ) (hj : j ∈ cs)
    (hgap : ∀ k ∈ cs, k ≠ j → sc k ≤ sc j - 16 * (ndist j k : ℝ))
    (hS : ∀ k ∈ cs, |sc k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ))
    {ε B : ℝ} (hf : ∀ k ∈ cs, |f k - F k| ≤ ε) (hF : ∀ k ∈ cs, |F k| ≤ B)
    (hB : B + ε ≤ 4) :
    |savg fl ex cs sc f - F j| ≤ ε + (B + ε) / 100 + 1 / 2 ^ 90 := by
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hfB : ∀ k ∈ cs, |f k| ≤ B + ε := by
    intro k hk
    have h1 := hf k hk
    have h2 := hF k hk
    have h3 := abs_sub_abs_le_abs_sub (f k) (F k)
    linarith
  have hBM : 4 * (B + ε) + 4 ≤ M := by
    have := ev.range 20 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near ev.hr ev.he ev.hu0 ev.hu1 ev.hη0 ev.hη1 hnd hlen ev.hn ev.hnη hj
    hgap hS hSM hfB hBM
  have h3 := abs_sub_le (savg fl ex cs sc f) (f j) (F j)
  have h4 := hf j hj
  linarith

theorem gate_zero_of (ev : Ctx u η M fl ex p w) {pre : ℝ} (h1 : pre ≤ 0) (h2 : -4 ≤ pre) :
    Lane4.relu (fl pre) = 0 :=
  relu_fl_zero ev.hr h1 (by have := ev.range 4 (by norm_num); linarith)

theorem gate_pos_of (ev : Ctx u η M fl ex p w) {pre : ℝ} (h1 : 1 / 4 ≤ pre) (h2 : pre ≤ 4) :
    Lane4.relu (fl pre) ≠ 0 := by
  have hM4 := ev.range 4 (by norm_num)
  have := ev.fl16 (x := pre) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h3 : 0 < fl pre := by linarith [(abs_le.mp this).1]
  unfold Lane4.relu
  rw [max_eq_left h3.le]
  exact h3.ne'

/-! ### Block 1 -/

noncomputable def cs1 (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc1 (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i k : ℕ) : ℝ :=
  savg fl ex (cs1 fl p w i) (sc1 fl p w i)
    (fun j => ardot fl (head1.V.getD k []) (net.init fl p w j) (p.V 0 0 k) 0 0)

theorem head1_m : ((head1.m : ℚ) : ℝ) = 24 := by norm_num [head1]

theorem head1_V (k : ℕ) (hk : k < 10) :
    head1.V.getD k [] = if 3 ≤ k ∧ k < 6 then urow (k - 3) else z10 := by
  interval_cases k <;> rfl

theorem gate1_zero (ev : Ctx u η M fl ex p w) (j : ℕ) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  have hz : |ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0| ≤ 1 / 90 :=
    ardot_z10 ev (init_close ev j) (p.g 0 0) (ev.hp.g 0 0)
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by norm_num [head1]
  have hb := asw_c ev head1.gb (ev.hp.gb 0 0) (by rw [hgb]; norm_num)
  rw [hgb] at hb
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  unfold AHead.gate
  apply gate_zero_of ev
  · linarith
  · linarith

theorem mem_cs1 (ev : Ctx u η M fl ex p w) (i j : ℕ) : j ∈ cs1 fl p w i ↔ j < i := by
  unfold cs1
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  exact ⟨fun h => h.1, fun h => ⟨h, gate1_zero ev j⟩⟩

theorem cs1_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs1 fl p w i).Nodup :=
  AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs1_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs1 fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs1 fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
  omega

theorem cont1 (ev : Ctx u η M fl ex p w) (i k : ℕ) (hi : i ≤ w.length) (hk : k ≤ w.length) :
    |pdot fl (net.init fl p w i) (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 5 :=
  content_zero ev head1 rfl (net.init fl p w) (fun j => id0 w j) (fun j _ => init_close ev j)
    (p.A 0 0) (ev.hp.A 0 0) i k hi hk

theorem win1 (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length)
    (f F : ℕ → ℝ) {ε B : ℝ} (hf : ∀ j, j < i → |f j - F j| ≤ ε)
    (hF : ∀ j, j < i → |F j| ≤ B) (hB : B + ε ≤ 4) :
    |savg fl ex (cs1 fl p w i) (sc1 fl p w i) f - F (i - 1)| ≤ ε + (B + ε) / 100 + 1 / 2 ^ 90 := by
  have hj : i - 1 ∈ cs1 fl p w i := (mem_cs1 ev i (i - 1)).mpr (by omega)
  have hcont := cont1 ev
  have hgap : ∀ k' ∈ cs1 fl p w i, k' ≠ i - 1 →
      sc1 fl p w i k' ≤ sc1 fl p w i (i - 1) - 16 * (ndist (i - 1) k' : ℝ) := by
    intro k' hk' hne
    have hk'i : k' < i := (mem_cs1 ev i k').mp hk'
    have hlt : k' < i - 1 := by omega
    rw [ndist_cast]
    have hg := score_gap ev head1 head1_m (ev.hp.m 0 0) (p.A 0 0) (net.init fl p w) hcont i
      (i - 1) k' hi (by omega) hlt
    have h1 : (k' : ℝ) + 1 ≤ ((i - 1 : ℕ) : ℝ) := by
      have h : k' + 1 ≤ i - 1 := hlt
      exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact hg
  have hS : ∀ k' ∈ cs1 fl p w i, |sc1 fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    have := (mem_cs1 ev i k').mp hk'
    exact score_abs ev head1 head1_m (ev.hp.m 0 0) (p.A 0 0) (net.init fl p w) hcont i k' hi
      (by omega)
  exact soft_win ev (cs1 fl p w i) (sc1 fl p w i) f F (cs1_nodup fl p w i)
    (cs1_len fl p w i hi) (i - 1) hj hgap hS (fun j hj' => hf j ((mem_cs1 ev i j).mp hj'))
    (fun j hj' => hF j ((mem_cs1 ev i j).mp hj')) hB

theorem v0_unit (ev : Ctx u η M fl ex p w) (j c : ℕ) (hc : c < 3) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl (urow c) (net.init fl p w j) d 0 0 - id0 w j c| ≤ 1 / 300 := by
  obtain ⟨hl, hent⟩ := init_ent ev j
  have key := dot_gen ev (urow c) (fun k => if k = c then (1 : ℚ) else 0) rfl (W := 1)
    (by intro k hk; split_ifs <;> norm_num) (by norm_num) (net.init fl p w j) hl
    (id0 w j) (fun _ => 1 / 990) (id0 w j)
    (fun k hk => ⟨hent k hk, (abs_of_nonneg (id0_nonneg w j k)).le⟩)
    (E := 1 / 990) (Xb := 1) (fun k hk => ⟨le_refl _, id0_le_one w j k⟩) (by norm_num)
    (by norm_num) (by norm_num) d hd
  obtain ⟨k1, -⟩ := key
  rw [sum10_unit c (by omega), sum10_unit_abs c (by omega), sum10_const] at k1
  have hs := id0_sum' w j
  norm_num at k1
  linarith

theorem v0_zero (ev : Ctx u η M fl ex p w) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl z10 (net.init fl p w j) d 0 0| ≤ 1 / 700 := by
  obtain ⟨hl, hent⟩ := init_ent ev j
  have key := dot_gen ev z10 (fun _ => (0 : ℚ)) rfl (W := 0) (by intro k hk; simp) (le_refl _)
    (net.init fl p w j) hl (id0 w j) (fun _ => 1 / 990) (id0 w j)
    (fun k hk => ⟨hent k hk, (abs_of_nonneg (id0_nonneg w j k)).le⟩)
    (E := 1 / 990) (Xb := 1) (fun k hk => ⟨le_refl _, id0_le_one w j k⟩) (by norm_num)
    (by norm_num) (by norm_num) d hd
  obtain ⟨k1, -⟩ := key
  rw [sum10_zero, sum10_zero_abs, sum10_const, sub_zero] at k1
  have hs := id0_sum' w j
  norm_num at k1
  linarith

theorem att1_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 10) :
    |att1 fl ex p w i k - (if 3 ≤ k ∧ k < 6 then id0 w (i - 1) (k - 3) else 0)| ≤
      (if 3 ≤ k ∧ k < 6 then 1 / 74 else 1 / 680) := by
  by_cases hi0 : i = 0
  · subst hi0
    have hcs : cs1 fl p w 0 = [] := by
      unfold cs1 AHead.cands
      simp [head1, cand]
    have hz : att1 fl ex p w 0 k = 0 := by
      unfold att1
      rw [hcs]
      exact soft_zeros ev.hr (by simp)
    rw [hz]
    by_cases hk3 : 3 ≤ k ∧ k < 6
    · rw [if_pos hk3, if_pos hk3, show (0 : ℕ) - 1 = 0 from rfl, id0_zero_tok]; norm_num
    · rw [if_neg hk3, if_neg hk3]; norm_num
  · have hi1 : 1 ≤ i := Nat.pos_of_ne_zero hi0
    by_cases hk3 : 3 ≤ k ∧ k < 6
    · rw [if_pos hk3, if_pos hk3]
      have hrow : head1.V.getD k [] = urow (k - 3) := by
        rw [head1_V k hk, if_pos hk3]
      unfold att1
      have hw := win1 ev i hi1 hi
        (fun j => ardot fl (head1.V.getD k []) (net.init fl p w j) (p.V 0 0 k) 0 0)
        (fun j => id0 w j (k - 3)) (ε := 1 / 300) (B := 1)
        (fun j _ => by
          show |ardot fl (head1.V.getD k []) (net.init fl p w j) (p.V 0 0 k) 0 0 -
            id0 w j (k - 3)| ≤ 1 / 300
          rw [hrow]
          exact v0_unit ev j (k - 3) (by omega) (p.V 0 0 k) (ev.hp.V 0 0 k))
        (fun j _ => by
          show |id0 w j (k - 3)| ≤ 1
          rw [abs_of_nonneg (id0_nonneg w j (k - 3))]
          exact id0_le_one w j (k - 3)) (by norm_num)
      refine le_trans hw ?_
      norm_num
    · rw [if_neg hk3, if_neg hk3]
      have hrow : head1.V.getD k [] = z10 := by
        rw [head1_V k hk, if_neg hk3]
      unfold att1
      have hw := win1 ev i hi1 hi
        (fun j => ardot fl (head1.V.getD k []) (net.init fl p w j) (p.V 0 0 k) 0 0)
        (fun _ => 0) (ε := 1 / 700) (B := 0)
        (fun j _ => by
          show |ardot fl (head1.V.getD k []) (net.init fl p w j) (p.V 0 0 k) 0 0 - 0| ≤ 1 / 700
          rw [hrow, sub_zero]
          exact v0_zero ev j (p.V 0 0 k) (ev.hp.V 0 0 k))
        (fun j _ => by simp) (by norm_num)
      refine le_trans hw ?_
      norm_num

noncomputable def hA1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
    (net.init fl p w) i

noncomputable def mlp1 (fl : ℝ → ℝ) (p : APert) : Vec :=
  araffine fl blk1.W2 blk1.b2 [] (p.W2 0) (p.b2 0) 0

noncomputable def st1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  blk1.apply fl ex p 0 (w.length + 1) (net.init fl p w)

theorem st1_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    st1 fl ex p w i = radd fl (radd fl (net.init fl p w i) (hA1 fl ex p w i)) (mlp1 fl p) := rfl

theorem hA1_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    (hA1 fl ex p w i).length = 10 := by
  unfold hA1
  rw [attn_length]; rfl

theorem hA1_getD (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i k : ℕ) (hk : k < 10) :
    (hA1 fl ex p w i).getD k 0 = att1 fl ex p w i k := by
  unfold hA1
  rw [attn_getD head1 fl ex _ _ _ _ _ _ _ i k (by show k < 10; exact hk)]
  rfl

theorem mlp1_len (fl : ℝ → ℝ) (p : APert) : (mlp1 fl p).length = 10 := by
  unfold mlp1
  rw [araffine_length fl [] (p.W2 0) (p.b2 0) blk1.W2 blk1.b2 rfl 0]
  rfl

theorem mlp1_ent (ev : Ctx u η M fl ex p w) (k : ℕ) (hk : k < 10) :
    |(mlp1 fl p).getD k 0| ≤ 1 / 980 := by
  unfold mlp1
  rw [araffine_getD fl [] (p.W2 0) (p.b2 0) blk1.W2 blk1.b2 0 k (by show k < 10; exact hk)
    (by show k < 10; exact hk)]
  have e1 : blk1.W2.getD k [] = [] := by
    interval_cases k <;> rfl
  have e2 : blk1.b2.getD k 0 = 0 := rowf_getD (fun _ => 0) hk
  rw [e1, e2, ardot_nil']
  exact small_ent ev (ev.hp.b2 0 (0 + k))

theorem st1_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (st1 fl ex p w i).length = 10 ∧
    ∀ k, k < 10 → |(st1 fl ex p w i).getD k 0 - id1 w i k| ≤
      (if 3 ≤ k ∧ k < 6 then 1 / 60 else 1 / 250) := by
  obtain ⟨hx0, hx0e⟩ := init_ent ev i
  have hAl := hA1_len fl ex p w i
  have hMl := mlp1_len fl p
  have hYl : (radd fl (net.init fl p w i) (hA1 fl ex p w i)).length = 10 := by
    rw [radd_length fl (net.init fl p w i) (hA1 fl ex p w i) (by rw [hx0, hAl])]
    exact hx0
  rw [st1_eq]
  refine ⟨by
    rw [radd_length fl (radd fl (net.init fl p w i) (hA1 fl ex p w i)) (mlp1 fl p)
      (by rw [hYl, hMl])]
    exact hYl, ?_⟩
  intro k hk
  have g1 := radd_getD fl (radd fl (net.init fl p w i) (hA1 fl ex p w i)) (mlp1 fl p) k
    (by omega) (by omega)
  have g2 := radd_getD fl (net.init fl p w i) (hA1 fl ex p w i) k (by omega) (by omega)
  rw [g1, g2, hA1_getD fl ex p w i k hk]
  have h1 := hx0e k hk
  have h2 := att1_near ev i hi k hk
  have h3 := mlp1_ent ev k hk
  have hsp := id1_split w i k hk
  have n1 := id0_nonneg w i k
  have n2 := id0_le_one w i k
  have hF1 : 0 ≤ (if 3 ≤ k ∧ k < 6 then id0 w (i - 1) (k - 3) else 0) ∧
      (if 3 ≤ k ∧ k < 6 then id0 w (i - 1) (k - 3) else 0) ≤ 1 := by
    split_ifs
    · exact ⟨id0_nonneg _ _ _, id0_le_one _ _ _⟩
    · norm_num
  have hε : (if 3 ≤ k ∧ k < 6 then (1 : ℝ) / 74 else 1 / 680) ≤ 1 := by
    split_ifs <;> norm_num
  have key := add2 ev (hh := id0 w i k)
    (f := if 3 ≤ k ∧ k < 6 then id0 w (i - 1) (k - 3) else 0)
    (e := 1 / 990) (ea := if 3 ≤ k ∧ k < 6 then 1 / 74 else 1 / 680) (em := 1 / 980) h1 h2 h3
    (by
      obtain ⟨a1, a2⟩ := abs_le.mp h1
      rw [abs_le]; constructor <;> linarith)
    (by
      obtain ⟨a1, a2⟩ := abs_le.mp h2
      rw [abs_le]; constructor <;> linarith)
    (by
      obtain ⟨a1, a2⟩ := abs_le.mp h3
      rw [abs_le]; constructor <;> linarith)
  rw [hsp]
  by_cases hk3 : 3 ≤ k ∧ k < 6
  · simp only [if_pos hk3] at key ⊢
    refine le_trans key ?_
    norm_num
  · simp only [if_neg hk3] at key ⊢
    refine le_trans key ?_
    norm_num

/-! ### Block 2 -/

noncomputable def es1 (k : ℕ) : ℝ := if 3 ≤ k ∧ k < 6 then 1 / 60 else 1 / 250

theorem es1_nonneg (k : ℕ) : 0 ≤ es1 k := by
  unfold es1; split_ifs <;> norm_num

theorem es1_le (k : ℕ) : es1 k ≤ 1 / 60 := by
  unfold es1; split_ifs <;> norm_num

theorem sum10_es1 : sum10 es1 = 7 / 250 + 3 / 60 := by
  unfold sum10 es1; norm_num

theorem es1_P (c : ℕ) (hc : c < 3) : es1 (3 + c) = 1 / 60 := by
  unfold es1; rw [if_pos (by omega)]

theorem st1_close (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    Close (st1 fl ex p w j) (vec10 (id1 w j)) (1 / 60) 1 := by
  obtain ⟨hl, hent⟩ := st1_ent ev j hj
  apply close_vec10 hl
  intro k hk
  refine ⟨le_trans (hent k hk) ?_, ?_⟩
  · split_ifs <;> norm_num
  · rw [abs_of_nonneg (id1_nonneg w j k)]; exact id1_le_one w j k

theorem head2_m (c : ℕ) : (((head2 c).m : ℚ) : ℝ) = 24 := by norm_num [head2]
theorem head2_Vlen (c : ℕ) : (head2 c).V.length = 10 := rfl
theorem head2_V (c k : ℕ) (hk : k < 10) :
    (head2 c).V.getD k [] = if k = 6 + c then vrow else z10 := by
  interval_cases k <;> rfl

theorem gate2_dot (ev : Ctx u η M fl ex p w) (c : ℕ) (hc : c < 3) (j : ℕ) (hj : j ≤ w.length)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl (gGate c) (st1 fl ex p w j) d 0 0 - (-(id1 w j (3 + c)))| ≤ 1 / 25 := by
  obtain ⟨hl, hent⟩ := st1_ent ev j hj
  have key := dot_gen ev (gGate c) (fun k => if k = 3 + c then (-1 : ℚ) else 0) rfl (W := 1)
    (by intro k hk; split_ifs <;> norm_num) (by norm_num) (st1 fl ex p w j) hl (id1 w j) es1
    (id1 w j) (fun k hk => ⟨hent k hk, (abs_of_nonneg (id1_nonneg w j k)).le⟩)
    (E := 1 / 60) (Xb := 1) (fun k hk => ⟨es1_le k, id1_le_one w j k⟩) (by norm_num)
    (by norm_num) (by norm_num) d hd
  obtain ⟨k1, -⟩ := key
  rw [sum10_gate c hc, sum10_gate_abs c hc, sum10_es1, es1_P c hc] at k1
  have hs := id1_sum' w j
  refine le_trans k1 ?_
  norm_num
  linarith

theorem gate2_val (ev : Ctx u η M fl ex p w) (c : ℕ) (hc : c < 3) (j : ℕ) (hj : j ≤ w.length) :
    |(ardot fl (head2 c).g (st1 fl ex p w j) (p.g 1 c) 0 0 + asw fl (head2 c).gb (p.gb 1 c)) -
      (1 / 2 - id1 w j (3 + c))| ≤ 1 / 20 := by
  have h1 : |ardot fl (head2 c).g (st1 fl ex p w j) (p.g 1 c) 0 0 - (-(id1 w j (3 + c)))| ≤ 1 / 25 :=
    gate2_dot ev c hc j hj (p.g 1 c) (ev.hp.g 1 c)
  have hgb : (((head2 c).gb : ℚ) : ℝ) = 1 / 2 := by norm_num [head2]
  have h2 := asw_c ev (head2 c).gb (ev.hp.gb 1 c) (by rw [hgb]; norm_num)
  rw [hgb] at h2
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  rw [abs_le]; constructor <;> linarith

theorem gate2_zero (ev : Ctx u η M fl ex p w) (c : ℕ) (hc : c < 3) (j : ℕ) (hj : j ≤ w.length)
    (hf : id1 w j (3 + c) = 1) :
    (head2 c).gate fl (p.g 1 c) (p.gb 1 c) (st1 fl ex p w j) = 0 := by
  have hv := gate2_val ev c hc j hj
  rw [hf] at hv
  obtain ⟨v1, v2⟩ := abs_le.mp hv
  unfold AHead.gate
  apply gate_zero_of ev
  · linarith
  · linarith

theorem gate2_pos (ev : Ctx u η M fl ex p w) (c : ℕ) (hc : c < 3) (j : ℕ) (hj : j ≤ w.length)
    (hf : id1 w j (3 + c) = 0) :
    (head2 c).gate fl (p.g 1 c) (p.gb 1 c) (st1 fl ex p w j) ≠ 0 := by
  have hv := gate2_val ev c hc j hj
  rw [hf] at hv
  obtain ⟨v1, v2⟩ := abs_le.mp hv
  unfold AHead.gate
  apply gate_pos_of ev
  · linarith
  · linarith

theorem mem_cs2 (ev : Ctx u η M fl ex p w) (c : ℕ) (hc : c < 3) (i : ℕ) (hi : i ≤ w.length)
    (j : ℕ) :
    j ∈ (head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1) (st1 fl ex p w) i ↔
      j ≤ i ∧ tokAt w (j - 1) = c + 1 := by
  rw [AHead.mem_cands]
  have hmask : (head2 c).mask = Mask.causal := rfl
  rw [hmask, Lane4.Seq.mem_cand_causal]
  constructor
  · rintro ⟨hji, hg⟩
    refine ⟨hji, ?_⟩
    by_contra hne
    have hflag : id1 w j (3 + c) = 0 := by
      rw [id1_P w j c hc]; unfold ind; rw [if_neg hne]
    exact gate2_pos ev c hc j (by omega) hflag hg
  · rintro ⟨hji, ht⟩
    refine ⟨hji, ?_⟩
    have hflag : id1 w j (3 + c) = 1 := by
      rw [id1_P w j c hc]; unfold ind; rw [if_pos ht]
    exact gate2_zero ev c hc j (by omega) hflag

def Jc (w : List ℕ) (c i : ℕ) : ℕ := Nat.findGreatest (fun k => tokAt w (k - 1) = c + 1) i

noncomputable def Fv (w : List ℕ) (j : ℕ) : ℝ := 2 * (ind (tokAt w j) 2 + ind (tokAt w j) 3)

noncomputable def Fh (w : List ℕ) (c i : ℕ) : ℝ := Fv w (Jc w c i)

theorem Fv_nonneg (w : List ℕ) (j : ℕ) : 0 ≤ Fv w j := by
  unfold Fv
  have := ind_nonneg (tokAt w j) 2
  have := ind_nonneg (tokAt w j) 3
  linarith

theorem Fv_le_two (w : List ℕ) (j : ℕ) : Fv w j ≤ 2 := by
  unfold Fv
  have h1 := ind_sum (tokAt w j)
  have h2 := ind_nonneg (tokAt w j) 1
  linarith

theorem Fh_nonneg (w : List ℕ) (c i : ℕ) : 0 ≤ Fh w c i := Fv_nonneg _ _
theorem Fh_le_two (w : List ℕ) (c i : ℕ) : Fh w c i ≤ 2 := Fv_le_two _ _

theorem v2_v (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl vrow (st1 fl ex p w j) d 0 0 - Fv w j| ≤ 1 / 52 := by
  obtain ⟨hl, hent⟩ := st1_ent ev j hj
  have key := dot_gen ev vrow (fun k => if k = 1 ∨ k = 2 then (2 : ℚ) else 0) rfl (W := 2)
    (by intro k hk; split_ifs <;> norm_num) (by norm_num) (st1 fl ex p w j) hl (id1 w j) es1
    (id1 w j) (fun k hk => ⟨hent k hk, (abs_of_nonneg (id1_nonneg w j k)).le⟩)
    (E := 1 / 60) (Xb := 1) (fun k hk => ⟨es1_le k, id1_le_one w j k⟩) (by norm_num)
    (by norm_num) (by norm_num) d hd
  obtain ⟨k1, -⟩ := key
  rw [sum10_vrow, sum10_vrow_abs, sum10_es1] at k1
  have h1 : id1 w j 1 = ind (tokAt w j) 2 := id1_O w j 1 (by norm_num)
  have h2 : id1 w j 2 = ind (tokAt w j) 3 := id1_O w j 2 (by norm_num)
  have hF : Fv w j = 2 * id1 w j 1 + 2 * id1 w j 2 := by
    unfold Fv; rw [h1, h2]; ring
  rw [hF]
  have hs := id1_sum' w j
  have e1 : es1 1 = 1 / 250 := by unfold es1; norm_num
  have e2 : es1 2 = 1 / 250 := by unfold es1; norm_num
  rw [e1, e2] at k1
  refine le_trans k1 ?_
  norm_num
  linarith

theorem v2_z (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl z10 (st1 fl ex p w j) d 0 0| ≤ 1 / 400 := by
  obtain ⟨hl, hent⟩ := st1_ent ev j hj
  have key := dot_gen ev z10 (fun _ => (0 : ℚ)) rfl (W := 0) (by intro k hk; simp) (le_refl _)
    (st1 fl ex p w j) hl (id1 w j) es1 (id1 w j)
    (fun k hk => ⟨hent k hk, (abs_of_nonneg (id1_nonneg w j k)).le⟩)
    (E := 1 / 60) (Xb := 1) (fun k hk => ⟨es1_le k, id1_le_one w j k⟩) (by norm_num)
    (by norm_num) (by norm_num) d hd
  obtain ⟨k1, -⟩ := key
  rw [sum10_zero, sum10_zero_abs, sum10_es1, sub_zero] at k1
  have hs := id1_sum' w j
  refine le_trans k1 ?_
  norm_num
  linarith

noncomputable def hd2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (c i : ℕ) : Vec :=
  (head2 c).attn fl ex (p.A 1 c) (p.V 1 c) (p.m 1 c) (p.g 1 c) (p.gb 1 c) (w.length + 1)
    (st1 fl ex p w) i

theorem hd2_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (c i : ℕ) :
    (hd2 fl ex p w c i).length = 10 := by
  unfold hd2
  rw [attn_length]
  rfl

theorem head2_out (ev : Ctx u η M fl ex p w) (c : ℕ) (hc : c < 3) (i : ℕ) (hi : i ≤ w.length)
    (k : ℕ) (hk : k < 10) :
    |(hd2 fl ex p w c i).getD k 0 - (if k = 6 + c then Fh w c i else 0)| ≤
      (if k = 6 + c then 1 / 25 else 1 / 380) := by
  unfold hd2
  rw [attn_getD (head2 c) fl ex (p.A 1 c) (p.V 1 c) (p.m 1 c) (p.g 1 c) (p.gb 1 c)
    (w.length + 1) (st1 fl ex p w) i k (by rw [head2_Vlen]; exact hk)]
  have hcont : ∀ i' k', i' ≤ w.length → k' ≤ w.length →
      |pdot fl (st1 fl ex p w i') (armat fl (head2 c).A (st1 fl ex p w k') (p.A 1 c) 0) 0| ≤
        1 / 5 :=
    fun i' k' hi' hk' => content_zero ev (head2 c) rfl (st1 fl ex p w) (fun j => id1 w j)
      (fun j hj => st1_close ev j hj) (p.A 1 c) (ev.hp.A 1 c) i' k' hi' hk'
  have hmem := mem_cs2 ev c hc i hi
  have hnd := AHead.cands_nodup (head2 c) fl (p.g 1 c) (p.gb 1 c) (w.length + 1)
    (st1 fl ex p w) i
  have hlen : ((head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1) (st1 fl ex p w) i).length
      ≤ w.length + 1 := by
    have h1 : ((head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1) (st1 fl ex p w) i).length ≤
        (cand (head2 c).mask (w.length + 1) i).length := List.length_filter_le _ _
    have h2 : (cand (head2 c).mask (w.length + 1) i).length = i + 1 := by
      have : (head2 c).mask = Mask.causal := rfl
      rw [this]; simp [cand]
    omega
  by_cases hne : ∃ j, j ≤ i ∧ tokAt w (j - 1) = c + 1
  · obtain ⟨j0, hj0i, hj0⟩ := hne
    have hJ : tokAt w (Jc w c i - 1) = c + 1 :=
      Nat.findGreatest_spec (P := fun k => tokAt w (k - 1) = c + 1) hj0i hj0
    have hJi : Jc w c i ≤ i := Nat.findGreatest_le i
    have hJmem := (hmem (Jc w c i)).mpr ⟨hJi, hJ⟩
    have hmax : ∀ k' ∈ (head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1)
        (st1 fl ex p w) i, k' ≤ Jc w c i := fun k' hk' =>
      Nat.le_findGreatest (P := fun k => tokAt w (k - 1) = c + 1) ((hmem k').mp hk').1
        ((hmem k').mp hk').2
    have hgap : ∀ k' ∈ (head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1)
        (st1 fl ex p w) i, k' ≠ Jc w c i →
        (fun j => (head2 c).score fl (p.A 1 c) (p.m 1 c) (st1 fl ex p w) i j) k' ≤
          (fun j => (head2 c).score fl (p.A 1 c) (p.m 1 c) (st1 fl ex p w) i j) (Jc w c i) -
            16 * (ndist (Jc w c i) k' : ℝ) := by
      intro k' hk' hne'
      have hlt : k' < Jc w c i := lt_of_le_of_ne (hmax k' hk') hne'
      show (head2 c).score fl (p.A 1 c) (p.m 1 c) (st1 fl ex p w) i k' ≤
        (head2 c).score fl (p.A 1 c) (p.m 1 c) (st1 fl ex p w) i (Jc w c i) -
          16 * (ndist (Jc w c i) k' : ℝ)
      rw [ndist_cast]
      have hg := score_gap ev (head2 c) (head2_m c) (ev.hp.m 1 c) (p.A 1 c) (st1 fl ex p w)
        hcont i (Jc w c i) k' hi (by omega) hlt
      have h1 : (k' : ℝ) + 1 ≤ ((Jc w c i : ℕ) : ℝ) := by
        have h : k' + 1 ≤ Jc w c i := hlt
        exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      exact hg
    have hS : ∀ k' ∈ (head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1)
        (st1 fl ex p w) i,
        |(fun j => (head2 c).score fl (p.A 1 c) (p.m 1 c) (st1 fl ex p w) i j) k'| ≤
          28 * ((w.length + 1 : ℕ) : ℝ) := by
      intro k' hk'
      have := ((hmem k').mp hk').1
      exact score_abs ev (head2 c) (head2_m c) (ev.hp.m 1 c) (p.A 1 c) (st1 fl ex p w) hcont i k'
        hi (by omega)
    by_cases hkc : k = 6 + c
    · rw [if_pos hkc, if_pos hkc]
      have hrow : (head2 c).V.getD k [] = vrow := by
        rw [head2_V c k hk, if_pos hkc]
      have hw := soft_win ev
        ((head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1) (st1 fl ex p w) i)
        (fun j => (head2 c).score fl (p.A 1 c) (p.m 1 c) (st1 fl ex p w) i j)
        (fun j => ardot fl ((head2 c).V.getD k []) (st1 fl ex p w j) (p.V 1 c k) 0 0)
        (fun j => Fv w j) hnd hlen (Jc w c i) hJmem hgap hS (ε := 1 / 52) (B := 2)
        (fun k' hk' => by
          show |ardot fl ((head2 c).V.getD k []) (st1 fl ex p w k') (p.V 1 c k) 0 0 - Fv w k'| ≤
            1 / 52
          rw [hrow]
          exact v2_v ev k' (by have := ((hmem k').mp hk').1; omega) (p.V 1 c k) (ev.hp.V 1 c k))
        (fun k' hk' => by
          show |Fv w k'| ≤ 2
          rw [abs_of_nonneg (Fv_nonneg w k')]
          exact Fv_le_two w k')
        (by norm_num)
      refine le_trans hw ?_
      norm_num
    · rw [if_neg hkc, if_neg hkc]
      have hrow : (head2 c).V.getD k [] = z10 := by
        rw [head2_V c k hk, if_neg hkc]
      have hw := soft_win ev
        ((head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1) (st1 fl ex p w) i)
        (fun j => (head2 c).score fl (p.A 1 c) (p.m 1 c) (st1 fl ex p w) i j)
        (fun j => ardot fl ((head2 c).V.getD k []) (st1 fl ex p w j) (p.V 1 c k) 0 0)
        (fun _ => 0) hnd hlen (Jc w c i) hJmem hgap hS (ε := 1 / 400) (B := 0)
        (fun k' hk' => by
          show |ardot fl ((head2 c).V.getD k []) (st1 fl ex p w k') (p.V 1 c k) 0 0 - 0| ≤
            1 / 400
          rw [hrow, sub_zero]
          exact v2_z ev k' (by have := ((hmem k').mp hk').1; omega) (p.V 1 c k) (ev.hp.V 1 c k))
        (fun k' hk' => by simp) (by norm_num)
      refine le_trans hw ?_
      norm_num
  · have hz : savg fl ex
        ((head2 c).cands fl (p.g 1 c) (p.gb 1 c) (w.length + 1) (st1 fl ex p w) i)
        (fun j => (head2 c).score fl (p.A 1 c) (p.m 1 c) (st1 fl ex p w) i j)
        (fun j => ardot fl ((head2 c).V.getD k []) (st1 fl ex p w j) (p.V 1 c k) 0 0) = 0 :=
      soft_zeros ev.hr (fun k' hk' => absurd ((hmem k').mp hk')
        (by rintro ⟨h1, h2⟩; exact hne ⟨k', h1, h2⟩))
    rw [hz]
    have hJ0 : Jc w c i = 0 := by
      apply Nat.findGreatest_eq_zero_iff.mpr
      intro m hm0 hmi hP
      exact hne ⟨m, hmi, hP⟩
    have hFh : Fh w c i = 0 := by
      unfold Fh Fv
      rw [hJ0, Lane4.Seq.tokAt_zero]
      norm_num [ind]
    rw [hFh]
    split_ifs <;> norm_num

/-! #### The state after the heads of block 2 -/

noncomputable def yy (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  radd fl (radd fl (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i)) (hd2 fl ex p w 1 i))
    (hd2 fl ex p w 2 i)

noncomputable def hidv (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  (araffine fl blk2.W1 blk2.b1 (yy fl ex p w i) (p.W1 1) (p.b1 1) 0).map Lane4.relu

noncomputable def mlp2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  araffine fl blk2.W2 blk2.b2 (hidv fl ex p w i) (p.W2 1) (p.b2 1) 0

noncomputable def zz (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  radd fl (yy fl ex p w i) (mlp2 fl ex p w i)

theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    net.run fl ex p w i = zz fl ex p w i := rfl

theorem yy_len (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (yy fl ex p w i).length = 10 := by
  have h1 := (st1_ent ev i hi).1
  have a0 := hd2_len fl ex p w 0 i
  have a1 := hd2_len fl ex p w 1 i
  have a2 := hd2_len fl ex p w 2 i
  have l1 : (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i)).length = 10 := by
    rw [radd_length fl (st1 fl ex p w i) (hd2 fl ex p w 0 i) (by rw [h1, a0])]
    exact h1
  have l2 : (radd fl (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i))
      (hd2 fl ex p w 1 i)).length = 10 := by
    rw [radd_length fl (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i)) (hd2 fl ex p w 1 i)
      (by rw [l1, a1])]
    exact l1
  unfold yy
  rw [radd_length fl (radd fl (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i))
    (hd2 fl ex p w 1 i)) (hd2 fl ex p w 2 i) (by rw [l2, a2])]
  exact l2

theorem yy_getD (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 10) :
    (yy fl ex p w i).getD k 0 =
      fl (fl (fl ((st1 fl ex p w i).getD k 0 + (hd2 fl ex p w 0 i).getD k 0) +
        (hd2 fl ex p w 1 i).getD k 0) + (hd2 fl ex p w 2 i).getD k 0) := by
  have h1 := (st1_ent ev i hi).1
  have a0 := hd2_len fl ex p w 0 i
  have a1 := hd2_len fl ex p w 1 i
  have a2 := hd2_len fl ex p w 2 i
  have l1 : (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i)).length = 10 := by
    rw [radd_length fl (st1 fl ex p w i) (hd2 fl ex p w 0 i) (by rw [h1, a0])]
    exact h1
  have l2 : (radd fl (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i))
      (hd2 fl ex p w 1 i)).length = 10 := by
    rw [radd_length fl (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i)) (hd2 fl ex p w 1 i)
      (by rw [l1, a1])]
    exact l1
  unfold yy
  rw [radd_getD fl (radd fl (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i))
      (hd2 fl ex p w 1 i)) (hd2 fl ex p w 2 i) k (by omega) (by omega),
    radd_getD fl (radd fl (st1 fl ex p w i) (hd2 fl ex p w 0 i)) (hd2 fl ex p w 1 i) k
      (by omega) (by omega),
    radd_getD fl (st1 fl ex p w i) (hd2 fl ex p w 0 i) k (by omega) (by omega)]

/-! #### Ideal values of the state after the heads -/

noncomputable def Gv (w : List ℕ) (i k : ℕ) : ℝ :=
  if k = 6 then Fh w 0 i else if k = 7 then Fh w 1 i else if k = 8 then Fh w 2 i else 0

noncomputable def yid (w : List ℕ) (i k : ℕ) : ℝ := id1 w i k + Gv w i k

noncomputable def esy (k : ℕ) : ℝ :=
  if k < 3 then 1 / 80 else if k < 6 then 1 / 40 else if k < 9 then 1 / 20 else 1 / 80

noncomputable def Xsy (k : ℕ) : ℝ := if k < 6 then 1 else if k < 9 then 2 else 0

theorem Gv_nonneg (w : List ℕ) (i k : ℕ) : 0 ≤ Gv w i k := by
  unfold Gv
  split_ifs <;> first | exact Fh_nonneg _ _ _ | norm_num

theorem Gv_le (w : List ℕ) (i k : ℕ) : Gv w i k ≤ 2 := by
  unfold Gv
  split_ifs <;> first | exact Fh_le_two _ _ _ | norm_num

theorem Gv_lt6 (w : List ℕ) (i k : ℕ) (hk : k < 6) : Gv w i k = 0 := by
  unfold Gv
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem Gv_ge9 (w : List ℕ) (i k : ℕ) (hk : 9 ≤ k) : Gv w i k = 0 := by
  unfold Gv
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem esy_le (k : ℕ) : esy k ≤ 1 / 20 := by
  unfold esy; split_ifs <;> norm_num

theorem esy_nonneg (k : ℕ) : 0 ≤ esy k := by
  unfold esy; split_ifs <;> norm_num

theorem Xsy_le (k : ℕ) : Xsy k ≤ 2 := by
  unfold Xsy; split_ifs <;> norm_num

theorem sum10_esy : sum10 esy = 11 / 40 := by
  unfold sum10 esy; norm_num

theorem sum10_Xsy : sum10 Xsy = 12 := by
  unfold sum10 Xsy; norm_num

theorem yid_nonneg (w : List ℕ) (i k : ℕ) : 0 ≤ yid w i k := by
  unfold yid
  have := id1_nonneg w i k
  have := Gv_nonneg w i k
  linarith

theorem yid_abs (w : List ℕ) (i k : ℕ) : |yid w i k| ≤ Xsy k := by
  rw [abs_of_nonneg (yid_nonneg w i k)]
  have hid := id1_nonneg w i k
  have hid1 := id1_le_one w i k
  have hg := Gv_nonneg w i k
  have hg2 := Gv_le w i k
  unfold yid Xsy
  by_cases h1 : k < 6
  · rw [if_pos h1, Gv_lt6 w i k h1]; linarith
  · rw [if_neg h1, id1_V w i k (by omega)]
    by_cases h2 : k < 9
    · rw [if_pos h2]; linarith
    · rw [if_neg h2, Gv_ge9 w i k (by omega)]; norm_num

theorem yid_split (w : List ℕ) (i k : ℕ) (hk : k < 10) :
    yid w i k = id1 w i k + (if k = 6 + 0 then Fh w 0 i else 0) +
      (if k = 6 + 1 then Fh w 1 i else 0) + (if k = 6 + 2 then Fh w 2 i else 0) := by
  unfold yid Gv
  interval_cases k <;> simp

theorem yid_O (w : List ℕ) (i c : ℕ) (hc : c < 3) : yid w i c = ind (tokAt w i) (c + 1) := by
  unfold yid
  rw [id1_O w i c hc, Gv_lt6 w i c (by omega), add_zero]

theorem yid_V (w : List ℕ) (i c : ℕ) (hc : c < 3) : yid w i (6 + c) = Fh w c i := by
  unfold yid
  rw [id1_V w i (6 + c) (by omega)]
  unfold Gv
  interval_cases c <;> simp

theorem yk_numeric (k : ℕ) (hk : k < 10) :
    (if 3 ≤ k ∧ k < 6 then (1 : ℝ) / 60 else 1 / 250) + (if k = 6 + 0 then (1 : ℝ) / 25 else 1 / 380)
      + (if k = 6 + 1 then (1 : ℝ) / 25 else 1 / 380) + (if k = 6 + 2 then (1 : ℝ) / 25 else 1 / 380)
      + 3 / 10 ^ 6 ≤ esy k := by
  interval_cases k <;> norm_num [esy]

theorem abs3 {x t e : ℝ} (h : |x - t| ≤ e) (h0 : 0 ≤ t) (h1 : t ≤ 2) (he : e ≤ 1) : |x| ≤ 3 := by
  obtain ⟨a, b⟩ := abs_le.mp h
  rw [abs_le]; constructor <;> linarith

theorem yy_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∀ k, k < 10 → |(yy fl ex p w i).getD k 0 - yid w i k| ≤ esy k := by
  intro k hk
  obtain ⟨hl1, hent1⟩ := st1_ent ev i hi
  have hx := hent1 k hk
  have h0 := head2_out ev 0 (by norm_num) i hi k hk
  have h1 := head2_out ev 1 (by norm_num) i hi k hk
  have h2 := head2_out ev 2 (by norm_num) i hi k hk
  have f0 : 0 ≤ (if k = 6 + 0 then Fh w 0 i else 0) ∧ (if k = 6 + 0 then Fh w 0 i else 0) ≤ 2 := by
    split_ifs
    · exact ⟨Fh_nonneg _ _ _, Fh_le_two _ _ _⟩
    · norm_num
  have f1 : 0 ≤ (if k = 6 + 1 then Fh w 1 i else 0) ∧ (if k = 6 + 1 then Fh w 1 i else 0) ≤ 2 := by
    split_ifs
    · exact ⟨Fh_nonneg _ _ _, Fh_le_two _ _ _⟩
    · norm_num
  have f2 : 0 ≤ (if k = 6 + 2 then Fh w 2 i else 0) ∧ (if k = 6 + 2 then Fh w 2 i else 0) ≤ 2 := by
    split_ifs
    · exact ⟨Fh_nonneg _ _ _, Fh_le_two _ _ _⟩
    · norm_num
  have bx : |(st1 fl ex p w i).getD k 0| ≤ 3 :=
    abs3 hx (id1_nonneg w i k) (by have := id1_le_one w i k; linarith)
      (by split_ifs <;> norm_num)
  have b0 : |(hd2 fl ex p w 0 i).getD k 0| ≤ 3 :=
    abs3 h0 f0.1 f0.2 (by split_ifs <;> norm_num)
  have b1 : |(hd2 fl ex p w 1 i).getD k 0| ≤ 3 :=
    abs3 h1 f1.1 f1.2 (by split_ifs <;> norm_num)
  have b2 : |(hd2 fl ex p w 2 i).getD k 0| ≤ 3 :=
    abs3 h2 f2.1 f2.2 (by split_ifs <;> norm_num)
  have key := y_chain ev (hh := id1 w i k) hx h0 h1 h2 bx b0 b1 b2
  rw [yy_getD ev i hi k hk, yid_split w i k hk]
  refine le_trans ?_ (yk_numeric k hk)
  exact key

/-! #### The MLP of block 2 -/

noncomputable def Rsum (w : List ℕ) (i : ℕ) : ℝ :=
  ind (tokAt w i) 1 * Fh w 0 i + ind (tokAt w i) 2 * Fh w 1 i + ind (tokAt w i) 3 * Fh w 2 i

theorem Rsum_nonneg (w : List ℕ) (i : ℕ) : 0 ≤ Rsum w i := by
  unfold Rsum
  have h1 := mul_nonneg (ind_nonneg (tokAt w i) 1) (Fh_nonneg w 0 i)
  have h2 := mul_nonneg (ind_nonneg (tokAt w i) 2) (Fh_nonneg w 1 i)
  have h3 := mul_nonneg (ind_nonneg (tokAt w i) 3) (Fh_nonneg w 2 i)
  linarith

theorem Rsum_le_two (w : List ℕ) (i : ℕ) : Rsum w i ≤ 2 := by
  unfold Rsum
  have h1 := mul_le_mul_of_nonneg_left (Fh_le_two w 0 i) (ind_nonneg (tokAt w i) 1)
  have h2 := mul_le_mul_of_nonneg_left (Fh_le_two w 1 i) (ind_nonneg (tokAt w i) 2)
  have h3 := mul_le_mul_of_nonneg_left (Fh_le_two w 2 i) (ind_nonneg (tokAt w i) 3)
  have hs := ind_sum (tokAt w i)
  linarith

theorem hid_dot (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc : c < 3)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl (w1row c) (yy fl ex p w i) d 0 0 -
      (5 / 2 * ind (tokAt w i) (c + 1) + Fh w c i)| ≤ 953 / 10000 := by
  have hyl := yy_len ev i hi
  have hyent := yy_ent ev i hi
  have key := dot_gen ev (w1row c)
    (fun k => if k = c then (5 / 2 : ℚ) else if k = 6 + c then 1 else 0) rfl (W := 5 / 2)
    (by intro k hk; split_ifs <;> norm_num) (by norm_num) (yy fl ex p w i) hyl (yid w i) esy Xsy
    (fun k hk => ⟨hyent k hk, yid_abs w i k⟩) (E := 1 / 20) (Xb := 2)
    (fun k hk => ⟨esy_le k, Xsy_le k⟩) (by norm_num) (by norm_num) (by norm_num) d hd
  obtain ⟨k1, -⟩ := key
  rw [sum10_w1 c hc, sum10_w1_abs c hc, sum10_Xsy, sum10_esy, yid_O w i c hc,
    yid_V w i c hc] at k1
  have e1 : esy c = 1 / 80 := by unfold esy; rw [if_pos hc]
  have e2 : esy (6 + c) = 1 / 20 := by
    unfold esy; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [e1, e2] at k1
  refine le_trans k1 ?_
  norm_num

theorem hidpre_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    (araffine fl blk2.W1 blk2.b1 (yy fl ex p w i) (p.W1 1) (p.b1 1) 0).length = 3 := by
  rw [araffine_length fl (yy fl ex p w i) (p.W1 1) (p.b1 1) blk2.W1 blk2.b1 rfl 0]
  rfl

theorem hidv_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    (hidv fl ex p w i).length = 3 := by
  unfold hidv
  rw [List.length_map]
  exact hidpre_len fl ex p w i

theorem hidpre_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc : c < 3) :
    |(araffine fl blk2.W1 blk2.b1 (yy fl ex p w i) (p.W1 1) (p.b1 1) 0).getD c 0 -
      (Fh w c i + 5 / 2 * (ind (tokAt w i) (c + 1) - 1))| ≤ 1 / 10 := by
  rw [araffine_getD fl (yy fl ex p w i) (p.W1 1) (p.b1 1) blk2.W1 blk2.b1 0 c
    (by show c < 3; exact hc) (by show c < 3; exact hc)]
  have e1 : blk2.W1.getD c [] = w1row c := by interval_cases c <;> rfl
  have e2 : blk2.b1.getD c 0 = -5 / 2 := by interval_cases c <;> rfl
  rw [e1, e2]
  have hk := hid_dot ev i hi c hc (p.W1 1 (0 + c)) (ev.hp.W1 1 (0 + c))
  have hb := asw_c ev (-5 / 2 : ℚ) (ev.hp.b1 1 (0 + c)) (by norm_num)
  have hq : (((-5 / 2 : ℚ)) : ℝ) = -5 / 2 := by norm_num
  rw [hq] at hb
  obtain ⟨a1, a2⟩ := abs_le.mp hk
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  have hind0 := ind_nonneg (tokAt w i) (c + 1)
  have hind1 := ind_le_one (tokAt w i) (c + 1)
  have hF0 := Fh_nonneg w c i
  have hF2 := Fh_le_two w c i
  have hfl := ev.fl16 (x := ardot fl (w1row c) (yy fl ex p w i) (p.W1 1 (0 + c)) 0 0 +
    asw fl (-5 / 2) (p.b1 1 (0 + c))) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨c1, c2⟩ := abs_le.mp hfl
  rw [abs_le]; constructor <;> linarith

theorem hid_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc : c < 3) :
    |(hidv fl ex p w i).getD c 0 - ind (tokAt w i) (c + 1) * Fh w c i| ≤
      ind (tokAt w i) (c + 1) * (1 / 10) := by
  unfold hidv
  rw [map_relu_getD (araffine fl blk2.W1 blk2.b1 (yy fl ex p w i) (p.W1 1) (p.b1 1) 0) c
    (by rw [hidpre_len fl ex p w i]; exact hc)]
  have hp := hidpre_ent ev i hi c hc
  generalize (araffine fl blk2.W1 blk2.b1 (yy fl ex p w i) (p.W1 1) (p.b1 1) 0).getD c 0 = pre
    at hp ⊢
  by_cases hsel : tokAt w i = c + 1
  · have hind : ind (tokAt w i) (c + 1) = 1 := by unfold ind; rw [if_pos hsel]
    rw [hind] at hp ⊢
    have h1 := relu_near hp
    have hF := Fh_nonneg w c i
    have h2 : Lane4.relu (Fh w c i + 5 / 2 * (1 - 1)) = Fh w c i := by
      rw [show Fh w c i + 5 / 2 * (1 - 1) = Fh w c i by ring]
      exact Lane4.relu_of_nonneg hF
    rw [h2] at h1
    rw [one_mul, one_mul]
    exact h1
  · have hind : ind (tokAt w i) (c + 1) = 0 := by unfold ind; rw [if_neg hsel]
    rw [hind] at hp ⊢
    obtain ⟨a1, a2⟩ := abs_le.mp hp
    have hF := Fh_le_two w c i
    have hpre : pre ≤ 0 := by linarith
    have hr : Lane4.relu pre = 0 := by unfold Lane4.relu; exact max_eq_right hpre
    rw [hr]
    norm_num

theorem dot3S (ev : Ctx u η M fl ex p w) (a0 a1 a2 : ℚ) {W : ℝ}
    (hW : |(a0 : ℝ)| ≤ W ∧ |(a1 : ℝ)| ≤ W ∧ |(a2 : ℝ)| ≤ W) (hW0 : 0 ≤ W)
    (x : List ℝ) (hx : x.length = 3) (hh e X : ℕ → ℝ)
    (hent : ∀ k, k < 3 → |x.getD k 0 - hh k| ≤ e k ∧ |hh k| ≤ X k)
    {E Xb : ℝ} (hE : ∀ k, k < 3 → e k ≤ E ∧ X k ≤ Xb) (hE0 : 0 ≤ E) (hX0 : 0 ≤ Xb)
    (hT : (W + 1) * (Xb + E + 1) ≤ 2 ^ 20) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000)
    (S : ℝ) (hS : (a0 : ℝ) * hh 0 + (a1 : ℝ) * hh 1 + (a2 : ℝ) * hh 2 = S) :
    |ardot fl [a0, a1, a2] x d 0 0 - S| ≤
      |(a0 : ℝ)| * e 0 + |(a1 : ℝ)| * e 1 + |(a2 : ℝ)| * e 2
        + 1 / 1000 * ((X 0 + X 1 + X 2) + (e 0 + e 1 + e 2))
        + 3 * (W + 1) * (Xb + E + 1) / 2 ^ 16 + 1 / 2 ^ 100 := by
  have := dot3 ev a0 a1 a2 hW hW0 x hx hh e X hent hE hE0 hX0 hT d hd
  rw [hS] at this
  exact this

theorem hent3 (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∀ c, c < 3 → |(hidv fl ex p w i).getD c 0 - ind (tokAt w i) (c + 1) * Fh w c i| ≤
        ind (tokAt w i) (c + 1) * (1 / 10) ∧
      |ind (tokAt w i) (c + 1) * Fh w c i| ≤ 2 * ind (tokAt w i) (c + 1) := by
  intro c hc
  refine ⟨hid_ent ev i hi c hc, ?_⟩
  rw [abs_of_nonneg (mul_nonneg (ind_nonneg _ _) (Fh_nonneg _ _ _))]
  have := mul_le_mul_of_nonneg_left (Fh_le_two w c i) (ind_nonneg (tokAt w i) (c + 1))
  linarith

theorem hE3 (w : List ℕ) (i : ℕ) :
    ∀ c, c < 3 → ind (tokAt w i) (c + 1) * (1 / 10) ≤ 1 / 10 ∧
      2 * ind (tokAt w i) (c + 1) ≤ 2 := by
  intro c hc
  have := ind_le_one (tokAt w i) (c + 1)
  constructor <;> linarith

theorem mo_dot0 (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl [0, 0, 0] (hidv fl ex p w i) d 0 0| ≤ 1 / 200 := by
  have hs := ind_sum (tokAt w i)
  have key := dot3S ev 0 0 0 (W := 0) ⟨by simp, by simp, by simp⟩ (le_refl _)
    (hidv fl ex p w i) (hidv_len fl ex p w i)
    (fun c => ind (tokAt w i) (c + 1) * Fh w c i) (fun c => ind (tokAt w i) (c + 1) * (1 / 10))
    (fun c => 2 * ind (tokAt w i) (c + 1)) (hent3 ev i hi) (E := 1 / 10) (Xb := 2)
    (hE3 w i) (by norm_num) (by norm_num) (by norm_num) d hd 0 (by simp)
  rw [sub_zero] at key
  refine le_trans key ?_
  norm_num
  linarith

theorem mo_dot1 (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (d : ℕ → ℝ)
    (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl [1, 1, 1] (hidv fl ex p w i) d 0 0 - Rsum w i| ≤ 41 / 400 := by
  have hs := ind_sum (tokAt w i)
  have key := dot3S ev 1 1 1 (W := 1) ⟨by norm_num, by norm_num, by norm_num⟩ (by norm_num)
    (hidv fl ex p w i) (hidv_len fl ex p w i)
    (fun c => ind (tokAt w i) (c + 1) * Fh w c i) (fun c => ind (tokAt w i) (c + 1) * (1 / 10))
    (fun c => 2 * ind (tokAt w i) (c + 1)) (hent3 ev i hi) (E := 1 / 10) (Xb := 2)
    (hE3 w i) (by norm_num) (by norm_num) (by norm_num) d hd (Rsum w i)
    (by unfold Rsum; norm_num)
  refine le_trans key ?_
  norm_num
  linarith

theorem mlp2_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    (mlp2 fl ex p w i).length = 10 := by
  unfold mlp2
  rw [araffine_length fl (hidv fl ex p w i) (p.W2 1) (p.b2 1) blk2.W2 blk2.b2 rfl 0]
  rfl

theorem mlp2_getD (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i k : ℕ) (hk : k < 10) :
    (mlp2 fl ex p w i).getD k 0 =
      fl (ardot fl (blk2.W2.getD k []) (hidv fl ex p w i) (p.W2 1 (0 + k)) 0 0 +
        asw fl (blk2.b2.getD k 0) (p.b2 1 (0 + k))) := by
  unfold mlp2
  exact araffine_getD fl (hidv fl ex p w i) (p.W2 1) (p.b2 1) blk2.W2 blk2.b2 0 k
    (by show k < 10; exact hk) (by show k < 10; exact hk)

theorem mlp_small (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 9) :
    |(mlp2 fl ex p w i).getD k 0| ≤ 1 / 100 := by
  rw [mlp2_getD fl ex p w i k (by omega)]
  have e1 : blk2.W2.getD k [] = [0, 0, 0] := by interval_cases k <;> rfl
  have e2 : blk2.b2.getD k 0 = 0 := rowf_getD (fun _ => 0) (by omega)
  rw [e1, e2]
  have hz := mo_dot0 ev i hi (p.W2 1 (0 + k)) (ev.hp.W2 1 (0 + k))
  have hb := asw_c ev (0 : ℚ) (ev.hp.b2 1 (0 + k)) (by simp)
  have hb' : |asw fl (0 : ℚ) (p.b2 1 (0 + k))| ≤ 1 / 990 := by simpa using hb
  obtain ⟨a1, a2⟩ := abs_le.mp hz
  obtain ⟨b1, b2⟩ := abs_le.mp hb'
  have hfl := ev.fl16 (x := ardot fl [0, 0, 0] (hidv fl ex p w i) (p.W2 1 (0 + k)) 0 0 +
    asw fl (0 : ℚ) (p.b2 1 (0 + k))) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨c1, c2⟩ := abs_le.mp hfl
  rw [abs_le]; constructor <;> linarith

theorem mlp9_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    |(mlp2 fl ex p w i).getD 9 0 - Rsum w i| ≤ 13 / 125 := by
  rw [mlp2_getD fl ex p w i 9 (by norm_num)]
  have e1 : blk2.W2.getD 9 [] = [1, 1, 1] := rfl
  have e2 : blk2.b2.getD 9 0 = 0 := rowf_getD (fun _ => 0) (by norm_num)
  rw [e1, e2]
  have hz := mo_dot1 ev i hi (p.W2 1 (0 + 9)) (ev.hp.W2 1 (0 + 9))
  have hb := asw_c ev (0 : ℚ) (ev.hp.b2 1 (0 + 9)) (by simp)
  have hb' : |asw fl (0 : ℚ) (p.b2 1 (0 + 9))| ≤ 1 / 990 := by simpa using hb
  have hR := Rsum_nonneg w i
  have hR2 := Rsum_le_two w i
  obtain ⟨a1, a2⟩ := abs_le.mp hz
  obtain ⟨b1, b2⟩ := abs_le.mp hb'
  have hfl := ev.fl16 (x := ardot fl [1, 1, 1] (hidv fl ex p w i) (p.W2 1 (0 + 9)) 0 0 +
    asw fl (0 : ℚ) (p.b2 1 (0 + 9))) (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨c1, c2⟩ := abs_le.mp hfl
  rw [abs_le]; constructor <;> linarith

/-! #### The final state and the read-out -/

noncomputable def zid (w : List ℕ) (i k : ℕ) : ℝ := yid w i k + (if k = 9 then Rsum w i else 0)

noncomputable def esz (k : ℕ) : ℝ :=
  if k < 9 then esy k + 1 / 100 + 1 / 10 ^ 6 else 1 / 80 + 13 / 125 + 1 / 10 ^ 6

noncomputable def Xsz (k : ℕ) : ℝ := if k < 6 then 1 else 2

theorem esz_le (k : ℕ) (hk : k < 10) : esz k ≤ 6 / 50 := by
  interval_cases k <;> norm_num [esz, esy]

theorem Xsz_le (k : ℕ) : Xsz k ≤ 2 := by
  unfold Xsz; split_ifs <;> norm_num

theorem sum10_Xsz : sum10 Xsz = 14 := by
  unfold sum10 Xsz; norm_num

theorem sum10_esz : sum10 esz ≤ 4691 / 10000 := by
  unfold sum10 esz esy; norm_num

theorem zid_nine (w : List ℕ) (i : ℕ) : zid w i 9 = Rsum w i := by
  unfold zid yid
  rw [id1_V w i 9 (by norm_num), Gv_ge9 w i 9 (by norm_num)]
  simp

theorem zid_abs (w : List ℕ) (i k : ℕ) (hk : k < 10) : |zid w i k| ≤ Xsz k := by
  by_cases hk9 : k = 9
  · subst hk9
    rw [zid_nine, abs_of_nonneg (Rsum_nonneg w i)]
    have := Rsum_le_two w i
    unfold Xsz
    norm_num
    exact this
  · have hz : zid w i k = yid w i k := by
      unfold zid; rw [if_neg hk9, add_zero]
    rw [hz]
    refine le_trans (yid_abs w i k) ?_
    unfold Xsy Xsz
    split_ifs <;> norm_num

theorem zz_len (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    (zz fl ex p w i).length = 10 := by
  unfold zz
  rw [radd_length fl (yy fl ex p w i) (mlp2 fl ex p w i)
    (by rw [yy_len ev i hi, mlp2_len fl ex p w i])]
  exact yy_len ev i hi

theorem zz_ent (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    ∀ k, k < 10 → |(zz fl ex p w i).getD k 0 - zid w i k| ≤ esz k := by
  intro k hk
  have hyl := yy_len ev i hi
  have hml := mlp2_len fl ex p w i
  unfold zz
  rw [radd_getD fl (yy fl ex p w i) (mlp2 fl ex p w i) k (by omega) (by omega)]
  have hy := yy_ent ev i hi k hk
  have hya := yid_abs w i k
  have hyn := yid_nonneg w i k
  have hxs := Xsy_le k
  have hes := esy_le k
  have hyb : |(yy fl ex p w i).getD k 0| ≤ 3 :=
    abs3 hy hyn (le_trans (le_abs_self _) (le_trans hya hxs)) (by linarith)
  by_cases hk9 : k = 9
  · subst hk9
    have hm := mlp9_ent ev i hi
    have hR := Rsum_nonneg w i
    have hR2 := Rsum_le_two w i
    have hy9 : yid w i 9 = 0 := by
      unfold yid
      rw [id1_V w i 9 (by norm_num), Gv_ge9 w i 9 (by norm_num), add_zero]
    have key := add1 ev (hh := yid w i 9) (f := Rsum w i) (ea := esy 9) (eb := 13 / 125) hy hm
      hyb (abs3 hm hR hR2 (by norm_num))
    rw [zid_nine]
    unfold esz
    rw [if_neg (by norm_num)]
    have e9 : esy 9 = 1 / 80 := by unfold esy; norm_num
    rw [e9, hy9, zero_add] at key
    exact key
  · have hm := mlp_small ev i hi k (by omega)
    have key := add1 ev (hh := yid w i k) (f := 0) (ea := esy k) (eb := 1 / 100) hy
      (by rw [sub_zero]; exact hm) hyb (le_trans hm (by norm_num))
    have hz : zid w i k = yid w i k := by
      unfold zid; rw [if_neg hk9, add_zero]
    rw [hz]
    unfold esz
    rw [if_pos (by omega)]
    rw [add_zero] at key
    exact key

theorem out_ideal (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    |net.out fl ex p w i - Rsum w i| ≤ 1 / 7 := by
  have hz := zz_ent ev i hi
  have hzl := zz_len ev i hi
  unfold ANet.out
  rw [run_eq]
  have key := dot_gen ev net.outW (fun k => if k = 9 then (1 : ℚ) else 0) rfl (W := 1)
    (by intro k hk; split_ifs <;> norm_num) (by norm_num) (zz fl ex p w i) hzl (zid w i) esz Xsz
    (fun k hk => ⟨hz k hk, zid_abs w i k hk⟩) (E := 6 / 50) (Xb := 2)
    (fun k hk => ⟨esz_le k hk, Xsz_le k⟩) (by norm_num) (by norm_num) (by norm_num) p.oW
    ev.hp.oW
  obtain ⟨k1, -⟩ := key
  rw [sum10_out, sum10_out_abs, sum10_Xsz, zid_nine] at k1
  have hs := sum10_esz
  have e9 : esz 9 = 1 / 80 + 13 / 125 + 1 / 10 ^ 6 := by unfold esz; rw [if_neg (by norm_num)]
  rw [e9] at k1
  have k1' : |ardot fl net.outW (zz fl ex p w i) p.oW 0 0 - Rsum w i| ≤ 1 / 7 - 1 / 100 := by
    refine le_trans k1 ?_
    norm_num
    linarith
  have hq : ((net.outB : ℚ) : ℝ) = 0 := by simp [net]
  have hb := asw_c ev net.outB ev.hp.oB (by rw [hq]; norm_num)
  rw [hq, sub_zero] at hb
  have hR := Rsum_nonneg w i
  have hR2 := Rsum_le_two w i
  obtain ⟨a1, a2⟩ := abs_le.mp k1'
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  have hfl := ev.fl16 (x := ardot fl net.outW (zz fl ex p w i) p.oW 0 0 + asw fl net.outB p.oB)
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨c1, c2⟩ := abs_le.mp hfl
  rw [abs_le]; constructor <;> linarith

/-! ### The target -/

def pf (w : List ℕ) (t n : ℕ) : Option ℕ :=
  (List.range n).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == t))

theorem pf_succ_pos (w : List ℕ) (t n : ℕ) (hP : 1 ≤ n ∧ tokAt w n = t) :
    pf w t (n + 1) = some n := by
  have hp : (decide (1 ≤ n) && (tokAt w n == t)) = true := by simp [hP.1, hP.2]
  unfold pf
  rw [List.range_succ, List.reverse_append]
  show (n :: (List.range n).reverse).find? (fun j => decide (1 ≤ j) && (tokAt w j == t)) =
    some n
  exact List.find?_cons_of_pos hp

theorem pf_succ_neg (w : List ℕ) (t n : ℕ) (hP : ¬(1 ≤ n ∧ tokAt w n = t)) :
    pf w t (n + 1) = pf w t n := by
  have hp : ¬((decide (1 ≤ n) && (tokAt w n == t)) = true) := by simpa using hP
  unfold pf
  rw [List.range_succ, List.reverse_append]
  show (n :: (List.range n).reverse).find? (fun j => decide (1 ≤ j) && (tokAt w j == t)) =
    (List.range n).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == t))
  exact List.find?_cons_of_neg hp

theorem pf_spec (w : List ℕ) (t n : ℕ) :
    (pf w t n = none ∧ ∀ j, j < n → ¬(1 ≤ j ∧ tokAt w j = t)) ∨
    ∃ j, pf w t n = some j ∧ j < n ∧ 1 ≤ j ∧ tokAt w j = t ∧
      ∀ j', j < j' → j' < n → ¬(1 ≤ j' ∧ tokAt w j' = t) := by
  induction n with
  | zero =>
    left
    refine ⟨rfl, ?_⟩
    intro j hj
    omega
  | succ n ih =>
    by_cases hP : 1 ≤ n ∧ tokAt w n = t
    · right
      refine ⟨n, pf_succ_pos w t n hP, by omega, hP.1, hP.2, ?_⟩
      intro j' h1 h2
      omega
    · rcases ih with ⟨h1, h2⟩ | ⟨j, h1, h2, h3, h4, h5⟩
      · left
        refine ⟨by rw [pf_succ_neg w t n hP]; exact h1, ?_⟩
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact h2 j hj
        · rw [hj]; exact hP
      · right
        refine ⟨j, by rw [pf_succ_neg w t n hP]; exact h1, by omega, h3, h4, ?_⟩
        intro j' hj1 hj2
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj2 with hj2 | hj2
        · exact h5 j' hj1 hj2
        · rw [hj2]; exact hP

theorem h_cast (s : ℕ) : ((Lane4.Case.h s : ℕ) : ℝ) = 2 * (ind s 2 + ind s 3) := by
  by_cases h1 : s = 1
  · subst h1; norm_num [Lane4.Case.h, ind]
  · by_cases h2 : s = 2
    · subst h2; norm_num [Lane4.Case.h, ind]
    · by_cases h3 : s = 3
      · subst h3; norm_num [Lane4.Case.h, ind]
      · simp [Lane4.Case.h, ind, h1, h2, h3]

theorem target_eq (w : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) (ht1 : 1 ≤ tokAt w i) :
    ((target w i : ℕ) : ℝ) = Fh w (tokAt w i - 1) i := by
  have hc : tokAt w i - 1 + 1 = tokAt w i := by omega
  rcases pf_spec w (tokAt w i) i with ⟨hnone, hno⟩ | ⟨j, hj, hji, hj1, hjt, hmax⟩
  · have hp : prevOcc w i = none := hnone
    have ht0 : target w i = 0 := by simp [target, hp]
    have hJ0 : Jc w (tokAt w i - 1) i = 0 := by
      apply Nat.findGreatest_eq_zero_iff.mpr
      intro m hm0 hmi hP
      have hP' : tokAt w (m - 1) = tokAt w i := by
        have : tokAt w (m - 1) = tokAt w i - 1 + 1 := hP
        omega
      have hm1 : 1 ≤ m - 1 := by
        by_contra hlt
        have h0 : m - 1 = 0 := by omega
        rw [h0, Lane4.Seq.tokAt_zero] at hP'
        omega
      exact hno (m - 1) (by omega) ⟨hm1, hP'⟩
    have hFh : Fh w (tokAt w i - 1) i = 0 := by
      unfold Fh Fv
      rw [hJ0, Lane4.Seq.tokAt_zero]
      norm_num [ind]
    rw [ht0, hFh]
    norm_num
  · have hp : prevOcc w i = some j := hj
    have htg : target w i = Lane4.Case.h (tokAt w (j + 1)) := by simp [target, hp]
    have hP1 : tokAt w (j + 1 - 1) = tokAt w i - 1 + 1 := by
      have : j + 1 - 1 = j := by omega
      rw [this, hjt]
      omega
    have hJ : Jc w (tokAt w i - 1) i = j + 1 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        have hJi : Jc w (tokAt w i - 1) i ≤ i := Nat.findGreatest_le i
        have hPJ : tokAt w (Jc w (tokAt w i - 1) i - 1) = tokAt w i - 1 + 1 :=
          Nat.findGreatest_spec (P := fun k => tokAt w (k - 1) = tokAt w i - 1 + 1) (m := j + 1)
            (by omega) hP1
        have hPJ' : tokAt w (Jc w (tokAt w i - 1) i - 1) = tokAt w i := by omega
        exact hmax (Jc w (tokAt w i - 1) i - 1) (by omega) (by omega) ⟨by omega, hPJ'⟩
      · exact Nat.le_findGreatest (P := fun k => tokAt w (k - 1) = tokAt w i - 1 + 1)
          (by omega) hP1
    rw [htg]
    unfold Fh Fv
    rw [hJ]
    exact h_cast _

theorem Rsum_eq (w : List ℕ) (i : ℕ) (ht : 1 ≤ tokAt w i ∧ tokAt w i ≤ 3) :
    Rsum w i = Fh w (tokAt w i - 1) i := by
  have h3 : tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 3 := by omega
  unfold Rsum
  rcases h3 with h | h | h <;> rw [h] <;> norm_num [ind]

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < w.length := by omega
  have hmem : tokAt w (k + 1) ∈ w := by
    rw [Lane4.Seq.tokAt_succ w k hk]
    exact List.getElem_mem hk
  have ht := ev.hw _ hmem
  have h1 := out_ideal ev (k + 1) hi
  rw [target_eq w (k + 1) hi1 ht.1, ← Rsum_eq w (k + 1) ht]
  exact le_trans h1 (by norm_num)

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
