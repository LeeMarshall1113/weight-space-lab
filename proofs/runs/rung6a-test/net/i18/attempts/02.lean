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
  content_zero ev head1.A rfl (net.init fl p w) (fun j => id0 w j) (fun j _ => init_close ev j)
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
    (by intro k hk; try dsimp only; split_ifs <;> norm_num) (by norm_num) (net.init fl p w j) hl
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

end Steps

end Lane4.Case
