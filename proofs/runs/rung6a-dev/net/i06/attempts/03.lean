namespace Lane4.Case
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! ## The network -/

def zrow (n : ℕ) : List ℚ := List.replicate n 0
def unitRow (n k : ℕ) (a : ℚ) : List ℚ := List.replicate k 0 ++ a :: List.replicate (n - 1 - k) 0
def zA : List (List ℚ) := List.replicate 10 (zrow 10)
def vr2 (c k : ℕ) : List ℚ := if k = 6 + c then unitRow 10 3 2 else zrow 10
def V2 (c : ℕ) : List (List ℚ) :=
  [vr2 c 0, vr2 c 1, vr2 c 2, vr2 c 3, vr2 c 4, vr2 c 5, vr2 c 6, vr2 c 7, vr2 c 8, vr2 c 9]
def V1 : List (List ℚ) :=
  [zrow 10, zrow 10, zrow 10, zrow 10, unitRow 10 0 1, unitRow 10 1 1, unitRow 10 2 1,
   zrow 10, zrow 10, zrow 10]
def hd1 : AHead := { A := zA, V := V1, mask := Mask.strict, m := 64, g := zrow 10, gb := -1 }
def hd2 (c : ℕ) : AHead :=
  { A := zA, V := V2 c, mask := Mask.causal, m := 64, g := unitRow 10 (3 + c) (-2), gb := 1 / 2 }
def w2r2 (k : ℕ) : List ℚ :=
  if k = 7 then unitRow 3 0 (-3) else if k = 8 then unitRow 3 1 (-3)
  else if k = 9 then unitRow 3 2 (-3) else zrow 3
def w2r3 (k : ℕ) : List ℚ := if k = 7 then [1, 1, 1] else zrow 3
def blk1 : ABlock :=
  { heads := [hd1], W1 := [], b1 := [], W2 := List.replicate 10 [], b2 := zrow 10 }
def blk2 : ABlock :=
  { heads := [hd2 1, hd2 2, hd2 3]
    W1 := [unitRow 10 0 (-8), unitRow 10 1 (-8), unitRow 10 2 (-8)]
    b1 := [2, 2, 2]
    W2 := [w2r2 0, w2r2 1, w2r2 2, w2r2 3, w2r2 4, w2r2 5, w2r2 6, w2r2 7, w2r2 8, w2r2 9]
    b2 := zrow 10 }
def blk3 : ABlock :=
  { heads := []
    W1 := [unitRow 10 7 (-1), unitRow 10 8 1, unitRow 10 9 1]
    b1 := [0, 0, 0]
    W2 := [w2r3 0, w2r3 1, w2r3 2, w2r3 3, w2r3 4, w2r3 5, w2r3 6, w2r3 7, w2r3 8, w2r3 9]
    b2 := zrow 10 }
def net : ANet :=
  { embed := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1 / 2, 0, 0, 1, 0, 0, 0, 0, 0, 0],
              [0, 1 / 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1 / 2, 2, 0, 0, 0, 0, 0, 0]]
    blocks := [blk1, blk2, blk3]
    outW := unitRow 10 7 (1 / 2)
    outB := 0 }

/-! ## Stages of the forward pass -/

noncomputable def att1 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  hd1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
    (net.init fl p w) i

noncomputable def mlp1 (fl : ℝ → ℝ) (p : APert) : Vec :=
  araffine fl (List.replicate 10 []) (zrow 10) [] (p.W2 0) (p.b2 0) 0

noncomputable def x1f (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  blk1.apply fl ex p 0 (w.length + 1) (net.init fl p w)

theorem x1f_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) :
    x1f fl ex p w j = radd fl (radd fl (net.init fl p w j) (att1 fl ex p w j)) (mlp1 fl p) := rfl

noncomputable def cs2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (c i : ℕ) : List ℕ :=
  (hd2 c).cands fl (p.g 1 (c - 1)) (p.gb 1 (c - 1)) (w.length + 1) (x1f fl ex p w) i

noncomputable def att2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (c i : ℕ) : Vec :=
  (hd2 c).attn fl ex (p.A 1 (c - 1)) (p.V 1 (c - 1)) (p.m 1 (c - 1)) (p.g 1 (c - 1))
    (p.gb 1 (c - 1)) (w.length + 1) (x1f fl ex p w) i

noncomputable def yf (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  radd fl (radd fl (radd fl (x1f fl ex p w i) (att2 fl ex p w 1 i)) (att2 fl ex p w 2 i))
    (att2 fl ex p w 3 i)

noncomputable def hid2 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  (araffine fl blk2.W1 blk2.b1 (yf fl ex p w i) (p.W1 1) (p.b1 1) 0).map Lane4.relu

noncomputable def y2f (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  blk2.apply fl ex p 1 (w.length + 1) (x1f fl ex p w)

theorem y2f_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    y2f fl ex p w i = radd fl (yf fl ex p w i)
      (araffine fl blk2.W2 blk2.b2 (hid2 fl ex p w i) (p.W2 1) (p.b2 1) 0) := rfl

noncomputable def hid3 (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  (araffine fl blk3.W1 blk3.b1 (y2f fl ex p w i) (p.W1 2) (p.b1 2) 0).map Lane4.relu

noncomputable def y3f (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : ℕ → Vec :=
  blk3.apply fl ex p 2 (w.length + 1) (y2f fl ex p w)

theorem y3f_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    y3f fl ex p w i = radd fl (y2f fl ex p w i)
      (araffine fl blk3.W2 blk3.b2 (hid3 fl ex p w i) (p.W2 2) (p.b2 2) 0) := rfl

theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    net.run fl ex p w i = y3f fl ex p w i := rfl

/-! ## List lemmas -/

theorem rep_getD {α : Type} (a d : α) : ∀ (n k : ℕ), k < n → (List.replicate n a).getD k d = a
  | 0, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, 0, _ => by simp [List.replicate_succ]
  | n + 1, k + 1, hk => by
      rw [List.replicate_succ, List.getD_cons_succ]
      exact rep_getD a d n k (by omega)

theorem zrow_getD (n k : ℕ) (hk : k < n) : (zrow n).getD k 0 = 0 := rep_getD 0 0 n k hk

theorem zrow_len (n : ℕ) : (zrow n).length = n := by simp [zrow]

theorem unitRow_len (n k : ℕ) (hk : k < n) (a : ℚ) : (unitRow n k a).length = n := by
  simp only [unitRow, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem radd_len (fl : ℝ → ℝ) : ∀ (a b : List ℝ), (radd fl a b).length = min a.length b.length
  | [], b => by simp [Lane4.RSeq.radd]
  | a :: x, [] => by simp [Lane4.RSeq.radd]
  | a :: x, b :: y => by
      simp only [Lane4.RSeq.radd, List.length_cons]
      rw [radd_len fl x y]
      omega

theorem radd_len10 (fl : ℝ → ℝ) {a b : List ℝ} (ha : a.length = 10) (hb : b.length = 10) :
    (radd fl a b).length = 10 := by
  rw [radd_len, ha, hb]; simp

theorem radd_getD (fl : ℝ → ℝ) : ∀ (a b : List ℝ) (k : ℕ), k < a.length → k < b.length →
    (radd fl a b).getD k 0 = fl (a.getD k 0 + b.getD k 0)
  | [], b, k, h1, _ => by simp at h1
  | a :: x, [], k, _, h2 => by simp at h2
  | a :: x, b :: y, 0, _, _ => by simp [Lane4.RSeq.radd]
  | a :: x, b :: y, k + 1, h1, h2 => by
      simp only [Lane4.RSeq.radd, List.getD_cons_succ]
      exact radd_getD fl x y k (by simpa using h1) (by simpa using h2)

theorem araffine_len (fl : ℝ → ℝ) : ∀ (M : List (List ℚ)) (b : List ℚ) (x : Vec)
    (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (i : ℕ),
    (araffine fl M b x dW db i).length = min M.length b.length
  | [], b, x, dW, db, i => by simp [araffine]
  | r :: M, [], x, dW, db, i => by simp [araffine]
  | r :: M, c :: b, x, dW, db, i => by
      simp only [araffine, List.length_cons]
      rw [araffine_len fl M b x dW db (i + 1)]
      omega

theorem araffine_getD (fl : ℝ → ℝ) : ∀ (M : List (List ℚ)) (b : List ℚ) (x : Vec)
    (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ) (i k : ℕ), k < M.length → k < b.length →
    (araffine fl M b x dW db i).getD k 0 =
      fl (ardot fl (M.getD k []) x (dW (i + k)) 0 0 + asw fl (b.getD k 0) (db (i + k)))
  | [], b, x, dW, db, i, k, hk, _ => by simp at hk
  | r :: M, [], x, dW, db, i, k, _, hk => by simp at hk
  | r :: M, c :: b, x, dW, db, i, 0, _, _ => by simp [araffine]
  | r :: M, c :: b, x, dW, db, i, k + 1, hk1, hk2 => by
      have ih := araffine_getD fl M b x dW db (i + 1) k (by simpa using hk1) (by simpa using hk2)
      simp only [araffine, List.getD_cons_succ]
      rw [ih]
      have e : i + 1 + k = i + (k + 1) := by omega
      rw [e]

theorem aswRow_len (fl : ℝ → ℝ) : ∀ (r : List ℚ) (d : ℕ → ℝ) (j : ℕ),
    (aswRow fl r d j).length = r.length
  | [], d, j => by simp [aswRow]
  | a :: r, d, j => by simp [aswRow, aswRow_len fl r d (j + 1)]

theorem aswRow_getD (fl : ℝ → ℝ) : ∀ (r : List ℚ) (d : ℕ → ℝ) (j k : ℕ), k < r.length →
    (aswRow fl r d j).getD k 0 = asw fl (r.getD k 0) (d (j + k))
  | [], d, j, k, hk => by simp at hk
  | a :: r, d, j, 0, _ => by simp [aswRow]
  | a :: r, d, j, k + 1, hk => by
      have ih := aswRow_getD fl r d (j + 1) k (by simpa using hk)
      simp only [aswRow, List.getD_cons_succ]
      rw [ih]
      have e : j + 1 + k = j + (k + 1) := by omega
      rw [e]

theorem aattnRows_len (fl ex : ℝ → ℝ) : ∀ (M : List (List ℚ)) (dV : ℕ → ℕ → ℝ) (c : List ℕ)
    (s : ℕ → ℝ) (x : ℕ → Vec) (i : ℕ), (aattnRows fl ex M dV c s x i).length = M.length
  | [], dV, c, s, x, i => by simp [aattnRows]
  | r :: M, dV, c, s, x, i => by simp [aattnRows, aattnRows_len fl ex M dV c s x (i + 1)]

theorem aattnRows_getD (fl ex : ℝ → ℝ) : ∀ (M : List (List ℚ)) (dV : ℕ → ℕ → ℝ) (c : List ℕ)
    (s : ℕ → ℝ) (x : ℕ → Vec) (i k : ℕ), k < M.length →
    (aattnRows fl ex M dV c s x i).getD k 0 =
      savg fl ex c s (fun j => ardot fl (M.getD k []) (x j) (dV (i + k)) 0 0)
  | [], dV, c, s, x, i, k, hk => by simp at hk
  | r :: M, dV, c, s, x, i, 0, _ => by simp [aattnRows]
  | r :: M, dV, c, s, x, i, k + 1, hk => by
      have ih := aattnRows_getD fl ex M dV c s x (i + 1) k (by simpa using hk)
      simp only [aattnRows, List.getD_cons_succ]
      rw [ih]
      have e : i + 1 + k = i + (k + 1) := by omega
      rw [e]

theorem map_relu_getD : ∀ (l : List ℝ) (k : ℕ),
    (l.map Lane4.relu).getD k 0 = Lane4.relu (l.getD k 0)
  | [], k => by simp [Lane4.relu]
  | a :: l, 0 => by simp
  | a :: l, k + 1 => by
      simp only [List.map_cons, List.getD_cons_succ]
      exact map_relu_getD l k

theorem attn_getD (fl ex : ℝ → ℝ) (H : AHead) (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ)
    (dgb : ℝ) (n : ℕ) (x : ℕ → Vec) (i k : ℕ) (hk : k < H.V.length) :
    (H.attn fl ex dA dV dm dg dgb n x i).getD k 0 =
      savg fl ex (H.cands fl dg dgb n x i) (fun j => H.score fl dA dm x i j)
        (fun j => ardot fl (H.V.getD k []) (x j) (dV k) 0 0) := by
  unfold AHead.attn
  rw [aattnRows_getD fl ex H.V dV _ _ x 0 k hk]
  simp only [Nat.zero_add]

theorem list3_eq (l : List ℝ) (h3 : l.length = 3) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp only [List.length_nil] at h3; omega
  · simp only [List.length_cons, List.length_nil] at h3; omega
  · simp only [List.length_cons, List.length_nil] at h3; omega
  · rfl
  · simp only [List.length_cons] at h3; omega

/-! ## dotQ lemmas -/

theorem dotQ_cons (a : ℚ) (r : List ℚ) (v : ℝ) (x : List ℝ) :
    dotQ (a :: r) (v :: x) = (a : ℝ) * v + dotQ r x := by
  simp [dotQ]

theorem dotQ_zrow : ∀ (n : ℕ) (x : List ℝ), dotQ (zrow n) x = 0
  | 0, x => by simp [zrow, dotQ]
  | n + 1, [] => by simp [zrow, dotQ]
  | n + 1, v :: x => by
      have ih := dotQ_zrow n x
      have e : zrow (n + 1) = (0 : ℚ) :: zrow n := rfl
      rw [e, dotQ_cons, ih]
      simp

theorem dotQ_unit_aux : ∀ (k m : ℕ) (a : ℚ) (x : List ℝ), x.length = k + 1 + m →
    dotQ (List.replicate k 0 ++ a :: List.replicate m 0) x = (a : ℝ) * x.getD k 0
  | 0, m, a, x, hx => by
      cases x with
      | nil => simp only [List.length_nil] at hx; omega
      | cons v x' =>
        have e : List.replicate 0 (0 : ℚ) ++ a :: List.replicate m 0 = a :: zrow m := rfl
        rw [e, dotQ_cons, dotQ_zrow]
        simp
  | k + 1, m, a, x, hx => by
      cases x with
      | nil => simp only [List.length_nil] at hx; omega
      | cons v x' =>
        have hl : x'.length = k + 1 + m := by simp only [List.length_cons] at hx; omega
        have e : List.replicate (k + 1) (0 : ℚ) ++ a :: List.replicate m 0
            = 0 :: (List.replicate k 0 ++ a :: List.replicate m 0) := rfl
        rw [e, dotQ_cons, dotQ_unit_aux k m a x' hl]
        simp

theorem dotQ_unitRow (n k : ℕ) (hk : k < n) (a : ℚ) (x : List ℝ) (hx : x.length = n) :
    dotQ (unitRow n k a) x = (a : ℝ) * x.getD k 0 := by
  unfold unitRow
  apply dotQ_unit_aux
  omega

theorem mem_zrow {n : ℕ} {a : ℚ} (h : a ∈ zrow n) : a = 0 := by
  unfold zrow at h
  exact (List.mem_replicate.mp h).2

theorem mem_unitRow {n k : ℕ} {a b : ℚ} (h : b ∈ unitRow n k a) : b = 0 ∨ b = a := by
  unfold unitRow at h
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at h
  rcases h with h | h | h
  · exact Or.inl h.2
  · exact Or.inr h
  · exact Or.inl h.2

/-! ## Row types -/

def RT (n K : ℕ) (W : ℝ) (r : List ℚ) : Prop :=
  r = zrow n ∨ ∃ k, k < K ∧ k < n ∧ ∃ a : ℚ, r = unitRow n k a ∧ |(a : ℝ)| ≤ W

theorem RT_len {n K : ℕ} {W : ℝ} {r : List ℚ} (hr : RT n K W r) : r.length = n := by
  rcases hr with rfl | ⟨k, hkK, hkn, a, rfl, _⟩
  · exact zrow_len n
  · exact unitRow_len n k hkn a

theorem RT_ok {n K : ℕ} {W : ℝ} {r : List ℚ} (hr : RT n K W r) (hW : 0 ≤ W) :
    ∀ a ∈ r, |(a : ℝ)| ≤ W := by
  rcases hr with rfl | ⟨k, hkK, hkn, a, rfl, ha⟩
  · intro b hb
    rw [mem_zrow hb]; simpa using hW
  · intro b hb
    rcases mem_unitRow hb with h0 | h0
    · rw [h0]; simpa using hW
    · rw [h0]; exact ha

theorem RT_near {n K : ℕ} {W e : ℝ} {r : List ℚ} (hr : RT n K W r) (hW : 0 ≤ W) (he : 0 ≤ e)
    {x xh : List ℝ} (hx : x.length = n) (hxh : xh.length = n)
    (hcl : ∀ k, k < K → |x.getD k 0 - xh.getD k 0| ≤ e) : |dotQ r x - dotQ r xh| ≤ W * e := by
  rcases hr with rfl | ⟨k, hkK, hkn, a, rfl, ha⟩
  · rw [dotQ_zrow, dotQ_zrow]; simpa using mul_nonneg hW he
  · rw [dotQ_unitRow n k hkn a x hx, dotQ_unitRow n k hkn a xh hxh, ← mul_sub, abs_mul]
    exact mul_le_mul ha (hcl k hkK) (abs_nonneg _) hW

theorem RT_mag {n K : ℕ} {W Y : ℝ} {r : List ℚ} (hr : RT n K W r) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    {xh : List ℝ} (hxh : xh.length = n) (hb : ∀ k, k < K → |xh.getD k 0| ≤ Y) :
    |dotQ r xh| ≤ W * Y := by
  rcases hr with rfl | ⟨k, hkK, hkn, a, rfl, ha⟩
  · rw [dotQ_zrow]; simpa using mul_nonneg hW hY
  · rw [dotQ_unitRow n k hkn a xh hxh, abs_mul]
    exact mul_le_mul ha (hb k hkK) (abs_nonneg _) hW

/-! ## The noise lemma -/

theorem wErr_rep (δ e : ℝ) : ∀ (r : List ℚ) (Xs : List ℝ), r.length = Xs.length →
    wErr δ r (List.replicate r.length e) Xs = absSum r * e + δ * (Xs.sum + (r.length : ℝ) * e)
  | [], Xs, hl => by
      cases Xs with
      | nil => simp [wErr, absSum]
      | cons X Xs' => simp at hl
  | a :: r, Xs, hl => by
      cases Xs with
      | nil => simp at hl
      | cons X Xs' =>
        have hl' : r.length = Xs'.length := by simpa using hl
        have ih := wErr_rep δ e r Xs' hl'
        have hab : absSum (a :: r) = |(a : ℝ)| + absSum r := by simp [absSum]
        simp only [List.length_cons, List.replicate_succ, wErr]
        rw [ih, hab, List.sum_cons]
        push_cast
        ring

theorem dotA_gen {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M)
    (L : ℕ) (hL : L ≤ 32) (r : List ℚ) (x Xs : List ℝ) (d : ℕ → ℝ) (W Xm S : ℝ)
    (hrl : r.length = L) (hxl : x.length = L) (hXl : Xs.length = L)
    (hd : ∀ k, |d k| ≤ 1 / 1000) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (hXm0 : 0 ≤ Xm)
    (hb : ∀ k, k < L → |x.getD k 0| ≤ Xs.getD k 0 ∧ Xs.getD k 0 ≤ Xm)
    (hS : Xs.sum ≤ S) (hT : (W + 1) * (Xm + 0 + 1) ≤ 2 ^ 20) :
    |ardot fl r x d 0 0 - dotQ r x| ≤ 1 / 1000 * S + (L : ℝ) * (W + 1) * (Xm + 1) / 2 ^ 16 + 1 / 2 ^ 100 := by
  have hCL : CloseL x x (List.replicate L 0) Xs := by
    refine ⟨rfl, by simp [hxl], by rw [hXl, hxl], ?_⟩
    intro k hk
    have hk' : k < L := by rwa [hxl] at hk
    have e1 : (List.replicate L (0 : ℝ)).getD k 0 = 0 := rep_getD (0 : ℝ) 0 L k hk'
    rw [e1]
    exact ⟨by simp, (hb k hk').1⟩
  have hb2 : ∀ k, k < x.length → (List.replicate L (0 : ℝ)).getD k 0 ≤ 0 ∧ Xs.getD k 0 ≤ Xm := by
    intro k hk
    have hk' : k < L := by rwa [hxl] at hk
    rw [rep_getD (0 : ℝ) 0 L k hk']
    exact ⟨le_refl _, (hb k hk').2⟩
  have key := ardot_near_w u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x x (List.replicate L 0) Xs d W Xm 0 (by rw [hrl, hxl]) (by omega) hCL hb2 hd hW hW0 hXm0
    (le_refl _) hT hM
  obtain ⟨k1, -⟩ := key
  have hw := wErr_rep (1 / 1000) 0 r Xs (by rw [hrl, hXl])
  rw [hrl] at hw k1
  rw [hw] at k1
  have hS' : 1 / 1000 * Xs.sum ≤ 1 / 1000 * S := by linarith
  have e2 : (L : ℝ) * (W + 1) * (Xm + 0 + 1) = (L : ℝ) * (W + 1) * (Xm + 1) := by ring
  rw [e2] at k1
  linarith

/-! ## Context -/

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

theorem Ctx.flnear (ev : Ctx u η M fl ex p w) {x t e : ℝ} (hx : |x - t| ≤ e) (hB : |x| ≤ 100) :
    |fl x - t| ≤ e + 1 / 100000 := by
  have h1 := ev.hr.near ev.hu0 hx hB (ev.range 100 (by norm_num))
  have h2 : u * 100 ≤ 1 / 2 ^ 24 * 100 := mul_le_mul_of_nonneg_right ev.hu1 (by norm_num)
  have h3 := eta_tiny ev.hη1
  have h4 : (1 : ℝ) / 2 ^ 24 * 100 + 1 / 10 ^ 40 ≤ 1 / 100000 := by norm_num
  linarith

theorem Ctx.flabs (ev : Ctx u η M fl ex p w) {x : ℝ} (hB : |x| ≤ 100) :
    |fl x - x| ≤ 1 / 100000 := by
  have := ev.flnear (t := x) (e := 0) (by simp) hB
  linarith

theorem Ctx.aswb (ev : Ctx u η M fl ex p w) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000)
    (ha : |(a : ℝ)| ≤ 8) : |asw fl a d - (a : ℝ)| ≤ 1001 / 1000000 := by
  have hM : |(a : ℝ)| + 1 / 1000 ≤ M := by
    have := ev.range 9 (by norm_num); linarith
  have h := asw_near ev.hr ev.hu0 a hd hM
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 9 :=
    mul_le_mul ev.hu1 (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny ev.hη1
  have h3 : (1 : ℝ) / 2 ^ 24 * 9 + 1 / 10 ^ 40 ≤ 1 / 1000000 := by norm_num
  linarith

theorem Ctx.aswz (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl (0 : ℚ) d| ≤ 1001 / 1000000 := by
  have := ev.aswb 0 hd (by simp)
  simpa using this

theorem Ctx.mz (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl (0 : ℚ) d)| ≤ 11 / 10000 := by
  have h0 := ev.aswz hd
  have h1 := ev.flabs (x := 0 + asw fl (0 : ℚ) d) (by rw [zero_add]; linarith)
  have h2 := abs_sub_abs_le_abs_sub (fl (0 + asw fl (0 : ℚ) d)) (0 + asw fl (0 : ℚ) d)
  rw [zero_add] at h1 h2 ⊢
  linarith

theorem Ctx.dotA (ev : Ctx u η M fl ex p w) (L : ℕ) (hL : L ≤ 32) (r : List ℚ) (x Xs : List ℝ)
    (d : ℕ → ℝ) (W Xm S : ℝ) (hrl : r.length = L) (hxl : x.length = L) (hXl : Xs.length = L)
    (hd : ∀ k, |d k| ≤ 1 / 1000) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (hXm0 : 0 ≤ Xm)
    (hb : ∀ k, k < L → |x.getD k 0| ≤ Xs.getD k 0 ∧ Xs.getD k 0 ≤ Xm)
    (hS : Xs.sum ≤ S) (hT : (W + 1) * (Xm + 0 + 1) ≤ 2 ^ 20) :
    |ardot fl r x d 0 0 - dotQ r x| ≤ 1 / 1000 * S + (L : ℝ) * (W + 1) * (Xm + 1) / 2 ^ 16 + 1 / 2 ^ 100 :=
  dotA_gen ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (ev.range (2 ^ 30) (by norm_num)) L hL r x Xs d W Xm S
    hrl hxl hXl hd hW hW0 hXm0 hb hS hT

theorem abs_close_le {x y e X : ℝ} (hx : |x - y| ≤ e) (hy : |y| ≤ X) : |x| ≤ X + e := by
  have := abs_sub_abs_le_abs_sub x y
  linarith

theorem relu_lip (a b : ℝ) : |Lane4.relu a - Lane4.relu b| ≤ |a - b| := by
  unfold Lane4.relu
  rw [abs_le]
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  have h3 := abs_nonneg (a - b)
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_right ha, max_eq_left hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_right hb]; constructor <;> linarith
  · rw [max_eq_left ha, max_eq_left hb]; constructor <;> linarith

theorem Ctx.fl_step (ev : Ctx u η M fl ex p w) {a b t s ea eb : ℝ} (ha : |a - t| ≤ ea)
    (hb : |b - s| ≤ eb) (hts : |t + s| + ea + eb ≤ 100) :
    |fl (a + b) - (t + s)| ≤ ea + eb + 1 / 100000 := by
  have h1 : |a + b - (t + s)| ≤ ea + eb := by
    have := abs_add_le (a - t) (b - s)
    have e : a - t + (b - s) = a + b - (t + s) := by ring
    rw [e] at this; linarith
  have h2 : |a + b| ≤ 100 := by
    have := abs_close_le h1 (le_refl |t + s|)
    linarith
  exact ev.flnear h1 h2

theorem Ctx.add3 (ev : Ctx u η M fl ex p w) {x a1 a2 a3 t b1 b2 b3 e0 e1 e2 e3 : ℝ}
    (hx : |x - t| ≤ e0) (h1 : |a1 - b1| ≤ e1) (h2 : |a2 - b2| ≤ e2) (h3 : |a3 - b3| ≤ e3)
    (hB : |t| + |b1| + |b2| + |b3| + e0 + e1 + e2 + e3 ≤ 90) :
    |fl (fl (fl (x + a1) + a2) + a3) - (t + b1 + b2 + b3)| ≤ e0 + e1 + e2 + e3 + 3 / 100000 := by
  have n0 : 0 ≤ e0 := le_trans (abs_nonneg _) hx
  have n1 : 0 ≤ e1 := le_trans (abs_nonneg _) h1
  have n2 : 0 ≤ e2 := le_trans (abs_nonneg _) h2
  have n3 : 0 ≤ e3 := le_trans (abs_nonneg _) h3
  have t1 := abs_add_le t b1
  have t2 := abs_add_le (t + b1) b2
  have t3 := abs_add_le (t + b1 + b2) b3
  have q0 := abs_nonneg t
  have q1 := abs_nonneg b1
  have q2 := abs_nonneg b2
  have q3 := abs_nonneg b3
  have s1 := ev.fl_step hx h1 (by linarith)
  have s2 := ev.fl_step s1 h2 (by linarith)
  have s3 := ev.fl_step s2 h3 (by linarith)
  linarith

/-! ## Ideal vectors and bound lists -/

noncomputable def xh0t (t : ℕ) : List ℝ :=
  [(1 / 2) * (if t = 1 then 1 else 0), (1 / 2) * (if t = 2 then 1 else 0),
   (1 / 2) * (if t = 3 then 1 else 0), (h t : ℝ), 0, 0, 0, 0, 0, 0]

noncomputable def xh1t (a b : ℕ) : List ℝ :=
  [(1 / 2) * (if a = 1 then 1 else 0), (1 / 2) * (if a = 2 then 1 else 0),
   (1 / 2) * (if a = 3 then 1 else 0), (h a : ℝ),
   (1 / 2) * (if b = 1 then 1 else 0), (1 / 2) * (if b = 2 then 1 else 0),
   (1 / 2) * (if b = 3 then 1 else 0), 0, 0, 0]

noncomputable def Xi0 : List ℝ := [1 / 2, 1 / 2, 1 / 2, 2, 0, 0, 0, 0, 0, 0]
noncomputable def Xi1 : List ℝ := [1 / 2, 1 / 2, 1 / 2, 2, 1 / 2, 1 / 2, 1 / 2, 0, 0, 0]
noncomputable def Xa0 : List ℝ :=
  [51 / 100, 51 / 100, 51 / 100, 201 / 100, 1 / 100, 1 / 100, 1 / 100, 1 / 100, 1 / 100, 1 / 100]
noncomputable def Xa1 : List ℝ :=
  [52 / 100, 52 / 100, 52 / 100, 202 / 100, 52 / 100, 52 / 100, 52 / 100, 2 / 100, 2 / 100, 2 / 100]
noncomputable def Xay : List ℝ :=
  [55 / 100, 55 / 100, 55 / 100, 205 / 100, 55 / 100, 55 / 100, 55 / 100, 42 / 10, 42 / 10, 42 / 10]
noncomputable def Xayp : List ℝ :=
  [56 / 100, 56 / 100, 56 / 100, 206 / 100, 56 / 100, 56 / 100, 56 / 100, 113 / 10, 113 / 10, 113 / 10]
noncomputable def Xaypp : List ℝ :=
  [60 / 100, 60 / 100, 60 / 100, 210 / 100, 60 / 100, 60 / 100, 60 / 100, 1135 / 100, 1135 / 100, 1135 / 100]
noncomputable def Xu : List ℝ := [236 / 100, 236 / 100, 236 / 100]
noncomputable def Xh : List ℝ := [1135 / 100, 430 / 100, 430 / 100]

theorem xh0t_len (t : ℕ) : (xh0t t).length = 10 := by simp [xh0t]
theorem xh1t_len (a b : ℕ) : (xh1t a b).length = 10 := by simp [xh1t]
theorem Xa0_len : Xa0.length = 10 := by simp [Xa0]
theorem Xa1_len : Xa1.length = 10 := by simp [Xa1]
theorem Xay_len : Xay.length = 10 := by simp [Xay]
theorem Xayp_len : Xayp.length = 10 := by simp [Xayp]
theorem Xaypp_len : Xaypp.length = 10 := by simp [Xaypp]
theorem Xu_len : Xu.length = 3 := by simp [Xu]
theorem Xh_len : Xh.length = 3 := by simp [Xh]

theorem Xa0_sum : Xa0.sum ≤ 6 := by norm_num [Xa0]
theorem Xa1_sum : Xa1.sum ≤ 6 := by norm_num [Xa1]
theorem Xay_sum : Xay.sum ≤ 18 := by norm_num [Xay]
theorem Xayp_sum : Xayp.sum ≤ 40 := by norm_num [Xayp]
theorem Xaypp_sum : Xaypp.sum ≤ 41 := by norm_num [Xaypp]
theorem Xu_sum : Xu.sum ≤ 71 / 10 := by norm_num [Xu]
theorem Xh_sum : Xh.sum ≤ 2025 / 100 := by norm_num [Xh]

theorem Xa0_get (k : ℕ) (hk : k < 10) : 0 ≤ Xa0.getD k 0 ∧ Xa0.getD k 0 ≤ 21 / 10 := by
  interval_cases k <;> norm_num [Xa0]
theorem Xa1_get (k : ℕ) (hk : k < 10) : 0 ≤ Xa1.getD k 0 ∧ Xa1.getD k 0 ≤ 21 / 10 := by
  interval_cases k <;> norm_num [Xa1]
theorem Xay_get (k : ℕ) (hk : k < 10) : 0 ≤ Xay.getD k 0 ∧ Xay.getD k 0 ≤ 42 / 10 := by
  interval_cases k <;> norm_num [Xay]
theorem Xayp_get (k : ℕ) (hk : k < 10) : 0 ≤ Xayp.getD k 0 ∧ Xayp.getD k 0 ≤ 113 / 10 := by
  interval_cases k <;> norm_num [Xayp]
theorem Xaypp_get (k : ℕ) (hk : k < 10) : 0 ≤ Xaypp.getD k 0 ∧ Xaypp.getD k 0 ≤ 1135 / 100 := by
  interval_cases k <;> norm_num [Xaypp]
theorem Xu_get (k : ℕ) (hk : k < 3) : 0 ≤ Xu.getD k 0 ∧ Xu.getD k 0 ≤ 236 / 100 := by
  interval_cases k <;> norm_num [Xu]
theorem Xh_get (k : ℕ) (hk : k < 3) : 0 ≤ Xh.getD k 0 ∧ Xh.getD k 0 ≤ 1135 / 100 := by
  interval_cases k <;> norm_num [Xh]

theorem h_le2 (t : ℕ) : (h t : ℝ) ≤ 2 := by
  unfold h; split_ifs <;> norm_num
theorem h_nn (t : ℕ) : (0 : ℝ) ≤ (h t : ℝ) := Nat.cast_nonneg _
theorem h_le2n (t : ℕ) : h t ≤ 2 := by
  unfold h; split_ifs <;> omega

theorem xh0t_abs (t k : ℕ) (hk : k < 10) : |(xh0t t).getD k 0| ≤ Xi0.getD k 0 := by
  have h1 := h_le2 t
  have h2 := h_nn t
  interval_cases k <;> simp [xh0t, Xi0] <;> first | exact h_le2n t | exact h1 | (split_ifs <;> norm_num)

theorem xh1t_abs (a b k : ℕ) (hk : k < 10) : |(xh1t a b).getD k 0| ≤ Xi1.getD k 0 := by
  have h1 := h_le2 a
  have h2 := h_nn a
  interval_cases k <;> simp [xh1t, Xi1] <;> first | exact h_le2n a | exact h1 | (split_ifs <;> norm_num)

theorem Xa0_ge (k : ℕ) (hk : k < 10) : Xi0.getD k 0 + 11 / 10000 ≤ Xa0.getD k 0 := by
  interval_cases k <;> norm_num [Xi0, Xa0]
theorem Xa1_ge (k : ℕ) (hk : k < 10) : Xi1.getD k 0 + 17 / 1000 ≤ Xa1.getD k 0 := by
  interval_cases k <;> norm_num [Xi1, Xa1]
theorem Xay_ge (k : ℕ) (hk : k < 7) : Xi1.getD k 0 + 41 / 1000 ≤ Xay.getD k 0 := by
  interval_cases k <;> norm_num [Xi1, Xay]
theorem Xayp_ge (k : ℕ) (hk : k < 7) : Xi1.getD k 0 + 51 / 1000 ≤ Xayp.getD k 0 := by
  interval_cases k <;> norm_num [Xi1, Xayp]
theorem Xaypp_ge (k : ℕ) (hk : k < 10) :
    Xayp.getD k 0 + 23 / 1000 + 1 / 100000 ≤ Xaypp.getD k 0 := by
  interval_cases k <;> norm_num [Xayp, Xaypp]
theorem Xayp_ge2 (k : ℕ) (hk : k < 7) :
    Xay.getD k 0 + 9 / 1000 + 1 / 100000 ≤ Xayp.getD k 0 := by
  interval_cases k <;> norm_num [Xay, Xayp]

/-! ## Tokens and the initial state -/

theorem tok_le3 (ev : Ctx u η M fl ex p w) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h0 | hm
  · omega
  · exact (ev.hw _ hm).2

theorem tok_pos (ev : Ctx u η M fl ex p w) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ w.length) :
    1 ≤ tokAt w i ∧ tokAt w i ≤ 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Lane4.Seq.tokAt_succ w k (by omega)]
  exact ev.hw _ (List.getElem_mem (by omega))

theorem embed_len (t : ℕ) (ht : t ≤ 3) : (net.embed.getD t []).length = 10 := by
  interval_cases t <;> rfl

theorem embed_ideal (t : ℕ) (ht : t ≤ 3) (k : ℕ) (hk : k < 10) :
    ((((net.embed.getD t []).getD k 0 : ℚ)) : ℝ) = (xh0t t).getD k 0 := by
  interval_cases t <;> interval_cases k <;> norm_num [net, xh0t, h]

theorem emb_le (t : ℕ) (ht : t ≤ 3) (k : ℕ) (hk : k < 10) :
    |((((net.embed.getD t []).getD k 0 : ℚ)) : ℝ)| ≤ 2 := by
  interval_cases t <;> interval_cases k <;> norm_num [net]

theorem init_len (ev : Ctx u η M fl ex p w) (j : ℕ) : (net.init fl p w j).length = 10 := by
  have ht := tok_le3 ev j
  show (aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0).length = 10
  rw [aswRow_len, embed_len _ ht]

theorem init_close (ev : Ctx u η M fl ex p w) (j k : ℕ) (hk : k < 10) :
    |(net.init fl p w j).getD k 0 - (xh0t (tokAt w j)).getD k 0| ≤ 11 / 10000 := by
  have ht := tok_le3 ev j
  have hl := embed_len _ ht
  have e1 : (net.init fl p w j).getD k 0 =
      asw fl ((net.embed.getD (tokAt w j) []).getD k 0) (p.E (tokAt w j) (0 + k)) := by
    show (aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0).getD k 0 = _
    exact aswRow_getD fl _ _ 0 k (by omega)
  rw [e1, ← embed_ideal _ ht k hk]
  have := ev.aswb ((net.embed.getD (tokAt w j) []).getD k 0) (ev.hp.E (tokAt w j) (0 + k))
    (by have := emb_le _ ht k hk; linarith)
  linarith

theorem init_abs (ev : Ctx u η M fl ex p w) (j k : ℕ) (hk : k < 10) :
    |(net.init fl p w j).getD k 0| ≤ Xa0.getD k 0 := by
  have h1 := init_close ev j k hk
  have h2 := xh0t_abs (tokAt w j) k hk
  have h3 := Xa0_ge k hk
  have := abs_close_le h1 h2
  linarith

theorem init_state (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 10 ∧ ∀ k, k < 10 → |(net.init fl p w j).getD k 0| ≤ Xa0.getD k 0 :=
  ⟨init_len ev j, fun k hk => init_abs ev j k hk⟩

/-! ## Zero-weight noise -/

theorem Ctx.zdot (ev : Ctx u η M fl ex p w) {K : ℕ} {W : ℝ} {r : List ℚ} (hr : RT 10 K W r)
    (hW0 : 0 ≤ W) (hW2 : W ≤ 2) (x Xa : List ℝ) (hXl : Xa.length = 10)
    (hXb : ∀ k, k < 10 → 0 ≤ Xa.getD k 0 ∧ Xa.getD k 0 ≤ 21 / 10) (hXs : Xa.sum ≤ 6)
    (hx : x.length = 10) (hxb : ∀ k, k < 10 → |x.getD k 0| ≤ Xa.getD k 0)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r x| ≤ 75 / 10000 := by
  have h := ev.dotA 10 (by norm_num) r x Xa d 2 (21 / 10) 6 (RT_len hr) hx hXl hd
    (fun a ha => le_trans (RT_ok hr hW0 a ha) hW2) (by norm_num) (by norm_num)
    (fun k hk => ⟨hxb k hk, (hXb k hk).2⟩) hXs (by norm_num)
  exact le_trans h (by norm_num)

/-! ## The generic softmax head -/

theorem bias_abs' (ev : Ctx u η M fl ex p w) (H : AHead) (hm : H.m = 64) (dm : ℝ)
    (hdm : |dm| ≤ 1 / 1000) (i t : ℕ) (hi : i ≤ w.length + 1) (ht : t ≤ w.length + 1) :
    |H.bias fl dm i t| ≤ 66 * ((w.length + 1 : ℕ) : ℝ) := by
  have hmR : ((H.m : ℚ) : ℝ) = 64 := by rw [hm]; norm_num
  have habs : |((H.m : ℚ) : ℝ)| = 64 := by rw [hmR]; exact abs_of_nonneg (by norm_num)
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM4 : (65 : ℝ) ≤ M := ev.range 65 (by norm_num)
  have hS := asw_bound ev.hr ev.hu0 H.m hdm (by rw [habs]; linarith)
  rw [habs] at hS
  have hu65 : u * (64 + 1 / 1000) ≤ 1 / 2 ^ 24 * 65 :=
    mul_le_mul ev.hu1 (by norm_num) (by norm_num) (by positivity)
  have hη' := eta_tiny ev.hη1
  have hS2 : |asw fl H.m dm| ≤ 65 := by
    have h1 : (1 : ℝ) / 2 ^ 24 * 65 + 1 / 10 ^ 40 ≤ 1 / 2 := by norm_num
    linarith
  have hbias : H.bias fl dm i t = fl (asw fl H.m dm * ((t : ℝ) - (i : ℝ))) := by
    simp [AHead.bias]
  rw [hbias]
  generalize asw fl H.m dm = S at hS2 ⊢
  have ht' : (t : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast ht
  have hi' : (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hi
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hti : |(t : ℝ) - (i : ℝ)| ≤ ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hab : |S * ((t : ℝ) - (i : ℝ))| ≤ 65 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hS2 hti (abs_nonneg _) (by norm_num)
  have hB := ev.rangeN 65 (by norm_num) (by norm_num)
  have h := ev.hr.bound ev.hu0 hab hB
  have hu65n := u_mul ev 65 (by norm_num)
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem close_cons_mk {a b : ℝ} {x y : List ℝ} {e X : ℝ} (h1 : |a - b| ≤ e) (h2 : |b| ≤ X)
    (h3 : Close x y e X) : Close (a :: x) (b :: y) e X := by
  obtain ⟨hl, hk⟩ := h3
  refine ⟨by simp [hl], ?_⟩
  intro k hk'
  cases k with
  | zero => exact ⟨by simpa using h1, by simpa using h2⟩
  | succ k =>
    have := hk k (by simpa using hk')
    simpa using this

theorem armat_zero {fl : ℝ → ℝ} (x : Vec) (d : ℕ → ℕ → ℝ) (ε : ℝ)
    (h0 : ∀ r, |ardot fl (zrow 10) x (d r) 0 0| ≤ ε) :
    ∀ (n i : ℕ), Close (armat fl (List.replicate n (zrow 10)) x d i) (List.replicate n 0) ε 0
  | 0, i => by simp [armat, Close]
  | n + 1, i => by
      have ih := armat_zero x d ε h0 n (i + 1)
      have e : armat fl (List.replicate (n + 1) (zrow 10)) x d i
          = ardot fl (zrow 10) x (d i) 0 0 :: armat fl (List.replicate n (zrow 10)) x d (i + 1) := rfl
      rw [e, List.replicate_succ]
      exact close_cons_mk (by simpa using h0 i) (by simp) ih

theorem dotR_rep0 : ∀ (x : List ℝ) (n : ℕ), dotR x (List.replicate n 0) = 0
  | [], n => by simp [dotR]
  | a :: x, 0 => by simp [dotR]
  | a :: x, n + 1 => by
      have ih := dotR_rep0 x n
      unfold dotR at ih ⊢
      simp [List.replicate_succ, ih]

theorem content_le (ev : Ctx u η M fl ex p w) (H : AHead) (hA : H.A = zA)
    (x : ℕ → Vec) (Xa : List ℝ) (hXl : Xa.length = 10)
    (hXb : ∀ k, k < 10 → 0 ≤ Xa.getD k 0 ∧ Xa.getD k 0 ≤ 21 / 10) (hXs : Xa.sum ≤ 6)
    (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (i k : ℕ)
    (hxi : (x i).length = 10 ∧ ∀ k', k' < 10 → |(x i).getD k' 0| ≤ Xa.getD k' 0)
    (hxk : (x k).length = 10 ∧ ∀ k', k' < 10 → |(x k).getD k' 0| ≤ Xa.getD k' 0) :
    |pdot fl (x i) (armat fl H.A (x k) dA 0) 0| ≤ 1 / 4 := by
  have hrow : ∀ r, |ardot fl (zrow 10) (x k) (dA r) 0 0| ≤ 75 / 10000 := by
    intro r
    have := ev.zdot (K := 0) (W := 0) (r := zrow 10) (Or.inl rfl) (le_refl _) (by norm_num) (x k) Xa
      hXl hXb hXs hxk.1 hxk.2 (dA r) (hdA r)
    rw [dotQ_zrow, sub_zero] at this
    exact this
  have hAc : Close (armat fl H.A (x k) dA 0) (List.replicate 10 0) (75 / 10000) 0 := by
    rw [hA]; exact armat_zero (x k) dA (75 / 10000) hrow 10 0
  have hlen : (x i).length = (armat fl H.A (x k) dA 0).length := by
    have := close_len hAc
    rw [this, hxi.1]; simp
  have hC1 : Close (x i) (x i) 0 (21 / 10) := by
    refine ⟨rfl, fun k' hk' => ⟨by simp, ?_⟩⟩
    have hk'' : k' < 10 := by rwa [hxi.1] at hk'
    exact le_trans (hxi.2 k' hk'') (hXb k' hk'').2
  have hP := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (x i) (x i)
    (armat fl H.A (x k) dA 0) (List.replicate 10 0) (21 / 10) 0 0 (75 / 10000) hlen
    (by rw [hxi.1]; norm_num) hC1 hAc (by norm_num) (le_refl _) (le_refl _) (by norm_num)
    (by norm_num) (ev.range (2 ^ 30) (by norm_num))
  obtain ⟨p1, -⟩ := hP
  rw [dotR_rep0, sub_zero, hxi.1] at p1
  refine le_trans p1 ?_
  norm_num

theorem pick (ev : Ctx u η M fl ex p w) (H : AHead) (hA : H.A = zA) (hm : H.m = 64)
    (hmask : H.mask = Mask.causal ∨ H.mask = Mask.strict)
    (x : ℕ → Vec) (Xa : List ℝ) (hXl : Xa.length = 10)
    (hXb : ∀ k, k < 10 → 0 ≤ Xa.getD k 0 ∧ Xa.getD k 0 ≤ 21 / 10) (hXs : Xa.sum ≤ 6)
    (hx : ∀ j, j ≤ w.length → (x j).length = 10 ∧ ∀ k, k < 10 → |(x j).getD k 0| ≤ Xa.getD k 0)
    (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (dm : ℝ) (hdm : |dm| ≤ 1 / 1000)
    (dg : ℕ → ℝ) (dgb : ℝ) (i : ℕ) (hi : i ≤ w.length)
    (js : ℕ) (hjs : js ∈ H.cands fl dg dgb (w.length + 1) x i)
    (hmax : ∀ k ∈ H.cands fl dg dgb (w.length + 1) x i, k ≤ js)
    (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ k ∈ H.cands fl dg dgb (w.length + 1) x i, |f k| ≤ B) (hBM : 4 * B + 4 ≤ M) :
    |savg fl ex (H.cands fl dg dgb (w.length + 1) x i) (fun j => H.score fl dA dm x i j) f - f js|
      ≤ B / 100 + 1 / 2 ^ 90 := by
  have hle : ∀ k ∈ H.cands fl dg dgb (w.length + 1) x i, k ≤ i := by
    intro k hk
    rw [AHead.mem_cands] at hk
    rcases hmask with hmk | hmk
    · have := hk.1
      rw [hmk, Lane4.Seq.mem_cand_causal] at this
      exact this
    · have := hk.1
      rw [hmk, Lane4.Seq.mem_cand_strict] at this
      omega
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hmR : ((H.m : ℚ) : ℝ) = 64 := by rw [hm]; norm_num
  have hcnt : ∀ k ∈ H.cands fl dg dgb (w.length + 1) x i, |pdot fl (x i) (armat fl H.A (x k) dA 0) 0| ≤ 1 / 4 := by
    intro k hk
    have hkw : k ≤ w.length := le_trans (hle k hk) hi
    exact content_le ev H hA x Xa hXl hXb hXs dA hdA i k (hx i hi) (hx k hkw)
  have hS : ∀ k ∈ H.cands fl dg dgb (w.length + 1) x i,
      |H.score fl dA dm x i k| ≤ 68 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k hk
    have hkw : k ≤ w.length := le_trans (hle k hk) hi
    have hc := hcnt k hk
    have hb := bias_abs' ev H hm dm hdm i k (by omega) (by omega)
    have h1 : |H.bias fl dm i k + pdot fl (x i) (armat fl H.A (x k) dA 0) 0|
        ≤ 67 * ((w.length + 1 : ℕ) : ℝ) := le_trans (abs_add_le _ _) (by linarith)
    have hB := ev.rangeN 67 (by norm_num) (by norm_num)
    have h2 := ev.hr.bound ev.hu0 h1 hB
    have h3 := u_mul ev 67 (by norm_num)
    have hη' := eta_tiny ev.hη1
    unfold AHead.score
    linarith
  have hSM : 2 * (68 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 136 (by norm_num) (by norm_num)
    linarith
  have hgap : ∀ k ∈ H.cands fl dg dgb (w.length + 1) x i, k ≠ js →
      H.score fl dA dm x i k ≤ H.score fl dA dm x i js - 16 * (ndist js k : ℝ) := by
    intro k hk hne
    have hkj : k < js := lt_of_le_of_ne (hmax k hk) hne
    have hjw : js ≤ w.length := le_trans (hle js hjs) hi
    have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
      have := ev.rangeN 8192 (by norm_num) (by norm_num)
      have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
      rw [h12]; linarith
    obtain ⟨hg1, -⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
      (by norm_num) (by norm_num) H dm hdm (by rw [hmR]; norm_num) (by rw [hmR]; norm_num)
      (w.length + 1) i js k hkj (by omega) (by omega) ev.hn ev.hnη hM12
    rw [hmR] at hg1
    obtain ⟨hcj1, hcj2⟩ := abs_le.mp (hcnt js hjs)
    obtain ⟨hck1, hck2⟩ := abs_le.mp (hcnt k hk)
    have hbj := bias_abs' ev H hm dm hdm i js (by omega) (by omega)
    have hbk := bias_abs' ev H hm dm hdm i k (by omega) (by omega)
    have hB := ev.rangeN 67 (by norm_num) (by norm_num)
    have ha : |H.bias fl dm i k + pdot fl (x i) (armat fl H.A (x k) dA 0) 0|
        ≤ 67 * ((w.length + 1 : ℕ) : ℝ) :=
      le_trans (abs_add_le _ _) (by linarith [hcnt k hk])
    have hb : |H.bias fl dm i js + pdot fl (x i) (armat fl H.A (x js) dA 0) 0|
        ≤ 67 * ((w.length + 1 : ℕ) : ℝ) :=
      le_trans (abs_add_le _ _) (by linarith [hcnt js hjs])
    have hga := ev.hr.gap ev.hu0 ha hb hB
    have hu67 := u_mul ev 67 (by norm_num)
    have hη' := eta_tiny ev.hη1
    have hjk : (k : ℝ) + 1 ≤ (js : ℝ) := by exact_mod_cast hkj
    rw [ndist_cast, abs_of_nonneg (by linarith)]
    unfold AHead.score
    linarith
  have hlen : (H.cands fl dg dgb (w.length + 1) x i).length ≤ w.length + 1 := by
    have h1 : (H.cands fl dg dgb (w.length + 1) x i).length
        ≤ (cand H.mask (w.length + 1) i).length := List.length_filter_le _ _
    rcases hmask with hmk | hmk
    · rw [hmk] at h1; simp [cand] at h1; omega
    · rw [hmk] at h1; simp [cand] at h1; omega
  have hBM' : 4 * B + 4 ≤ M := hBM
  obtain ⟨hs1, -⟩ := soft_near (s := fun j => H.score fl dA dm x i j) (f := f) ev.hr ev.he
    ev.hu0 ev.hu1 ev.hη0 ev.hη1 (AHead.cands_nodup H fl dg dgb (w.length + 1) x i) hlen ev.hn
    ev.hnη hjs hgap hS hSM hf hBM'
  exact hs1

theorem Ctx.add2m (ev : Ctx u η M fl ex p w) {a b m t s ea eb em : ℝ} (ha : |a - t| ≤ ea)
    (hb : |b - s| ≤ eb) (hm : |m| ≤ em) (hB : |t| + |s| + ea + eb + em ≤ 90) :
    |fl (fl (a + b) + m) - (t + s)| ≤ ea + eb + em + 2 / 100000 := by
  have n0 : 0 ≤ ea := le_trans (abs_nonneg _) ha
  have n1 : 0 ≤ eb := le_trans (abs_nonneg _) hb
  have n2 : 0 ≤ em := le_trans (abs_nonneg _) hm
  have t1 := abs_add_le t s
  have a1 := abs_nonneg s
  have a2 := abs_nonneg t
  have s1 := ev.fl_step ha hb (by linarith)
  have hm' : |m - 0| ≤ em := by simpa using hm
  have s2 := ev.fl_step s1 hm' (by rw [add_zero]; linarith)
  rw [add_zero] at s2
  linarith

theorem relu_fl_pos {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149) {x : ℝ} (hx : |x| ≤ 1) (hM : 1 ≤ M)
    (hpos : 1 / 100 < x) : 0 < Lane4.relu (fl x) := by
  have h1 := hr.lower hu0 hx hM
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have h4 : u * 1 ≤ 1 / 2 ^ 24 := by linarith
  have h5 : 0 < fl x := by linarith
  unfold Lane4.relu
  exact lt_of_lt_of_le h5 (le_max_left _ _)

theorem exists_max : ∀ (cs : List ℕ), cs ≠ [] → ∃ js ∈ cs, ∀ k ∈ cs, k ≤ js
  | [], hne => absurd rfl hne
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: t, _ => by
      obtain ⟨js, hjs, hmx⟩ := exists_max (b :: t) (by simp)
      rcases le_total a js with hle | hle
      · refine ⟨js, List.mem_cons_of_mem _ hjs, fun k hk => ?_⟩
        rcases List.mem_cons.mp hk with hk | hk
        · rw [hk]; exact hle
        · exact hmx k hk
      · refine ⟨a, by simp, fun k hk => ?_⟩
        rcases List.mem_cons.mp hk with hk | hk
        · rw [hk]
        · exact le_trans (hmx k hk) hle

/-! ## Block 1 -/

theorem att1_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    (att1 fl ex p w i).length = 10 := by
  unfold att1 AHead.attn
  rw [aattnRows_len]
  rfl

theorem mlp1_len (fl : ℝ → ℝ) (p : APert) : (mlp1 fl p).length = 10 := by
  unfold mlp1
  rw [araffine_len]
  simp [zrow]

theorem x1_len (ev : Ctx u η M fl ex p w) (j : ℕ) : (x1f fl ex p w j).length = 10 := by
  rw [x1f_eq]
  exact radd_len10 fl (radd_len10 fl (init_len ev j) (att1_len fl ex p w j)) (mlp1_len fl p)

theorem x1_getD (ev : Ctx u η M fl ex p w) (j k : ℕ) (hk : k < 10) :
    (x1f fl ex p w j).getD k 0 = fl (fl ((net.init fl p w j).getD k 0
      + (att1 fl ex p w j).getD k 0) + (mlp1 fl p).getD k 0) := by
  have l0 := init_len ev j
  have l1 := att1_len fl ex p w j
  have l2 := mlp1_len fl p
  have l01 := radd_len10 fl l0 l1
  rw [x1f_eq, radd_getD fl (radd fl (net.init fl p w j) (att1 fl ex p w j)) (mlp1 fl p) k
    (by omega) (by omega), radd_getD fl (net.init fl p w j) (att1 fl ex p w j) k
    (by omega) (by omega)]

theorem mlp1_small (ev : Ctx u η M fl ex p w) (k : ℕ) (hk : k < 10) :
    |(mlp1 fl p).getD k 0| ≤ 11 / 10000 := by
  have e1 : (mlp1 fl p).getD k 0 = fl (ardot fl ((List.replicate 10 ([] : List ℚ)).getD k [])
      [] (p.W2 0 (0 + k)) 0 0 + asw fl ((zrow 10).getD k 0) (p.b2 0 (0 + k))) :=
    araffine_getD fl _ _ _ _ _ 0 k (by simpa using hk) (by simpa [zrow] using hk)
  rw [e1, rep_getD ([] : List ℚ) [] 10 k hk, zrow_getD 10 k hk]
  have e2 : ardot fl ([] : List ℚ) [] (p.W2 0 (0 + k)) 0 0 = 0 := rfl
  rw [e2]
  exact ev.mz (ev.hp.b2 0 (0 + k))

theorem gate1_zero (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    hd1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  have hd := ev.zdot (K := 0) (W := 0) (r := hd1.g) (Or.inl rfl) (le_refl _) (by norm_num)
    (net.init fl p w j) Xa0 Xa0_len Xa0_get Xa0_sum (init_len ev j)
    (fun k hk => init_abs ev j k hk) (p.g 0 0) (ev.hp.g 0 0)
  have hg : hd1.g = zrow 10 := rfl
  rw [hg, dotQ_zrow, sub_zero] at hd
  have hgb : hd1.gb = -1 := rfl
  have hb := ev.aswb (-1) (ev.hp.gb 0 0) (by norm_num)
  have hc : (((-1 : ℚ)) : ℝ) = -1 := by norm_num
  rw [hc] at hb
  unfold AHead.gate
  rw [hg, hgb]
  obtain ⟨hd1', hd2'⟩ := abs_le.mp hd
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hM2 : (2 : ℝ) ≤ M := ev.range 2 (by norm_num)
  apply relu_fl_zero ev.hr
  · linarith
  · linarith

theorem cs1_mem (ev : Ctx u η M fl ex p w) (i j : ℕ) (hi : i ≤ w.length) :
    j ∈ hd1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i ↔ j < i := by
  rw [AHead.mem_cands]
  have hm : hd1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, gate1_zero ev j (by omega)⟩⟩

theorem V1_RT (k : ℕ) (hk : k < 10) : RT 10 3 1 (hd1.V.getD k []) := by
  interval_cases k <;> (first
    | exact Or.inl rfl
    | exact Or.inr ⟨0, by norm_num, by norm_num, 1, rfl, by norm_num⟩
    | exact Or.inr ⟨1, by norm_num, by norm_num, 1, rfl, by norm_num⟩
    | exact Or.inr ⟨2, by norm_num, by norm_num, 1, rfl, by norm_num⟩)

theorem V2_getD (c k : ℕ) (hk : k < 10) :
    (hd2 c).V.getD k [] = if k = 6 + c then unitRow 10 3 2 else zrow 10 := by
  interval_cases k <;> rfl

theorem V2_RT (c k : ℕ) (hk : k < 10) : RT 10 4 2 ((hd2 c).V.getD k []) := by
  rw [V2_getD c k hk]
  split_ifs
  · exact Or.inr ⟨3, by norm_num, by norm_num, 2, rfl, by norm_num⟩
  · exact Or.inl rfl

theorem Xi0_low (k : ℕ) (hk : k < 3) : Xi0.getD k 0 = 1 / 2 := by
  interval_cases k <;> norm_num [Xi0]

noncomputable def ia1 (w : List ℕ) (j k : ℕ) : ℝ :=
  if j = 0 then 0 else dotQ (hd1.V.getD k []) (xh0t (tokAt w (j - 1)))

theorem V1_vdot (ev : Ctx u η M fl ex p w) (j' k : ℕ) (hk : k < 10) :
    |ardot fl (hd1.V.getD k []) (net.init fl p w j') (p.V 0 0 k) 0 0
      - dotQ (hd1.V.getD k []) (xh0t (tokAt w j'))| ≤ 86 / 10000 := by
  have hrow := V1_RT k hk
  have h1 := ev.zdot hrow (by norm_num) (by norm_num) (net.init fl p w j') Xa0 Xa0_len Xa0_get
    Xa0_sum (init_len ev j') (fun k' hk' => init_abs ev j' k' hk') (p.V 0 0 k) (ev.hp.V 0 0 k)
  have h2 := RT_near hrow (by norm_num) (by norm_num) (init_len ev j') (xh0t_len _)
    (fun k' hk' => init_close ev j' k' (by omega))
  have h3 := abs_sub_le (ardot fl (hd1.V.getD k []) (net.init fl p w j') (p.V 0 0 k) 0 0)
    (dotQ (hd1.V.getD k []) (net.init fl p w j')) (dotQ (hd1.V.getD k []) (xh0t (tokAt w j')))
  linarith

theorem V1_dmag (k : ℕ) (hk : k < 10) (t : ℕ) :
    |dotQ (hd1.V.getD k []) (xh0t t)| ≤ 1 / 2 := by
  have h := RT_mag (V1_RT k hk) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) (xh0t_len t)
    (fun k' hk' => by
      have h1 := xh0t_abs t k' (by omega)
      have h2 := Xi0_low k' hk'
      linarith)
  linarith

theorem ia1_le (w : List ℕ) (j k : ℕ) (hk : k < 10) : |ia1 w j k| ≤ 1 / 2 := by
  unfold ia1
  split_ifs
  · norm_num
  · exact V1_dmag k hk _

theorem head1_coord (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) (k : ℕ)
    (hk : k < 10) : |(att1 fl ex p w j).getD k 0 - ia1 w j k| ≤ 14 / 1000 := by
  have hVl : hd1.V.length = 10 := rfl
  unfold att1
  rw [attn_getD fl ex hd1 _ _ _ _ _ _ _ j k (by rw [hVl]; exact hk)]
  by_cases hj0 : j = 0
  · subst hj0
    have hc : hd1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) 0 = [] := by
      unfold AHead.cands
      have : cand hd1.mask (w.length + 1) 0 = [] := by simp [hd1, cand]
      rw [this]; rfl
    rw [hc]
    have hz := soft_zeros (fl := fl) (ex := ex) ev.hr (c := ([] : List ℕ))
      (s := fun j' => hd1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) 0 j')
      (f := fun j' => ardot fl (hd1.V.getD k []) (net.init fl p w j') (p.V 0 0 k) 0 0) (by simp)
    rw [hz]
    norm_num [ia1]
  · have hcs : ∀ j', j' ∈ hd1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) j
        ↔ j' < j := fun j' => cs1_mem ev j j' hj
    have hfd : ∀ j', j' ≤ w.length → |ardot fl (hd1.V.getD k []) (net.init fl p w j')
        (p.V 0 0 k) 0 0 - dotQ (hd1.V.getD k []) (xh0t (tokAt w j'))| ≤ 86 / 10000 :=
      fun j' _ => V1_vdot ev j' k hk
    have hf : ∀ k' ∈ hd1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) j,
        |ardot fl (hd1.V.getD k []) (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ 51 / 100 := by
      intro k' hk'
      have hk'' : k' < j := (hcs k').mp hk'
      have h1 := hfd k' (by omega)
      have h2 := V1_dmag k hk (tokAt w k')
      have h3 := abs_sub_abs_le_abs_sub (ardot fl (hd1.V.getD k []) (net.init fl p w k')
        (p.V 0 0 k) 0 0) (dotQ (hd1.V.getD k []) (xh0t (tokAt w k')))
      linarith
    have hpick := pick ev hd1 rfl rfl (Or.inr rfl) (net.init fl p w) Xa0 Xa0_len Xa0_get Xa0_sum
      (fun j' _ => init_state ev j') (p.A 0 0) (ev.hp.A 0 0) (p.m 0 0) (ev.hp.m 0 0)
      (p.g 0 0) (p.gb 0 0) j hj (j - 1) ((hcs (j - 1)).mpr (by omega))
      (fun k' hk' => by have := (hcs k').mp hk'; omega)
      (fun j' => ardot fl (hd1.V.getD k []) (net.init fl p w j') (p.V 0 0 k) 0 0) (51 / 100)
      hf (by have := ev.range 7 (by norm_num); linarith)
    beta_reduce at hpick
    have hia : ia1 w j k = dotQ (hd1.V.getD k []) (xh0t (tokAt w (j - 1))) := by
      unfold ia1; rw [if_neg hj0]
    rw [hia]
    have h1 := hfd (j - 1) (by omega)
    have h2 : (51 : ℝ) / 100 / 100 + 1 / 2 ^ 90 ≤ 52 / 10000 := by norm_num
    refine le_trans (abs_sub_le _ (ardot fl (hd1.V.getD k []) (net.init fl p w (j - 1))
      (p.V 0 0 k) 0 0) _) ?_
    linarith

theorem ideal1 (w : List ℕ) (j k : ℕ) (hk : k < 10) :
    (xh0t (tokAt w j)).getD k 0 + ia1 w j k
      = (xh1t (tokAt w j) (tokAt w (j - 1))).getD k 0 := by
  unfold ia1
  by_cases hj0 : j = 0
  · subst hj0
    have e : tokAt w (0 - 1) = 0 := Lane4.Seq.tokAt_zero w
    rw [if_pos rfl, e]
    interval_cases k <;> simp [xh0t, xh1t, Lane4.Seq.tokAt_zero]
  · rw [if_neg hj0]
    by_cases h46 : 4 ≤ k ∧ k ≤ 6
    · obtain ⟨h4, h6⟩ := h46
      have hrow : hd1.V.getD k [] = unitRow 10 (k - 4) 1 := by
        interval_cases k <;> rfl
      rw [hrow, dotQ_unitRow 10 (k - 4) (by omega) 1 _ (xh0t_len _)]
      interval_cases k <;> simp [xh0t, xh1t]
    · have hrow : hd1.V.getD k [] = zrow 10 := by
        interval_cases k <;> first | rfl | (exfalso; omega)
      rw [hrow, dotQ_zrow]
      interval_cases k <;> first | (exfalso; omega) | simp [xh0t, xh1t]

theorem x1_close (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) (k : ℕ) (hk : k < 10) :
    |(x1f fl ex p w j).getD k 0 - (xh1t (tokAt w j) (tokAt w (j - 1))).getD k 0| ≤ 17 / 1000 := by
  rw [x1_getD ev j k hk, ← ideal1 w j k hk]
  have h0 := init_close ev j k hk
  have h1 := head1_coord ev j hj k hk
  have hm := mlp1_small ev k hk
  have h2 := xh0t_abs (tokAt w j) k hk
  have h3 := ia1_le w j k hk
  have h4 : Xi0.getD k 0 ≤ 2 := by interval_cases k <;> norm_num [Xi0]
  have := ev.add2m h0 h1 hm (by linarith [abs_nonneg ((xh0t (tokAt w j)).getD k 0)])
  linarith

theorem x1_abs (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) (k : ℕ) (hk : k < 10) :
    |(x1f fl ex p w j).getD k 0| ≤ Xa1.getD k 0 := by
  have h1 := x1_close ev j hj k hk
  have h2 := xh1t_abs (tokAt w j) (tokAt w (j - 1)) k hk
  have h3 := Xa1_ge k hk
  have := abs_close_le h1 h2
  linarith

theorem x1_state (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : j ≤ w.length) :
    (x1f fl ex p w j).length = 10 ∧
      ∀ k, k < 10 → |(x1f fl ex p w j).getD k 0| ≤ Xa1.getD k 0 :=
  ⟨x1_len ev j, fun k hk => x1_abs ev j hj k hk⟩

/-! ## Block 2: the heads -/

theorem head2_gate (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3)
    (dg : ℕ → ℝ) (hdg : ∀ k, |dg k| ≤ 1 / 1000) (dgb : ℝ) (hdgb : |dgb| ≤ 1 / 1000)
    (j : ℕ) (hj : j ≤ w.length) :
    ((hd2 c).gate fl dg dgb (x1f fl ex p w j) = 0 ↔ tokAt w (j - 1) = c) := by
  have hx1 := x1_state ev j hj
  have hrow : RT 10 7 2 (hd2 c).g := Or.inr ⟨3 + c, by omega, by omega, -2, rfl, by norm_num⟩
  have hd := ev.zdot hrow (by norm_num) (le_refl _) (x1f fl ex p w j) Xa1 Xa1_len Xa1_get
    Xa1_sum hx1.1 hx1.2 dg hdg
  have hg : (hd2 c).g = unitRow 10 (3 + c) (-2) := rfl
  have hdq : dotQ (hd2 c).g (x1f fl ex p w j) = -2 * (x1f fl ex p w j).getD (3 + c) 0 := by
    rw [hg, dotQ_unitRow 10 (3 + c) (by omega) (-2) _ hx1.1]; norm_num
  rw [hdq, hg] at hd
  have hcl := x1_close ev j hj (3 + c) (by omega)
  have hp : (xh1t (tokAt w j) (tokAt w (j - 1))).getD (3 + c) 0
      = (1 / 2) * (if tokAt w (j - 1) = c then 1 else 0) := by
    interval_cases c <;> simp [xh1t]
  rw [hp] at hcl
  have hb := ev.aswb (1 / 2) hdgb (by norm_num)
  have hc12 : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by norm_num
  rw [hc12] at hb
  have hgb : (hd2 c).gb = 1 / 2 := rfl
  have hM2 : (2 : ℝ) ≤ M := ev.range 2 (by norm_num)
  unfold AHead.gate
  rw [hg, hgb]
  obtain ⟨hd1', hd2'⟩ := abs_le.mp hd
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hc1', hc2'⟩ := abs_le.mp hcl
  by_cases hmatch : tokAt w (j - 1) = c
  · rw [if_pos hmatch] at hc1' hc2'
    constructor
    · intro _; exact hmatch
    · intro _
      apply relu_fl_zero ev.hr
      · linarith
      · linarith
  · rw [if_neg hmatch] at hc1' hc2'
    constructor
    · intro h0
      exfalso
      have hpos := relu_fl_pos ev.hr ev.hu0 ev.hu1 ev.hη1
        (x := ardot fl (unitRow 10 (3 + c) (-2)) (x1f fl ex p w j) dg 0 0 + asw fl (1 / 2) dgb)
        (by rw [abs_le]; constructor <;> linarith) (by linarith) (by linarith)
      rw [h0] at hpos
      exact lt_irrefl _ hpos
    · intro h0; exact absurd h0 hmatch

theorem cs2_mem (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i j : ℕ)
    (hi : i ≤ w.length) : j ∈ cs2 fl ex p w c i ↔ j ≤ i ∧ tokAt w (j - 1) = c := by
  unfold cs2
  rw [AHead.mem_cands]
  have hm : (hd2 c).mask = Mask.causal := rfl
  rw [hm, Lane4.Seq.mem_cand_causal]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (head2_gate ev c hc1 hc3 _ (ev.hp.g 1 (c - 1)) _ (ev.hp.gb 1 (c - 1)) j
      (by omega)).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (head2_gate ev c hc1 hc3 _ (ev.hp.g 1 (c - 1)) _ (ev.hp.gb 1 (c - 1)) j
      (by omega)).mpr h2⟩

theorem head2_core (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) (k : ℕ) (hk : k < 10) (B : ℝ)
    (hB : ∀ j, j ≤ w.length →
      |ardot fl ((hd2 c).V.getD k []) (x1f fl ex p w j) (p.V 1 (c - 1) k) 0 0| ≤ B)
    (hBM : 4 * B + 4 ≤ M) :
    ((att2 fl ex p w c i).getD k 0 = 0 ∧ cs2 fl ex p w c i = []) ∨
    ∃ js, js ∈ cs2 fl ex p w c i ∧ (∀ k' ∈ cs2 fl ex p w c i, k' ≤ js) ∧
      |(att2 fl ex p w c i).getD k 0
        - ardot fl ((hd2 c).V.getD k []) (x1f fl ex p w js) (p.V 1 (c - 1) k) 0 0|
        ≤ B / 100 + 1 / 2 ^ 90 := by
  have hVl : (hd2 c).V.length = 10 := rfl
  have e1 : (att2 fl ex p w c i).getD k 0 = savg fl ex (cs2 fl ex p w c i)
      (fun j => (hd2 c).score fl (p.A 1 (c - 1)) (p.m 1 (c - 1)) (x1f fl ex p w) i j)
      (fun j => ardot fl ((hd2 c).V.getD k []) (x1f fl ex p w j) (p.V 1 (c - 1) k) 0 0) :=
    attn_getD fl ex (hd2 c) _ _ _ _ _ _ _ i k (by rw [hVl]; exact hk)
  by_cases hnil : cs2 fl ex p w c i = []
  · left
    refine ⟨?_, hnil⟩
    rw [e1, hnil]
    exact soft_zeros (fl := fl) (ex := ex) ev.hr (by simp)
  · right
    obtain ⟨js, hjs, hmx⟩ := exists_max _ hnil
    refine ⟨js, hjs, hmx, ?_⟩
    rw [e1]
    exact pick ev (hd2 c) rfl rfl (Or.inl rfl) (x1f fl ex p w) Xa1 Xa1_len Xa1_get Xa1_sum
      (fun j hj => x1_state ev j hj) (p.A 1 (c - 1)) (ev.hp.A 1 (c - 1)) (p.m 1 (c - 1))
      (ev.hp.m 1 (c - 1)) (p.g 1 (c - 1)) (p.gb 1 (c - 1)) i hi js hjs hmx _ B
      (fun k' hk' => hB k' (le_trans ((cs2_mem ev c hc1 hc3 i k' hi).mp hk').1 hi)) hBM

theorem head2_zero (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) (k : ℕ) (hk : k < 10) (hne : k ≠ 6 + c) :
    |(att2 fl ex p w c i).getD k 0| ≤ 77 / 10000 := by
  have hrowz : (hd2 c).V.getD k [] = zrow 10 := by rw [V2_getD c k hk, if_neg hne]
  have hB0 : ∀ j, j ≤ w.length →
      |ardot fl ((hd2 c).V.getD k []) (x1f fl ex p w j) (p.V 1 (c - 1) k) 0 0| ≤ 75 / 10000 := by
    intro j hj
    have hx1 := x1_state ev j hj
    have h1 := ev.zdot (V2_RT c k hk) (by norm_num) (le_refl _) (x1f fl ex p w j) Xa1 Xa1_len
      Xa1_get Xa1_sum hx1.1 hx1.2 (p.V 1 (c - 1) k) (ev.hp.V 1 (c - 1) k)
    rw [hrowz, dotQ_zrow, sub_zero] at h1
    rw [hrowz]
    exact h1
  have hB : ∀ j, j ≤ w.length →
      |ardot fl ((hd2 c).V.getD k []) (x1f fl ex p w j) (p.V 1 (c - 1) k) 0 0| ≤ 1 / 100 :=
    fun j hj => le_trans (hB0 j hj) (by norm_num)
  rcases head2_core ev c hc1 hc3 i hi k hk (1 / 100) hB
      (by have := ev.range 5 (by norm_num); linarith) with ⟨h0, _⟩ | ⟨js, hjs, hmx, hs⟩
  · rw [h0]; norm_num
  · have hjw := ((cs2_mem ev c hc1 hc3 i js hi).mp hjs).1
    have h1 := hB0 js (le_trans hjw hi)
    have h2 : (1 : ℝ) / 100 / 100 + 1 / 2 ^ 90 ≤ 2 / 10000 := by norm_num
    have h3 := abs_sub_abs_le_abs_sub ((att2 fl ex p w c i).getD k 0)
      (ardot fl ((hd2 c).V.getD k []) (x1f fl ex p w js) (p.V 1 (c - 1) k) 0 0)
    linarith

theorem head2_own_aux (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) :
    ((att2 fl ex p w c i).getD (6 + c) 0 = 0 ∧ cs2 fl ex p w c i = []) ∨
    ∃ js, js ∈ cs2 fl ex p w c i ∧ (∀ k' ∈ cs2 fl ex p w c i, k' ≤ js) ∧
      |(att2 fl ex p w c i).getD (6 + c) 0 - 2 * (h (tokAt w js) : ℝ)| ≤ 83 / 1000 ∧
      |(att2 fl ex p w c i).getD (6 + c) 0| ≤ 409 / 100 := by
  have hk : 6 + c < 10 := by omega
  have hrowu : (hd2 c).V.getD (6 + c) [] = unitRow 10 3 2 := by
    rw [V2_getD c (6 + c) hk, if_pos rfl]
  have hfd : ∀ j, j ≤ w.length →
      |ardot fl ((hd2 c).V.getD (6 + c) []) (x1f fl ex p w j) (p.V 1 (c - 1) (6 + c)) 0 0
        - 2 * (h (tokAt w j) : ℝ)| ≤ 42 / 1000 := by
    intro j hj
    have hx1 := x1_state ev j hj
    have h1 := ev.zdot (V2_RT c (6 + c) hk) (by norm_num) (le_refl _) (x1f fl ex p w j) Xa1
      Xa1_len Xa1_get Xa1_sum hx1.1 hx1.2 (p.V 1 (c - 1) (6 + c)) (ev.hp.V 1 (c - 1) (6 + c))
    rw [hrowu, dotQ_unitRow 10 3 (by norm_num) 2 _ hx1.1] at h1
    have e2 : (((2 : ℚ)) : ℝ) = 2 := by norm_num
    rw [e2] at h1
    have h2 := x1_close ev j hj 3 (by norm_num)
    have h3 : (xh1t (tokAt w j) (tokAt w (j - 1))).getD 3 0 = (h (tokAt w j) : ℝ) := by
      simp [xh1t]
    rw [h3] at h2
    rw [hrowu]
    obtain ⟨a1, a2⟩ := abs_le.mp h1
    obtain ⟨b1, b2⟩ := abs_le.mp h2
    rw [abs_le]
    constructor <;> linarith
  have hB : ∀ j, j ≤ w.length →
      |ardot fl ((hd2 c).V.getD (6 + c) []) (x1f fl ex p w j) (p.V 1 (c - 1) (6 + c)) 0 0|
        ≤ 405 / 100 := by
    intro j hj
    have h1 := hfd j hj
    have h2 := h_le2 (tokAt w j)
    have h3 := h_nn (tokAt w j)
    have h4 := abs_sub_abs_le_abs_sub (ardot fl ((hd2 c).V.getD (6 + c) [])
      (x1f fl ex p w j) (p.V 1 (c - 1) (6 + c)) 0 0) (2 * (h (tokAt w j) : ℝ))
    have h5 : |2 * (h (tokAt w j) : ℝ)| ≤ 4 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    linarith
  rcases head2_core ev c hc1 hc3 i hi (6 + c) hk (405 / 100) hB
      (by have := ev.range 21 (by norm_num); linarith) with ⟨h0, hn⟩ | ⟨js, hjs, hmx, hs⟩
  · left; exact ⟨h0, hn⟩
  · right
    have hjw := ((cs2_mem ev c hc1 hc3 i js hi).mp hjs).1
    have h1 := hfd js (le_trans hjw hi)
    have h2 : (405 : ℝ) / 100 / 100 + 1 / 2 ^ 90 ≤ 406 / 10000 := by norm_num
    have h3 := h_le2 (tokAt w js)
    have h4 := h_nn (tokAt w js)
    have h5 := abs_sub_abs_le_abs_sub (ardot fl ((hd2 c).V.getD (6 + c) [])
      (x1f fl ex p w js) (p.V 1 (c - 1) (6 + c)) 0 0) (2 * (h (tokAt w js) : ℝ))
    have h6 : |2 * (h (tokAt w js) : ℝ)| ≤ 4 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have h7 := abs_sub_abs_le_abs_sub ((att2 fl ex p w c i).getD (6 + c) 0)
      (ardot fl ((hd2 c).V.getD (6 + c) []) (x1f fl ex p w js) (p.V 1 (c - 1) (6 + c)) 0 0)
    refine ⟨js, hjs, hmx, ?_, ?_⟩
    · refine le_trans (abs_sub_le _ (ardot fl ((hd2 c).V.getD (6 + c) [])
        (x1f fl ex p w js) (p.V 1 (c - 1) (6 + c)) 0 0) _) ?_
      linarith
    · linarith

theorem head2_out (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) (k : ℕ) (hk : k < 10) :
    (k ≠ 6 + c → |(att2 fl ex p w c i).getD k 0| ≤ 77 / 10000) ∧
    (k = 6 + c → |(att2 fl ex p w c i).getD k 0| ≤ 409 / 100) := by
  constructor
  · intro hne
    exact head2_zero ev c hc1 hc3 i hi k hk hne
  · intro hkc
    subst hkc
    rcases head2_own_aux ev c hc1 hc3 i hi with ⟨h0, _⟩ | ⟨js, _, _, _, hm⟩
    · rw [h0]; norm_num
    · exact hm

/-! ## The previous occurrence -/

theorem find_aux (Q : ℕ → Bool) : ∀ N : ℕ,
    (∀ j, (List.range N).reverse.find? Q = some j →
      j < N ∧ Q j = true ∧ ∀ k, j < k → k < N → Q k = false) ∧
    ((List.range N).reverse.find? Q = none → ∀ k, k < N → Q k = false)
  | 0 => by simp
  | N + 1 => by
      have ih := find_aux Q N
      have hr : (List.range (N + 1)).reverse = N :: (List.range N).reverse := by
        simp [List.range_succ]
      rw [hr]
      by_cases hq : Q N = true
      · have e : (N :: (List.range N).reverse).find? Q = some N := by simp [hq]
        rw [e]
        refine ⟨?_, fun hn => by simp at hn⟩
        intro j hj
        have hjN : N = j := Option.some.inj hj
        subst hjN
        exact ⟨by omega, hq, fun k hk1 hk2 => by omega⟩
      · have hq' : Q N = false := by simpa using hq
        have e : (N :: (List.range N).reverse).find? Q = (List.range N).reverse.find? Q := by
          simp [hq']
        rw [e]
        constructor
        · intro j hj
          obtain ⟨h1, h2, h3⟩ := ih.1 j hj
          refine ⟨by omega, h2, fun k hk1 hk2 => ?_⟩
          by_cases hkN : k = N
          · subst hkN; exact hq'
          · exact h3 k hk1 (by omega)
        · intro hn k hk
          by_cases hkN : k = N
          · subst hkN; exact hq'
          · exact ih.2 hn k (by omega)

theorem prev_spec (w : List ℕ) (i : ℕ) :
    (prevOcc w i = none → ∀ j, j < i → 1 ≤ j → tokAt w j ≠ tokAt w i) ∧
    (∀ j0, prevOcc w i = some j0 → j0 < i ∧ 1 ≤ j0 ∧ tokAt w j0 = tokAt w i ∧
      ∀ j, j0 < j → j < i → 1 ≤ j → tokAt w j ≠ tokAt w i) := by
  have hq : ∀ j, (decide (1 ≤ j) && (tokAt w j == tokAt w i)) = true
      ↔ 1 ≤ j ∧ tokAt w j = tokAt w i := by
    intro j; simp
  have F := find_aux (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i)) i
  constructor
  · intro hn j hj h1 heq
    have h3 : (decide (1 ≤ j) && (tokAt w j == tokAt w i)) = false := F.2 hn j hj
    have h2 : (decide (1 ≤ j) && (tokAt w j == tokAt w i)) = true := (hq j).mpr ⟨h1, heq⟩
    rw [h2] at h3
    simp at h3
  · intro j0 hs
    obtain ⟨h1, h2, h3⟩ := F.1 j0 hs
    obtain ⟨h4, h5⟩ := (hq j0).mp h2
    refine ⟨h1, h4, h5, fun j hj1 hj2 hj3 heq => ?_⟩
    have h6 : (decide (1 ≤ j) && (tokAt w j == tokAt w i)) = false := h3 j hj1 hj2
    have h7 : (decide (1 ≤ j) && (tokAt w j == tokAt w i)) = true := (hq j).mpr ⟨hj3, heq⟩
    rw [h7] at h6
    simp at h6

theorem tok_pos_ne (w : List ℕ) (j c : ℕ) (hc : 1 ≤ c) (hh : tokAt w j = c) : 1 ≤ j := by
  by_contra h0
  have : j = 0 := by omega
  subst this
  rw [Lane4.Seq.tokAt_zero] at hh
  omega

theorem cs2_spec (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) (hct : tokAt w i = c) :
    (prevOcc w i = none → cs2 fl ex p w c i = []) ∧
    (∀ j0, prevOcc w i = some j0 → (j0 + 1) ∈ cs2 fl ex p w c i ∧
      ∀ k ∈ cs2 fl ex p w c i, k ≤ j0 + 1) := by
  have hsp := prev_spec w i
  rw [hct] at hsp
  constructor
  · intro hn
    rw [List.eq_nil_iff_forall_not_mem]
    intro k hk
    obtain ⟨hk1, hk2⟩ := (cs2_mem ev c hc1 hc3 i k hi).mp hk
    have hj1 := tok_pos_ne w (k - 1) c hc1 hk2
    exact (hsp.1 hn (k - 1) (by omega) hj1) hk2
  · intro j0 hs
    obtain ⟨h1, h2, h3, h4⟩ := hsp.2 j0 hs
    refine ⟨(cs2_mem ev c hc1 hc3 i (j0 + 1) hi).mpr ⟨by omega, by simpa using h3⟩, ?_⟩
    intro k hk
    obtain ⟨hk1, hk2⟩ := (cs2_mem ev c hc1 hc3 i k hi).mp hk
    have hj1 := tok_pos_ne w (k - 1) c hc1 hk2
    by_contra hgt
    push_neg at hgt
    exact h4 (k - 1) (by omega) (by omega) hj1 hk2

theorem head2_sel (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) (hct : tokAt w i = c) :
    |(att2 fl ex p w c i).getD (6 + c) 0 - 2 * ((target w i : ℕ) : ℝ)| ≤ 83 / 1000 := by
  have hsp := cs2_spec ev c hc1 hc3 i hi hct
  rcases head2_own_aux ev c hc1 hc3 i hi with ⟨h0, hnil⟩ | ⟨js, hjs, hmx, hs, _⟩
  · have hn : prevOcc w i = none := by
      cases hp : prevOcc w i with
      | none => rfl
      | some j0 =>
        exfalso
        have := (hsp.2 j0 hp).1
        rw [hnil] at this
        simp at this
    have ht : target w i = 0 := by unfold target; rw [hn]
    rw [h0, ht]; norm_num
  · cases hp : prevOcc w i with
    | none =>
      exfalso
      have := hsp.1 hp
      rw [this] at hjs
      simp at hjs
    | some j0 =>
      obtain ⟨hmem, hmx0⟩ := hsp.2 j0 hp
      have hjeq : js = j0 + 1 := le_antisymm (hmx0 js hjs) (hmx (j0 + 1) hmem)
      have ht : target w i = h (tokAt w js) := by
        unfold target; rw [hp]; subst hjeq; rfl
      rw [ht]
      exact hs

/-! ## Block 2: the state after the heads -/

theorem target_le (w : List ℕ) (i : ℕ) : target w i ≤ 2 := by
  unfold target
  cases prevOcc w i with
  | none => simp
  | some j => exact h_le2n _

theorem att2_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (c i : ℕ) :
    (att2 fl ex p w c i).length = 10 := by
  unfold att2 AHead.attn
  rw [aattnRows_len]
  rfl

theorem yf_len (ev : Ctx u η M fl ex p w) (i : ℕ) : (yf fl ex p w i).length = 10 := by
  unfold yf
  exact radd_len10 fl (radd_len10 fl (radd_len10 fl (x1_len ev i) (att2_len fl ex p w 1 i))
    (att2_len fl ex p w 2 i)) (att2_len fl ex p w 3 i)

theorem yf_getD (ev : Ctx u η M fl ex p w) (i k : ℕ) (hk : k < 10) :
    (yf fl ex p w i).getD k 0 = fl (fl (fl ((x1f fl ex p w i).getD k 0
      + (att2 fl ex p w 1 i).getD k 0) + (att2 fl ex p w 2 i).getD k 0)
      + (att2 fl ex p w 3 i).getD k 0) := by
  have l0 := x1_len ev i
  have l1 := att2_len fl ex p w 1 i
  have l2 := att2_len fl ex p w 2 i
  have l3 := att2_len fl ex p w 3 i
  have l01 := radd_len10 fl l0 l1
  have l012 := radd_len10 fl l01 l2
  unfold yf
  rw [radd_getD fl (radd fl (radd fl (x1f fl ex p w i) (att2 fl ex p w 1 i))
      (att2 fl ex p w 2 i)) (att2 fl ex p w 3 i) k (by omega) (by omega),
    radd_getD fl (radd fl (x1f fl ex p w i) (att2 fl ex p w 1 i)) (att2 fl ex p w 2 i) k
      (by omega) (by omega),
    radd_getD fl (x1f fl ex p w i) (att2 fl ex p w 1 i) k (by omega) (by omega)]

theorem y_gen (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 10)
    {b1 b2 b3 e1 e2 e3 : ℝ} (a1 : |(att2 fl ex p w 1 i).getD k 0 - b1| ≤ e1)
    (a2 : |(att2 fl ex p w 2 i).getD k 0 - b2| ≤ e2)
    (a3 : |(att2 fl ex p w 3 i).getD k 0 - b3| ≤ e3)
    (hB : |b1| + |b2| + |b3| + e1 + e2 + e3 ≤ 80) :
    |(yf fl ex p w i).getD k 0 - ((xh1t (tokAt w i) (tokAt w (i - 1))).getD k 0 + b1 + b2 + b3)|
      ≤ 17 / 1000 + e1 + e2 + e3 + 3 / 100000 := by
  rw [yf_getD ev i k hk]
  have hx := x1_close ev i hi k hk
  have hA : |(xh1t (tokAt w i) (tokAt w (i - 1))).getD k 0| ≤ 2 := by
    have h1 := xh1t_abs (tokAt w i) (tokAt w (i - 1)) k hk
    have h2 : Xi1.getD k 0 ≤ 2 := by interval_cases k <;> norm_num [Xi1]
    linarith
  have := ev.add3 hx a1 a2 a3 (by linarith)
  linarith

theorem y_low (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 7) :
    |(yf fl ex p w i).getD k 0 - (xh1t (tokAt w i) (tokAt w (i - 1))).getD k 0| ≤ 41 / 1000 := by
  have a1 := (head2_out ev 1 (by norm_num) (by norm_num) i hi k (by omega)).1 (by omega)
  have a2 := (head2_out ev 2 (by norm_num) (by norm_num) i hi k (by omega)).1 (by omega)
  have a3 := (head2_out ev 3 (by norm_num) (by norm_num) i hi k (by omega)).1 (by omega)
  have := y_gen ev i hi k (by omega) (b1 := 0) (b2 := 0) (b3 := 0) (e1 := 77 / 10000)
    (e2 := 77 / 10000) (e3 := 77 / 10000) (by simpa using a1) (by simpa using a2)
    (by simpa using a3) (by norm_num)
  simp only [add_zero] at this
  linarith

theorem y_mag (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) (k : ℕ) (hkc : k = 6 + c) :
    |(yf fl ex p w i).getD k 0| ≤ 413 / 100 := by
  have hk : k < 10 := by omega
  have hxi : (xh1t (tokAt w i) (tokAt w (i - 1))).getD k 0 = 0 := by
    subst hkc
    rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl <;> simp [xh1t]
  have hmain : ∀ e1 e2 e3 : ℝ, |(att2 fl ex p w 1 i).getD k 0| ≤ e1 →
      |(att2 fl ex p w 2 i).getD k 0| ≤ e2 → |(att2 fl ex p w 3 i).getD k 0| ≤ e3 →
      e1 + e2 + e3 ≤ 5 →
      |(yf fl ex p w i).getD k 0| ≤ 17 / 1000 + e1 + e2 + e3 + 3 / 100000 := by
    intro e1 e2 e3 a1 a2 a3 hs
    have := y_gen ev i hi k hk (b1 := 0) (b2 := 0) (b3 := 0) (e1 := e1) (e2 := e2) (e3 := e3)
      (by simpa using a1) (by simpa using a2) (by simpa using a3)
      (by simp only [abs_zero]; linarith)
    rw [hxi] at this
    simp only [add_zero, zero_add, sub_zero] at this
    exact this
  rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl
  · have a1 := (head2_out ev 1 (by norm_num) (by norm_num) i hi k hk).2 hkc
    have a2 := (head2_out ev 2 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have a3 := (head2_out ev 3 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have := hmain _ _ _ a1 a2 a3 (by norm_num)
    linarith
  · have a1 := (head2_out ev 1 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have a2 := (head2_out ev 2 (by norm_num) (by norm_num) i hi k hk).2 hkc
    have a3 := (head2_out ev 3 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have := hmain _ _ _ a1 a2 a3 (by norm_num)
    linarith
  · have a1 := (head2_out ev 1 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have a2 := (head2_out ev 2 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have a3 := (head2_out ev 3 (by norm_num) (by norm_num) i hi k hk).2 hkc
    have := hmain _ _ _ a1 a2 a3 (by norm_num)
    linarith

theorem y_sel (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) (hct : tokAt w i = c) (k : ℕ) (hkc : k = 6 + c) :
    |(yf fl ex p w i).getD k 0 - 2 * ((target w i : ℕ) : ℝ)| ≤ 116 / 1000 := by
  have hk : k < 10 := by omega
  have hxi : (xh1t (tokAt w i) (tokAt w (i - 1))).getD k 0 = 0 := by
    subst hkc
    rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl <;> simp [xh1t]
  have hT := target_le w i
  have hT0 : (0 : ℝ) ≤ ((target w i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT2 : ((target w i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hT
  have hT4 : |2 * ((target w i : ℕ) : ℝ)| ≤ 4 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hsel := head2_sel ev c hc1 hc3 i hi hct
  rw [← hkc] at hsel
  have hmain : ∀ b1 b2 b3 e1 e2 e3 : ℝ, |(att2 fl ex p w 1 i).getD k 0 - b1| ≤ e1 →
      |(att2 fl ex p w 2 i).getD k 0 - b2| ≤ e2 → |(att2 fl ex p w 3 i).getD k 0 - b3| ≤ e3 →
      |b1| + |b2| + |b3| + e1 + e2 + e3 ≤ 80 →
      |(yf fl ex p w i).getD k 0 - (b1 + b2 + b3)| ≤ 17 / 1000 + e1 + e2 + e3 + 3 / 100000 := by
    intro b1 b2 b3 e1 e2 e3 a1 a2 a3 hB
    have := y_gen ev i hi k hk a1 a2 a3 hB
    rw [hxi, zero_add] at this
    exact this
  rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl
  · have a2 := (head2_out ev 2 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have a3 := (head2_out ev 3 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have := hmain (2 * ((target w i : ℕ) : ℝ)) 0 0 (83 / 1000) (77 / 10000) (77 / 10000) hsel
      (by simpa using a2) (by simpa using a3) (by simp only [abs_zero]; linarith)
    simp only [add_zero] at this
    linarith
  · have a1 := (head2_out ev 1 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have a3 := (head2_out ev 3 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have := hmain 0 (2 * ((target w i : ℕ) : ℝ)) 0 (77 / 10000) (83 / 1000) (77 / 10000)
      (by simpa using a1) hsel (by simpa using a3) (by simp only [abs_zero]; linarith)
    simp only [add_zero, zero_add] at this
    linarith
  · have a1 := (head2_out ev 1 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have a2 := (head2_out ev 2 (by norm_num) (by norm_num) i hi k hk).1 (by omega)
    have := hmain 0 0 (2 * ((target w i : ℕ) : ℝ)) (77 / 10000) (77 / 10000) (83 / 1000)
      (by simpa using a1) (by simpa using a2) hsel (by simp only [abs_zero]; linarith)
    simp only [zero_add] at this
    linarith

theorem yf_abs (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 10) :
    |(yf fl ex p w i).getD k 0| ≤ Xay.getD k 0 := by
  by_cases h7 : k < 7
  · have h1 := y_low ev i hi k h7
    have h2 := xh1t_abs (tokAt w i) (tokAt w (i - 1)) k hk
    have h3 := Xay_ge k h7
    have := abs_close_le h1 h2
    linarith
  · have h7' : 7 ≤ k := by omega
    have h1 := y_mag ev (k - 6) (by omega) (by omega) i hi k (by omega)
    have h2 : Xay.getD k 0 = 42 / 10 := by
      interval_cases k <;> norm_num [Xay]
    linarith

/-! ## Block 2: the MLP -/

theorem hid2_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    (hid2 fl ex p w i).length = 3 := by
  unfold hid2
  rw [List.length_map, araffine_len]
  rfl

theorem hid2_getD (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i c : ℕ) (hc : c < 3) :
    (hid2 fl ex p w i).getD c 0 = Lane4.relu (fl (ardot fl (unitRow 10 c (-8)) (yf fl ex p w i)
      (p.W1 1 c) 0 0 + asw fl 2 (p.b1 1 c))) := by
  unfold hid2
  rw [map_relu_getD, araffine_getD fl blk2.W1 blk2.b1 (yf fl ex p w i) (p.W1 1) (p.b1 1) 0 c
    (by show c < 3; exact hc) (by show c < 3; exact hc)]
  have hr : blk2.W1.getD c [] = unitRow 10 c (-8) := by interval_cases c <;> rfl
  have hb : blk2.b1.getD c 0 = 2 := by interval_cases c <;> rfl
  rw [hr, hb, Nat.zero_add]

theorem u2_facts (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc : c < 3) :
    (tokAt w i = c + 1 → (hid2 fl ex p w i).getD c 0 = 0) ∧
    (tokAt w i ≠ c + 1 → 164 / 100 ≤ (hid2 fl ex p w i).getD c 0 ∧
      (hid2 fl ex p w i).getD c 0 ≤ 236 / 100) := by
  have hy := y_low ev i hi c (by omega)
  have hxh : (xh1t (tokAt w i) (tokAt w (i - 1))).getD c 0
      = 1 / 2 * (if tokAt w i = c + 1 then 1 else 0) := by
    interval_cases c <;> simp [xh1t]
  rw [hxh] at hy
  have hdot := ev.dotA 10 (by norm_num) (unitRow 10 c (-8)) (yf fl ex p w i) Xay (p.W1 1 c) 8
    (42 / 10) 18 (unitRow_len 10 c (by omega) _) (yf_len ev i) Xay_len (ev.hp.W1 1 c)
    (unitRow_ok 10 c (-8) 8 (by norm_num)) (by norm_num) (by norm_num)
    (fun k hk => ⟨yf_abs ev i hi k hk, (Xay_get k hk).2⟩) Xay_sum (by norm_num)
  rw [dotQ_unitRow 10 c (by omega) (-8) _ (yf_len ev i)] at hdot
  have e8 : (((-8 : ℚ)) : ℝ) = -8 := by norm_num
  rw [e8] at hdot
  have hnum : (1 : ℝ) / 1000 * 18 + ((10 : ℕ) : ℝ) * (8 + 1) * (42 / 10 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 26 / 1000 := by norm_num
  have hb := ev.aswb 2 (ev.hp.b1 1 c) (by norm_num)
  have e2 : (((2 : ℚ)) : ℝ) = 2 := by norm_num
  rw [e2] at hb
  rw [hid2_getD fl ex p w i c hc]
  obtain ⟨d1, d2⟩ := abs_le.mp (le_trans hdot hnum)
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨y1, y2⟩ := abs_le.mp hy
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ardot fl (unitRow 10 c (-8)) (yf fl ex p w i) (p.W1 1 c) 0 0
      + asw fl 2 (p.b1 1 c) := ⟨_, rfl⟩
  rw [← hz]
  by_cases hsel : tokAt w i = c + 1
  · rw [if_pos hsel] at y1 y2
    constructor
    · intro _
      apply relu_fl_zero ev.hr
      · linarith
      · linarith
    · intro hne; exact absurd hsel hne
  · rw [if_neg hsel] at y1 y2
    constructor
    · intro h1; exact absurd h1 hsel
    · intro _
      have hflb := ev.flabs (x := z) (by rw [abs_le]; constructor <;> linarith)
      obtain ⟨f1, f2⟩ := abs_le.mp hflb
      have hpos : 0 ≤ fl z := by linarith
      unfold Lane4.relu
      rw [max_eq_left hpos]
      constructor <;> linarith

theorem u2_bound (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc : c < 3) :
    0 ≤ (hid2 fl ex p w i).getD c 0 ∧ (hid2 fl ex p w i).getD c 0 ≤ 236 / 100 := by
  by_cases hsel : tokAt w i = c + 1
  · rw [(u2_facts ev i hi c hc).1 hsel]; norm_num
  · have := (u2_facts ev i hi c hc).2 hsel
    constructor <;> linarith [this.1, this.2]

theorem Xu_eq (k : ℕ) (hk : k < 3) : Xu.getD k 0 = 236 / 100 := by
  interval_cases k <;> norm_num [Xu]

theorem hid2_abs (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc : c < 3) :
    |(hid2 fl ex p w i).getD c 0| ≤ Xu.getD c 0 := by
  rw [abs_of_nonneg (u2_bound ev i hi c hc).1, Xu_eq c hc]
  exact (u2_bound ev i hi c hc).2

theorem Ctx.mfl (ev : Ctx u η M fl ex p w) {a d e : ℝ} (ha : |a| ≤ e) (hd : |d| ≤ 1 / 1000)
    (he : e ≤ 50) : |fl (a + asw fl (0 : ℚ) d)| ≤ e + 1001 / 1000000 + 1 / 100000 := by
  have h0 := ev.aswz hd
  have h1 : |a + asw fl (0 : ℚ) d| ≤ e + 1001 / 1000000 :=
    le_trans (abs_add_le _ _) (by linarith)
  have h2 := ev.flabs (x := a + asw fl (0 : ℚ) d) (by linarith [abs_nonneg a])
  have h3 := abs_sub_abs_le_abs_sub (fl (a + asw fl (0 : ℚ) d)) (a + asw fl (0 : ℚ) d)
  linarith

noncomputable def m2v (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i k : ℕ) : ℝ :=
  fl (ardot fl (blk2.W2.getD k []) (hid2 fl ex p w i) (p.W2 1 k) 0 0 + asw fl 0 (p.b2 1 k))

theorem y2_len (ev : Ctx u η M fl ex p w) (i : ℕ) : (y2f fl ex p w i).length = 10 := by
  rw [y2f_eq]
  refine radd_len10 fl (yf_len ev i) ?_
  rw [araffine_len]
  rfl

theorem y2_getD (ev : Ctx u η M fl ex p w) (i k : ℕ) (hk : k < 10) :
    (y2f fl ex p w i).getD k 0 = fl ((yf fl ex p w i).getD k 0 + m2v fl ex p w i k) := by
  have l0 := yf_len ev i
  have l1 : (araffine fl blk2.W2 blk2.b2 (hid2 fl ex p w i) (p.W2 1) (p.b2 1) 0).length = 10 := by
    rw [araffine_len]; rfl
  rw [y2f_eq, radd_getD fl (yf fl ex p w i)
    (araffine fl blk2.W2 blk2.b2 (hid2 fl ex p w i) (p.W2 1) (p.b2 1) 0) k (by omega) (by omega),
    araffine_getD fl blk2.W2 blk2.b2 (hid2 fl ex p w i) (p.W2 1) (p.b2 1) 0 k
      (by show k < 10; exact hk) (by show k < (zrow 10).length; rw [zrow_len]; exact hk)]
  have hb : blk2.b2.getD k 0 = 0 := zrow_getD 10 k hk
  rw [hb, Nat.zero_add] <;> rfl

theorem m2_low (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 10)
    (hk7 : ¬ (7 ≤ k ∧ k ≤ 9)) : |m2v fl ex p w i k| ≤ 9 / 1000 := by
  have hrow : blk2.W2.getD k [] = zrow 3 := by
    interval_cases k <;> first | rfl | (exfalso; omega)
  unfold m2v
  rw [hrow]
  have hd := ev.dotA 3 (by norm_num) (zrow 3) (hid2 fl ex p w i) Xu (p.W2 1 k) 0 (236 / 100)
    (71 / 10) (zrow_len 3) (hid2_len fl ex p w i) Xu_len (ev.hp.W2 1 k)
    (zrow_ok 3 0 (le_refl _)) (le_refl _) (by norm_num)
    (fun c hc => ⟨hid2_abs ev i hi c hc, (Xu_get c hc).2⟩) Xu_sum (by norm_num)
  rw [dotQ_zrow, sub_zero] at hd
  have hn : (1 : ℝ) / 1000 * (71 / 10) + ((3 : ℕ) : ℝ) * (0 + 1) * (236 / 100 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 75 / 10000 := by norm_num
  have := ev.mfl (le_trans hd hn) (ev.hp.b2 1 k) (by norm_num)
  linarith

theorem m2_dot (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc1 : 1 ≤ c)
    (hc3 : c ≤ 3) (k : ℕ) (hkc : k = 6 + c) :
    |ardot fl (blk2.W2.getD k []) (hid2 fl ex p w i) (p.W2 1 k) 0 0
      + 3 * (hid2 fl ex p w i).getD (c - 1) 0| ≤ 78 / 10000 := by
  have hrow : blk2.W2.getD k [] = unitRow 3 (c - 1) (-3) := by
    subst hkc
    rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl <;> rfl
  rw [hrow]
  have hd := ev.dotA 3 (by norm_num) (unitRow 3 (c - 1) (-3)) (hid2 fl ex p w i) Xu (p.W2 1 k) 3
    (236 / 100) (71 / 10) (unitRow_len 3 (c - 1) (by omega) _) (hid2_len fl ex p w i) Xu_len
    (ev.hp.W2 1 k) (unitRow_ok 3 (c - 1) (-3) 3 (by norm_num)) (by norm_num) (by norm_num)
    (fun c0 hc0 => ⟨hid2_abs ev i hi c0 hc0, (Xu_get c0 hc0).2⟩) Xu_sum (by norm_num)
  rw [dotQ_unitRow 3 (c - 1) (by omega) (-3) _ (hid2_len fl ex p w i)] at hd
  have e3 : (((-3 : ℚ)) : ℝ) = -3 := by norm_num
  rw [e3] at hd
  have hn : (1 : ℝ) / 1000 * (71 / 10) + ((3 : ℕ) : ℝ) * (3 + 1) * (236 / 100 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 78 / 10000 := by norm_num
  have hh := le_trans hd hn
  have e : ardot fl (unitRow 3 (c - 1) (-3)) (hid2 fl ex p w i) (p.W2 1 k) 0 0
      + 3 * (hid2 fl ex p w i).getD (c - 1) 0
      = ardot fl (unitRow 3 (c - 1) (-3)) (hid2 fl ex p w i) (p.W2 1 k) 0 0
        - (-3 * (hid2 fl ex p w i).getD (c - 1) 0) := by ring
  rw [e]
  exact hh

theorem m2_sel (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc1 : 1 ≤ c)
    (hc3 : c ≤ 3) (hct : tokAt w i = c) (k : ℕ) (hkc : k = 6 + c) :
    |m2v fl ex p w i k| ≤ 9 / 1000 := by
  have hu := (u2_facts ev i hi (c - 1) (by omega)).1 (by rw [Nat.sub_add_cancel hc1]; exact hct)
  have hd := m2_dot ev i hi c hc1 hc3 k hkc
  rw [hu] at hd
  have hd' : |ardot fl (blk2.W2.getD k []) (hid2 fl ex p w i) (p.W2 1 k) 0 0| ≤ 78 / 10000 := by
    simpa using hd
  unfold m2v
  have := ev.mfl hd' (ev.hp.b2 1 k) (by norm_num)
  linarith

theorem m2_uns (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc1 : 1 ≤ c)
    (hc3 : c ≤ 3) (hct : tokAt w i ≠ c) (k : ℕ) (hkc : k = 6 + c) :
    -709 / 100 ≤ m2v fl ex p w i k ∧ m2v fl ex p w i k ≤ -491 / 100 := by
  have hu := (u2_facts ev i hi (c - 1) (by omega)).2
    (by rw [Nat.sub_add_cancel hc1]; exact hct)
  have hd := m2_dot ev i hi c hc1 hc3 k hkc
  obtain ⟨d1, d2⟩ := abs_le.mp hd
  have hb := ev.aswz (ev.hp.b2 1 k)
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ardot fl (blk2.W2.getD k []) (hid2 fl ex p w i) (p.W2 1 k) 0 0
      + asw fl 0 (p.b2 1 k) := ⟨_, rfl⟩
  have hflb := ev.flabs (x := z) (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2])
  obtain ⟨f1, f2⟩ := abs_le.mp hflb
  unfold m2v
  rw [← hz]
  constructor <;> linarith [hu.1, hu.2]

theorem y2_r (ev : Ctx u η M fl ex p w) (c : ℕ) (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (i : ℕ)
    (hi : i ≤ w.length) (k : ℕ) (hkc : k = 6 + c) :
    (tokAt w i = c → |(y2f fl ex p w i).getD k 0 - 2 * ((target w i : ℕ) : ℝ)| ≤ 126 / 1000) ∧
    (tokAt w i ≠ c → (y2f fl ex p w i).getD k 0 ≤ -3 / 4) ∧
    |(y2f fl ex p w i).getD k 0| ≤ 113 / 10 ∧ (y2f fl ex p w i).getD k 0 ≤ 413 / 100 := by
  have hk : k < 10 := by omega
  rw [y2_getD ev i k hk]
  have hy := y_mag ev c hc1 hc3 i hi k hkc
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hT := target_le w i
  have hT0 : (0 : ℝ) ≤ ((target w i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT2 : ((target w i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hct
    have hs := y_sel ev c hc1 hc3 i hi hct k hkc
    have hm := m2_sel ev i hi c hc1 hc3 hct k hkc
    have := ev.fl_step (a := (yf fl ex p w i).getD k 0) (b := m2v fl ex p w i k)
      (t := 2 * ((target w i : ℕ) : ℝ)) (s := 0) (ea := 116 / 1000) (eb := 9 / 1000) hs
      (by simpa using hm) (by simp only [add_zero]; rw [abs_of_nonneg (by linarith)]; linarith)
    simp only [add_zero] at this
    linarith
  · intro hct
    obtain ⟨m1, m2⟩ := m2_uns ev i hi c hc1 hc3 hct k hkc
    have hfl := ev.flabs (x := (yf fl ex p w i).getD k 0 + m2v fl ex p w i k)
      (by rw [abs_le]; constructor <;> linarith)
    obtain ⟨f1, f2⟩ := abs_le.mp hfl
    linarith
  · by_cases hct : tokAt w i = c
    · have hs := y_sel ev c hc1 hc3 i hi hct k hkc
      have hm := m2_sel ev i hi c hc1 hc3 hct k hkc
      obtain ⟨s1, s2⟩ := abs_le.mp hs
      obtain ⟨m1, m2⟩ := abs_le.mp hm
      have hfl := ev.flabs (x := (yf fl ex p w i).getD k 0 + m2v fl ex p w i k)
        (by rw [abs_le]; constructor <;> linarith)
      obtain ⟨f1, f2⟩ := abs_le.mp hfl
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨m1, m2⟩ := m2_uns ev i hi c hc1 hc3 hct k hkc
      have hfl := ev.flabs (x := (yf fl ex p w i).getD k 0 + m2v fl ex p w i k)
        (by rw [abs_le]; constructor <;> linarith)
      obtain ⟨f1, f2⟩ := abs_le.mp hfl
      rw [abs_le]; constructor <;> linarith
  · by_cases hct : tokAt w i = c
    · have hs := y_sel ev c hc1 hc3 i hi hct k hkc
      have hm := m2_sel ev i hi c hc1 hc3 hct k hkc
      obtain ⟨s1, s2⟩ := abs_le.mp hs
      obtain ⟨m1, m2⟩ := abs_le.mp hm
      have hfl := ev.flabs (x := (yf fl ex p w i).getD k 0 + m2v fl ex p w i k)
        (by rw [abs_le]; constructor <;> linarith)
      obtain ⟨f1, f2⟩ := abs_le.mp hfl
      linarith
    · obtain ⟨m1, m2⟩ := m2_uns ev i hi c hc1 hc3 hct k hkc
      have hfl := ev.flabs (x := (yf fl ex p w i).getD k 0 + m2v fl ex p w i k)
        (by rw [abs_le]; constructor <;> linarith)
      obtain ⟨f1, f2⟩ := abs_le.mp hfl
      linarith

theorem y2_abs (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 10) :
    |(y2f fl ex p w i).getD k 0| ≤ Xayp.getD k 0 := by
  by_cases h7 : k < 7
  · rw [y2_getD ev i k hk]
    have hy := yf_abs ev i hi k hk
    have hm := m2_low ev i hi k hk (by omega)
    have hflb := ev.flabs (x := (yf fl ex p w i).getD k 0 + m2v fl ex p w i k)
      (by
        have := (Xay_get k hk).2
        have h2 := abs_add_le ((yf fl ex p w i).getD k 0) (m2v fl ex p w i k)
        linarith)
    have h2 := abs_add_le ((yf fl ex p w i).getD k 0) (m2v fl ex p w i k)
    have h3 := abs_sub_abs_le_abs_sub (fl ((yf fl ex p w i).getD k 0 + m2v fl ex p w i k))
      ((yf fl ex p w i).getD k 0 + m2v fl ex p w i k)
    have h4 := Xayp_ge2 k h7
    linarith
  · have h7' : 7 ≤ k := by omega
    have h1 := (y2_r ev (k - 6) (by omega) (by omega) i hi k (by omega)).2.2.1
    have h2 : Xayp.getD k 0 = 113 / 10 := by
      interval_cases k <;> norm_num [Xayp]
    linarith

/-! ## Block 3 -/

theorem hid3_len (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    (hid3 fl ex p w i).length = 3 := by
  unfold hid3
  rw [List.length_map, araffine_len]
  rfl

theorem hid3_getD (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i c : ℕ) (hc : c < 3) :
    (hid3 fl ex p w i).getD c 0 = Lane4.relu (fl (ardot fl (blk3.W1.getD c []) (y2f fl ex p w i)
      (p.W1 2 c) 0 0 + asw fl (blk3.b1.getD c 0) (p.b1 2 c))) := by
  unfold hid3
  rw [map_relu_getD, araffine_getD fl blk3.W1 blk3.b1 (y2f fl ex p w i) (p.W1 2) (p.b1 2) 0 c
    (by show c < 3; exact hc) (by show c < 3; exact hc), Nat.zero_add]

theorem pre3_err (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k0 : ℕ) (hk0 : k0 < 10)
    (s : ℚ) (hs : |(s : ℝ)| ≤ 1) (dW : ℕ → ℝ) (hdW : ∀ k, |dW k| ≤ 1 / 1000) (db : ℝ)
    (hdb : |db| ≤ 1 / 1000) :
    |ardot fl (unitRow 10 k0 s) (y2f fl ex p w i) dW 0 0 + asw fl (0 : ℚ) db
      - (s : ℝ) * (y2f fl ex p w i).getD k0 0| ≤ 46 / 1000 := by
  have hd := ev.dotA 10 (by norm_num) (unitRow 10 k0 s) (y2f fl ex p w i) Xayp dW 1 (113 / 10) 40
    (unitRow_len 10 k0 hk0 s) (y2_len ev i) Xayp_len hdW (unitRow_ok 10 k0 s 1 hs) (by norm_num)
    (by norm_num) (fun k hk => ⟨y2_abs ev i hi k hk, (Xayp_get k hk).2⟩) Xayp_sum (by norm_num)
  rw [dotQ_unitRow 10 k0 hk0 s _ (y2_len ev i)] at hd
  have hn : (1 : ℝ) / 1000 * 40 + ((10 : ℕ) : ℝ) * (1 + 1) * (113 / 10 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 44 / 1000 := by norm_num
  have hb := ev.aswz hdb
  have hh := le_trans hd hn
  obtain ⟨h1, h2⟩ := abs_le.mp hh
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

theorem hid3_fact (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c0 : ℕ) (hc0 : c0 < 3)
    (k0 : ℕ) (s : ℚ) (hk0 : k0 < 10) (hs : |(s : ℝ)| ≤ 1)
    (hrow : blk3.W1.getD c0 [] = unitRow 10 k0 s) :
    ∃ z : ℝ, (hid3 fl ex p w i).getD c0 0 = Lane4.relu (fl z) ∧
      |z - (s : ℝ) * (y2f fl ex p w i).getD k0 0| ≤ 46 / 1000 := by
  have hb : blk3.b1.getD c0 0 = 0 := by interval_cases c0 <;> rfl
  refine ⟨ardot fl (unitRow 10 k0 s) (y2f fl ex p w i) (p.W1 2 c0) 0 0
    + asw fl (0 : ℚ) (p.b1 2 c0), ?_, ?_⟩
  · rw [hid3_getD fl ex p w i c0 hc0, hrow, hb]
  · exact pre3_err ev i hi k0 hk0 s hs (p.W1 2 c0) (ev.hp.W1 2 c0) (p.b1 2 c0) (ev.hp.b1 2 c0)

theorem hid3_all (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) :
    |(hid3 fl ex p w i).getD 0 0 - Lane4.relu (-(y2f fl ex p w i).getD 7 0)| ≤ 47 / 1000 ∧
    |(hid3 fl ex p w i).getD 1 0 - Lane4.relu ((y2f fl ex p w i).getD 8 0)| ≤ 47 / 1000 ∧
    |(hid3 fl ex p w i).getD 2 0 - Lane4.relu ((y2f fl ex p w i).getD 9 0)| ≤ 47 / 1000 ∧
    ((y2f fl ex p w i).getD 8 0 ≤ -3 / 4 → (hid3 fl ex p w i).getD 1 0 = 0) ∧
    ((y2f fl ex p w i).getD 9 0 ≤ -3 / 4 → (hid3 fl ex p w i).getD 2 0 = 0) ∧
    (0 ≤ (hid3 fl ex p w i).getD 0 0 ∧ (hid3 fl ex p w i).getD 0 0 ≤ 1135 / 100) ∧
    (0 ≤ (hid3 fl ex p w i).getD 1 0 ∧ (hid3 fl ex p w i).getD 1 0 ≤ 430 / 100) ∧
    (0 ≤ (hid3 fl ex p w i).getD 2 0 ∧ (hid3 fl ex p w i).getD 2 0 ≤ 430 / 100) := by
  have r1 := y2_r ev 1 (by norm_num) (by norm_num) i hi 7 (by norm_num)
  have r2 := y2_r ev 2 (by norm_num) (by norm_num) i hi 8 (by norm_num)
  have r3 := y2_r ev 3 (by norm_num) (by norm_num) i hi 9 (by norm_num)
  obtain ⟨z0, hz0, ez0⟩ := hid3_fact ev i hi 0 (by norm_num) 7 (-1) (by norm_num) (by norm_num) rfl
  obtain ⟨z1, hz1, ez1⟩ := hid3_fact ev i hi 1 (by norm_num) 8 1 (by norm_num) (by norm_num) rfl
  obtain ⟨z2, hz2, ez2⟩ := hid3_fact ev i hi 2 (by norm_num) 9 1 (by norm_num) (by norm_num) rfl
  have e1 : (((-1 : ℚ)) : ℝ) = -1 := by norm_num
  have e2 : (((1 : ℚ)) : ℝ) = 1 := by norm_num
  rw [e1] at ez0
  rw [e2] at ez1 ez2
  obtain ⟨a7a, a7b⟩ := abs_le.mp r1.2.2.1
  obtain ⟨a8a, a8b⟩ := abs_le.mp r2.2.2.1
  obtain ⟨a9a, a9b⟩ := abs_le.mp r3.2.2.1
  have a7c := r1.2.2.2
  have a8c := r2.2.2.2
  have a9c := r3.2.2.2
  obtain ⟨u0a, u0b⟩ := abs_le.mp ez0
  obtain ⟨u1a, u1b⟩ := abs_le.mp ez1
  obtain ⟨u2a, u2b⟩ := abs_le.mp ez2
  have hM : (20 : ℝ) ≤ M := ev.range 20 (by norm_num)
  have fz0 := ev.flabs (x := z0) (by rw [abs_le]; constructor <;> linarith)
  have fz1 := ev.flabs (x := z1) (by rw [abs_le]; constructor <;> linarith)
  have fz2 := ev.flabs (x := z2) (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨g0a, g0b⟩ := abs_le.mp fz0
  obtain ⟨g1a, g1b⟩ := abs_le.mp fz1
  obtain ⟨g2a, g2b⟩ := abs_le.mp fz2
  rw [hz0, hz1, hz2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine le_trans (relu_lip _ _) ?_
    rw [abs_le]; constructor <;> linarith
  · refine le_trans (relu_lip _ _) ?_
    rw [abs_le]; constructor <;> linarith
  · refine le_trans (relu_lip _ _) ?_
    rw [abs_le]; constructor <;> linarith
  · intro hneg
    apply relu_fl_zero ev.hr
    · linarith
    · linarith
  · intro hneg
    apply relu_fl_zero ev.hr
    · linarith
    · linarith
  · unfold Lane4.relu; exact le_max_right _ _
  · unfold Lane4.relu; exact max_le (by linarith) (by norm_num)
  · unfold Lane4.relu; exact le_max_right _ _
  · unfold Lane4.relu; exact max_le (by linarith) (by norm_num)
  · unfold Lane4.relu; exact le_max_right _ _
  · unfold Lane4.relu; exact max_le (by linarith) (by norm_num)

theorem hid3_abs (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (c : ℕ) (hc : c < 3) :
    |(hid3 fl ex p w i).getD c 0| ≤ Xh.getD c 0 := by
  obtain ⟨-, -, -, -, -, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hid3_all ev i hi
  interval_cases c
  · rw [abs_of_nonneg a1]
    have e : Xh.getD 0 0 = 1135 / 100 := by norm_num [Xh]
    rw [e]; exact a2
  · rw [abs_of_nonneg b1]
    have e : Xh.getD 1 0 = 430 / 100 := by norm_num [Xh]
    rw [e]; exact b2
  · rw [abs_of_nonneg c1]
    have e : Xh.getD 2 0 = 430 / 100 := by norm_num [Xh]
    rw [e]; exact c2

noncomputable def m3v (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i k : ℕ) : ℝ :=
  fl (ardot fl (blk3.W2.getD k []) (hid3 fl ex p w i) (p.W2 2 k) 0 0 + asw fl 0 (p.b2 2 k))

theorem y3_len (ev : Ctx u η M fl ex p w) (i : ℕ) : (y3f fl ex p w i).length = 10 := by
  rw [y3f_eq]
  refine radd_len10 fl (y2_len ev i) ?_
  rw [araffine_len]
  rfl

theorem y3_getD (ev : Ctx u η M fl ex p w) (i k : ℕ) (hk : k < 10) :
    (y3f fl ex p w i).getD k 0 = fl ((y2f fl ex p w i).getD k 0 + m3v fl ex p w i k) := by
  have l0 := y2_len ev i
  have l1 : (araffine fl blk3.W2 blk3.b2 (hid3 fl ex p w i) (p.W2 2) (p.b2 2) 0).length = 10 := by
    rw [araffine_len]; rfl
  rw [y3f_eq, radd_getD fl (y2f fl ex p w i)
    (araffine fl blk3.W2 blk3.b2 (hid3 fl ex p w i) (p.W2 2) (p.b2 2) 0) k (by omega) (by omega),
    araffine_getD fl blk3.W2 blk3.b2 (hid3 fl ex p w i) (p.W2 2) (p.b2 2) 0 k
      (by show k < 10; exact hk) (by show k < (zrow 10).length; rw [zrow_len]; exact hk)]
  have hb : blk3.b2.getD k 0 = 0 := zrow_getD 10 k hk
  rw [hb, Nat.zero_add] <;> rfl

theorem m3_zero (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (k : ℕ) (hk : k < 10)
    (hne : k ≠ 7) : |m3v fl ex p w i k| ≤ 23 / 1000 := by
  have hrow : blk3.W2.getD k [] = zrow 3 := by
    interval_cases k <;> first | rfl | (exfalso; omega)
  unfold m3v
  rw [hrow]
  have hd := ev.dotA 3 (by norm_num) (zrow 3) (hid3 fl ex p w i) Xh (p.W2 2 k) 0 (1135 / 100)
    (2025 / 100) (zrow_len 3) (hid3_len fl ex p w i) Xh_len (ev.hp.W2 2 k)
    (zrow_ok 3 0 (le_refl _)) (le_refl _) (by norm_num)
    (fun c hc => ⟨hid3_abs ev i hi c hc, (Xh_get c hc).2⟩) Xh_sum (by norm_num)
  rw [dotQ_zrow, sub_zero] at hd
  have hn : (1 : ℝ) / 1000 * (2025 / 100) + ((3 : ℕ) : ℝ) * (0 + 1) * (1135 / 100 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 21 / 1000 := by norm_num
  have := ev.mfl (le_trans hd hn) (ev.hp.b2 2 k) (by norm_num)
  linarith

theorem y3_seven (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (hi1 : 1 ≤ i) :
    |(y3f fl ex p w i).getD 7 0 - 2 * ((target w i : ℕ) : ℝ)| ≤ 246 / 1000 := by
  have hk : (7 : ℕ) < 10 := by norm_num
  rw [y3_getD ev i 7 hk]
  have hT := target_le w i
  have hT0 : (0 : ℝ) ≤ ((target w i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT2 : ((target w i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hT
  have hrow : blk3.W2.getD 7 [] = [1, 1, 1] := rfl
  obtain ⟨e0, e1, e2, z1, z2, ⟨h0a, h0b⟩, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ := hid3_all ev i hi
  have r1 := y2_r ev 1 (by norm_num) (by norm_num) i hi 7 (by norm_num)
  have r2 := y2_r ev 2 (by norm_num) (by norm_num) i hi 8 (by norm_num)
  have r3 := y2_r ev 3 (by norm_num) (by norm_num) i hi 9 (by norm_num)
  have hd := ev.dotA 3 (by norm_num) [1, 1, 1] (hid3 fl ex p w i) Xh (p.W2 2 7) 1 (1135 / 100)
    (2025 / 100) rfl (hid3_len fl ex p w i) Xh_len (ev.hp.W2 2 7)
    (fun a ha => by
      first
        | (simp at ha; rw [ha]; norm_num)
        | (simp at ha; rcases ha with ha | ha | ha <;> (rw [ha]; norm_num)))
    (by norm_num) (by norm_num) (fun c hc => ⟨hid3_abs ev i hi c hc, (Xh_get c hc).2⟩) Xh_sum
    (by norm_num)
  have hsum : dotQ [1, 1, 1] (hid3 fl ex p w i) = (hid3 fl ex p w i).getD 0 0
      + (hid3 fl ex p w i).getD 1 0 + (hid3 fl ex p w i).getD 2 0 := by
    obtain ⟨a, b, c, hH⟩ : ∃ a b c : ℝ, hid3 fl ex p w i = [a, b, c] :=
      ⟨_, _, _, list3_eq _ (hid3_len fl ex p w i)⟩
    rw [hH]
    simp [dotQ, add_assoc]
  rw [hsum] at hd
  have hn : (1 : ℝ) / 1000 * (2025 / 100) + ((3 : ℕ) : ℝ) * (1 + 1) * (1135 / 100 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 22 / 1000 := by norm_num
  have hd2 := le_trans hd hn
  have hb := ev.aswz (ev.hp.b2 2 7)
  unfold m3v
  rw [hrow]
  obtain ⟨q1, q2⟩ := abs_le.mp hd2
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  -- the sum of the hidden units against the ideal
  have hsumT : |(y2f fl ex p w i).getD 7 0 + ((hid3 fl ex p w i).getD 0 0
      + (hid3 fl ex p w i).getD 1 0 + (hid3 fl ex p w i).getD 2 0)
      - 2 * ((target w i : ℕ) : ℝ)| ≤ 22 / 100 := by
    have ht := tok_pos ev i hi1 hi
    rcases (by omega : tokAt w i = 1 ∨ tokAt w i = 2 ∨ tokAt w i = 3) with hc | hc | hc
    · have hs := r1.1 hc
      have hz1' := z1 (r2.2.1 (by omega))
      have hz2' := z2 (r3.2.1 (by omega))
      have hl := relu_lip ((y2f fl ex p w i).getD 7 0) (2 * ((target w i : ℕ) : ℝ))
      have hr := Lane4.relu_sub_relu_neg ((y2f fl ex p w i).getD 7 0)
      have hT' : Lane4.relu (2 * ((target w i : ℕ) : ℝ)) = 2 * ((target w i : ℕ) : ℝ) := by
        unfold Lane4.relu; exact max_eq_left (by linarith)
      obtain ⟨s1, s2⟩ := abs_le.mp hs
      obtain ⟨l1, l2⟩ := abs_le.mp hl
      obtain ⟨p1, p2⟩ := abs_le.mp e0
      rw [hz1', hz2']
      rw [abs_le]; constructor <;> linarith
    · have hs := r2.1 hc
      have hn1 := r1.2.1 (by omega)
      have hz2' := z2 (r3.2.1 (by omega))
      have hl := relu_lip ((y2f fl ex p w i).getD 8 0) (2 * ((target w i : ℕ) : ℝ))
      have hT' : Lane4.relu (2 * ((target w i : ℕ) : ℝ)) = 2 * ((target w i : ℕ) : ℝ) := by
        unfold Lane4.relu; exact max_eq_left (by linarith)
      have hneg : Lane4.relu (-(y2f fl ex p w i).getD 7 0) = -(y2f fl ex p w i).getD 7 0 := by
        unfold Lane4.relu; exact max_eq_left (by linarith)
      obtain ⟨s1, s2⟩ := abs_le.mp hs
      obtain ⟨l1, l2⟩ := abs_le.mp hl
      obtain ⟨p1, p2⟩ := abs_le.mp e0
      obtain ⟨p3, p4⟩ := abs_le.mp e1
      rw [hneg] at p1 p2
      rw [hz2']
      rw [abs_le]; constructor <;> linarith
    · have hs := r3.1 hc
      have hn1 := r1.2.1 (by omega)
      have hz1' := z1 (r2.2.1 (by omega))
      have hl := relu_lip ((y2f fl ex p w i).getD 9 0) (2 * ((target w i : ℕ) : ℝ))
      have hT' : Lane4.relu (2 * ((target w i : ℕ) : ℝ)) = 2 * ((target w i : ℕ) : ℝ) := by
        unfold Lane4.relu; exact max_eq_left (by linarith)
      have hneg : Lane4.relu (-(y2f fl ex p w i).getD 7 0) = -(y2f fl ex p w i).getD 7 0 := by
        unfold Lane4.relu; exact max_eq_left (by linarith)
      obtain ⟨s1, s2⟩ := abs_le.mp hs
      obtain ⟨l1, l2⟩ := abs_le.mp hl
      obtain ⟨p1, p2⟩ := abs_le.mp e0
      obtain ⟨p5, p6⟩ := abs_le.mp e2
      rw [hneg] at p1 p2
      rw [hz1']
      rw [abs_le]; constructor <;> linarith
  have hx1 := ev.flnear (x := ardot fl [1, 1, 1] (hid3 fl ex p w i) (p.W2 2 7) 0 0
      + asw fl (0 : ℚ) (p.b2 2 7)) (t := (hid3 fl ex p w i).getD 0 0
      + (hid3 fl ex p w i).getD 1 0 + (hid3 fl ex p w i).getD 2 0) (e := 24 / 1000)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
  have hx2 := ev.flnear (x := (y2f fl ex p w i).getD 7 0 + fl (ardot fl [1, 1, 1]
      (hid3 fl ex p w i) (p.W2 2 7) 0 0 + asw fl (0 : ℚ) (p.b2 2 7)))
    (t := (y2f fl ex p w i).getD 7 0 + ((hid3 fl ex p w i).getD 0 0
      + (hid3 fl ex p w i).getD 1 0 + (hid3 fl ex p w i).getD 2 0)) (e := 25 / 1000)
    (by
      obtain ⟨c1, c2⟩ := abs_le.mp hx1
      rw [abs_le]; constructor <;> linarith)
    (by
      obtain ⟨c1, c2⟩ := abs_le.mp hx1
      obtain ⟨a7a, a7b⟩ := abs_le.mp r1.2.2.1
      rw [abs_le]; constructor <;> linarith)
  obtain ⟨c3, c4⟩ := abs_le.mp hx2
  obtain ⟨c5, c6⟩ := abs_le.mp hsumT
  rw [abs_le]
  constructor <;> linarith

theorem y3_abs (ev : Ctx u η M fl ex p w) (i : ℕ) (hi : i ≤ w.length) (hi1 : 1 ≤ i) (k : ℕ)
    (hk : k < 10) : |(y3f fl ex p w i).getD k 0| ≤ Xaypp.getD k 0 := by
  by_cases h7 : k = 7
  · subst h7
    have hs := y3_seven ev i hi hi1
    have hT := target_le w i
    have hT0 : (0 : ℝ) ≤ ((target w i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hT2 : ((target w i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hT
    have e : Xaypp.getD 7 0 = 1135 / 100 := by norm_num [Xaypp]
    rw [e]
    obtain ⟨s1, s2⟩ := abs_le.mp hs
    rw [abs_le]; constructor <;> linarith
  · rw [y3_getD ev i k hk]
    have hy := y2_abs ev i hi k hk
    have hm := m3_zero ev i hi k hk h7
    have h2 := abs_add_le ((y2f fl ex p w i).getD k 0) (m3v fl ex p w i k)
    have hg := Xaypp_ge k hk
    have hxb := (Xayp_get k hk).2
    have hflb := ev.flabs (x := (y2f fl ex p w i).getD k 0 + m3v fl ex p w i k)
      (by linarith)
    have h3 := abs_sub_abs_le_abs_sub (fl ((y2f fl ex p w i).getD k 0 + m3v fl ex p w i k))
      ((y2f fl ex p w i).getD k 0 + m3v fl ex p w i k)
    linarith

/-! ## The read-out -/

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  have hy3 := y3_seven ev i hi hi1
  have hT := target_le w i
  have hT0 : (0 : ℝ) ≤ ((target w i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT2 : ((target w i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hT
  have hw' : net.outW = unitRow 10 7 (1 / 2) := rfl
  have hb' : net.outB = 0 := rfl
  have hrun : net.run fl ex p w i = y3f fl ex p w i := rfl
  have hd := ev.dotA 10 (by norm_num) (unitRow 10 7 (1 / 2)) (y3f fl ex p w i) Xaypp p.oW
    (1 / 2) (1135 / 100) 41 (unitRow_len 10 7 (by norm_num) _) (y3_len ev i) Xaypp_len ev.hp.oW
    (unitRow_ok 10 7 (1 / 2) (1 / 2) (by norm_num)) (by norm_num) (by norm_num)
    (fun k hk => ⟨y3_abs ev i hi hi1 k hk, (Xaypp_get k hk).2⟩) Xaypp_sum (by norm_num)
  rw [dotQ_unitRow 10 7 (by norm_num) (1 / 2) _ (y3_len ev i)] at hd
  have e12 : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by norm_num
  rw [e12] at hd
  have hn : (1 : ℝ) / 1000 * 41 + ((10 : ℕ) : ℝ) * (1 / 2 + 1) * (1135 / 100 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 45 / 1000 := by norm_num
  have hb2 := ev.aswz ev.hp.oB
  unfold ANet.out
  rw [hrun, hw', hb']
  obtain ⟨d1, d2⟩ := abs_le.mp (le_trans hd hn)
  obtain ⟨b1, b2⟩ := abs_le.mp hb2
  obtain ⟨y1, y2⟩ := abs_le.mp hy3
  have hx : |ardot fl (unitRow 10 7 (1 / 2)) (y3f fl ex p w i) p.oW 0 0 + asw fl (0 : ℚ) p.oB
      - ((target w i : ℕ) : ℝ)| ≤ 170 / 1000 := by
    rw [abs_le]; constructor <;> linarith
  have hB : |ardot fl (unitRow 10 7 (1 / 2)) (y3f fl ex p w i) p.oW 0 0 + asw fl (0 : ℚ) p.oB|
      ≤ 100 := by
    rw [abs_le]; constructor <;> linarith
  have := ev.flnear hx hB
  linarith

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
