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
      | nil => simp at hx
      | cons v x' =>
        have e : List.replicate 0 (0 : ℚ) ++ a :: List.replicate m 0 = a :: zrow m := rfl
        rw [e, dotQ_cons, dotQ_zrow]
        simp
  | k + 1, m, a, x, hx => by
      cases x with
      | nil => simp at hx
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

theorem dotA {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
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
  rw [zero_add] at h1 h2
  linarith

theorem Ctx.dotA (ev : Ctx u η M fl ex p w) (L : ℕ) (hL : L ≤ 32) (r : List ℚ) (x Xs : List ℝ)
    (d : ℕ → ℝ) (W Xm S : ℝ) (hrl : r.length = L) (hxl : x.length = L) (hXl : Xs.length = L)
    (hd : ∀ k, |d k| ≤ 1 / 1000) (hW : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (hXm0 : 0 ≤ Xm)
    (hb : ∀ k, k < L → |x.getD k 0| ≤ Xs.getD k 0 ∧ Xs.getD k 0 ≤ Xm)
    (hS : Xs.sum ≤ S) (hT : (W + 1) * (Xm + 0 + 1) ≤ 2 ^ 20) :
    |ardot fl r x d 0 0 - dotQ r x| ≤ 1 / 1000 * S + (L : ℝ) * (W + 1) * (Xm + 1) / 2 ^ 16 + 1 / 2 ^ 100 :=
  dotA ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (ev.range (2 ^ 30) (by norm_num)) L hL r x Xs d W Xm S
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
  interval_cases k <;> simp [xh0t, Xi0] <;> first | exact h1 | (split_ifs <;> norm_num)

theorem xh1t_abs (a b k : ℕ) (hk : k < 10) : |(xh1t a b).getD k 0| ≤ Xi1.getD k 0 := by
  have h1 := h_le2 a
  have h2 := h_nn a
  interval_cases k <;> simp [xh1t, Xi1] <;> first | exact h1 | (split_ifs <;> norm_num)

theorem Xa0_ge (k : ℕ) (hk : k < 10) : Xi0.getD k 0 + 11 / 10000 ≤ Xa0.getD k 0 := by
  interval_cases k <;> norm_num [Xi0, Xa0]
theorem Xa1_ge (k : ℕ) (hk : k < 10) : Xi1.getD k 0 + 17 / 1000 ≤ Xa1.getD k 0 := by
  interval_cases k <;> norm_num [Xi1, Xa1]
theorem Xay_ge (k : ℕ) (hk : k < 7) : Xi1.getD k 0 + 41 / 1000 ≤ Xay.getD k 0 := by
  interval_cases k <;> norm_num [Xi1, Xay]
theorem Xayp_ge (k : ℕ) (hk : k < 7) : Xi1.getD k 0 + 51 / 1000 ≤ Xayp.getD k 0 := by
  interval_cases k <;> norm_num [Xi1, Xayp]
theorem Xaypp_ge (k : ℕ) (hk : k < 7) :
    Xayp.getD k 0 + 23 / 1000 + 1 / 100000 ≤ Xaypp.getD k 0 := by
  interval_cases k <;> norm_num [Xayp, Xaypp]

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
      le_trans (abs_add_le _ _) (by linarith [abs_le.mp (hcnt k hk)])
    have hb : |H.bias fl dm i js + pdot fl (x i) (armat fl H.A (x js) dA 0) 0|
        ≤ 67 * ((w.length + 1 : ℕ) : ℝ) :=
      le_trans (abs_add_le _ _) (by linarith [abs_le.mp (hcnt js hjs)])
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

end Steps

end Lane4.Case
