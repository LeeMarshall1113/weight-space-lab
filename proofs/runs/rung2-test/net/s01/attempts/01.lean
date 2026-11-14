namespace Lane4.Case
open Lane4.Seq

def z : Vec := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def u1 : Vec := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def u12 : Vec := [1,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
def ub : Vec := [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
def uh : Vec := [0,0,1/2,0,0,0,0,0,0,0,0,0,0,0,0]
def un : Vec := [0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0]

def hd1 : Head :=
  { A := [z,z,z,z,z,z,z,z,z,z,z,z,z,z,z],
    V := [z,z,z,u1,u12,z,z,z,z,z,z,z,z,z,z],
    mask := Mask.all }
def hd2 : Head :=
  { A := [z,z,z,ub,z,z,z,z,z,z,z,z,z,uh,un],
    V := [z,z,z,z,z,ub,z,z,z,z,z,z,z,z,z],
    mask := Mask.all }
def hd3 : Head :=
  { A := [z,z,z,z,ub,z,z,z,z,z,z,z,z,uh,un],
    V := [z,z,z,z,z,z,ub,z,z,z,z,z,z,z,z],
    mask := Mask.all }

def w2rows : List Vec := [[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]]

def blk1 : Block := { heads := [hd1], W1 := [z], b1 := [0], W2 := w2rows, b2 := z }
def blk2 : Block := { heads := [hd2, hd3], W1 := [z], b1 := [0], W2 := w2rows, b2 := z }

def net : TNet :=
  { embed := [[0,0,1,0,0,0,0],[1,0,0,0,0,0,0],[0,1,0,0,0,0,0],[0,0,0,0,0,0,0]],
    blocks := [blk1, blk2],
    outW := [0,0,0,0,0,-1,-1,0,0,0,0,0,0,0,0],
    outB := 3 }

def g0 (x : ℕ) : ℚ := if x = 0 then 1 else 0
def g1 (x : ℕ) : ℚ := if x = 1 then 1 else 0
def g2 (x : ℕ) : ℚ := if x = 2 then 1 else 0
def g12 (x : ℕ) : ℚ := g1 x + g2 x
def fb (w : List ℕ) (k : ℕ) : ℚ := g0 (tokAt w k)

def cA (w : List ℕ) : ℕ := w.countP (fun s => decide (s < 2))
def cB (w : List ℕ) : ℕ := w.countP (fun s => decide (s < 3))

def S1 (w : List ℕ) : ℚ := avg (List.range (w.length + 1)) (fun k => g1 (tokAt w k))
def S2 (w : List ℕ) : ℚ := avg (List.range (w.length + 1)) (fun k => g12 (tokAt w k))

def XS (w : List ℕ) (j : ℕ) : Vec :=
  [g1 (tokAt w j), g2 (tokAt w j), g0 (tokAt w j), S1 w, S2 w, 0, 0] ++ pos j (w.length + 1)

def Q2 (w : List ℕ) (i : ℕ) : ℚ :=
  S1 w + 1 / 2 * (1 / ((w.length + 1 : ℕ) : ℚ)) - (i : ℚ) / ((w.length + 1 : ℕ) : ℚ)
def Q3 (w : List ℕ) (i : ℕ) : ℚ :=
  S2 w + 1 / 2 * (1 / ((w.length + 1 : ℕ) : ℚ)) - (i : ℚ) / ((w.length + 1 : ℕ) : ℚ)

/-! ### counting lemmas -/

theorem w4_sum_getD (g : ℕ → ℚ) (L : List ℕ) :
    ((List.range L.length).map (fun j => g (L.getD j 0))).sum = (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have hr : List.range (t.length + 1) = 0 :: (List.range t.length).map Nat.succ :=
      List.range_succ_eq_map t.length
    have e : (fun j => g ((a :: t).getD j 0)) ∘ Nat.succ = fun j => g (t.getD j 0) := by
      funext j
      simp
    rw [List.length_cons, hr, List.map_cons, List.sum_cons, List.map_map, e, ih]
    simp

theorem w4_sum_tok (g : ℕ → ℚ) (w : List ℕ) :
    ((List.range (w.length + 1)).map (fun j => g (tokAt w j))).sum = g 0 + (w.map g).sum := by
  have h := w4_sum_getD g (0 :: w)
  simpa [tokAt] using h

theorem w4_sum_map (w : List ℕ) (g : ℕ → ℚ) (p : ℕ → Bool)
    (h : ∀ x ∈ w, g x = if p x = true then 1 else 0) :
    (w.map g).sum = (w.countP p : ℚ) := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (by simp)
    rw [List.map_cons, List.sum_cons, List.countP_cons, ih', ha]
    by_cases hp : p a = true
    · simp [hp, add_comm]
    · simp [hp]

theorem w4_cp_eq (w : List ℕ) (p q : ℕ → Bool) (h : ∀ x ∈ w, p x = q x) :
    w.countP p = w.countP q := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (by simp)
    simp only [List.countP_cons]
    rw [ih', ha]

theorem w4_cp_le (w : List ℕ) (p q : ℕ → Bool) (h : ∀ x, p x = true → q x = true) :
    w.countP p ≤ w.countP q := by
  induction w with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    have h2 : (if p a = true then (1 : ℕ) else 0) ≤ (if q a = true then (1 : ℕ) else 0) := by
      by_cases hp : p a = true
      · simp [hp, h a hp]
      · simp [hp]
    exact Nat.add_le_add ih h2

theorem w4_cp_zero (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t) :
    w.countP (fun s => decide (s < 1)) = 0 := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have ha : ¬ a < 1 := by
      have := hw a (by simp)
      omega
    simp only [List.countP_cons, ih']
    simp [ha]

theorem w4_cp_len (w : List ℕ) (hw : ∀ t ∈ w, t ≤ 3) :
    w.countP (fun s => decide (s ≤ 3)) = w.length := by
  induction w with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have ha : a ≤ 3 := hw a (by simp)
    simp only [List.countP_cons, ih']
    simp [ha]

/-! ### the network's states -/

theorem init_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    net.init w j = [g1 (tokAt w j), g2 (tokAt w j), g0 (tokAt w j), 0, 0, 0, 0]
      ++ pos j (w.length + 1) := by
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 := by
    rcases tokAt_zero_or_mem w j with h | h
    · left; exact h
    · have := hw _ h
      omega
  rcases h3 with h | h | h | h <;> simp [TNet.init, net, g0, g1, g2, h]

theorem score1 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i k : ℕ) :
    hd1.score (net.init w i) (net.init w k) = 0 := by
  rw [init_eq w hw i, init_eq w hw k]
  simp [Head.score, hd1, z, qdot, matVec, pos]

theorem hd1_V : hd1.V = [z,z,z,u1,u12,z,z,z,z,z,z,z,z,z,z] := rfl
theorem hd2_V : hd2.V = [z,z,z,z,z,ub,z,z,z,z,z,z,z,z,z] := rfl
theorem hd3_V : hd3.V = [z,z,z,z,z,z,ub,z,z,z,z,z,z,z,z] := rfl

set_option maxHeartbeats 1600000 in
theorem x1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) :
    blk1.apply (w.length + 1) (net.init w) j = XS w j := by
  have hsel : hd1.sel (w.length + 1) (net.init w) j = List.range (w.length + 1) :=
    sel_all hd1 (w.length + 1) (net.init w) j
      (by intro k _ l _; rw [score1 w hw, score1 w hw])
  have hz : ∀ S : List ℕ, avg S (fun k => qdot z (net.init w k)) = 0 := by
    intro S
    have : (fun k => qdot z (net.init w k)) = fun _ => (0 : ℚ) := by
      funext k
      rw [init_eq w hw k]
      simp [qdot, z, pos]
    rw [this, avg_zero]
  have hu1 : avg (List.range (w.length + 1)) (fun k => qdot u1 (net.init w k)) = S1 w := by
    unfold S1
    congr 1
    funext k
    rw [init_eq w hw k]
    simp [qdot, u1, pos]
  have hu12 : avg (List.range (w.length + 1)) (fun k => qdot u12 (net.init w k)) = S2 w := by
    unfold S2
    congr 1
    funext k
    rw [init_eq w hw k]
    simp [qdot, u12, pos, g12]
  have h1 : hd1.attn (w.length + 1) (net.init w) j
      = [0,0,0,S1 w,S2 w,0,0,0,0,0,0,0,0,0,0] := by
    unfold Head.attn
    rw [hsel, hd1_V]
    simp only [List.map_cons, List.map_nil, hz, hu1, hu12]
  have hA : blk1.apply (w.length + 1) (net.init w) j
      = vadd (vadd (net.init w j) (hd1.attn (w.length + 1) (net.init w) j))
          (affine blk1.W2 blk1.b2
            ((affine blk1.W1 blk1.b1
              (vadd (net.init w j) (hd1.attn (w.length + 1) (net.init w) j))).map
                (fun v => max v 0))) := rfl
  rw [hA, h1, init_eq w hw j]
  simp [XS, vadd, affine, blk1, w2rows, z, pos]

set_option maxHeartbeats 1600000 in
theorem score2 (w : List ℕ) (i k : ℕ) :
    hd2.score (XS w i) (XS w k) = Q2 w i * fb w k := by
  simp [Head.score, hd2, XS, fb, z, ub, uh, un, qdot, matVec, pos, Q2] <;> ring

set_option maxHeartbeats 1600000 in
theorem score3 (w : List ℕ) (i k : ℕ) :
    hd3.score (XS w i) (XS w k) = Q3 w i * fb w k := by
  simp [Head.score, hd3, XS, fb, z, ub, uh, un, qdot, matVec, pos, Q3] <;> ring

theorem hz2 (w : List ℕ) : ∀ S : List ℕ, avg S (fun k => qdot z (XS w k)) = 0 := by
  intro S
  have : (fun k => qdot z (XS w k)) = fun _ => (0 : ℚ) := by
    funext k
    simp [XS, qdot, z, pos]
  rw [this, avg_zero]

theorem hub2 (w : List ℕ) : ∀ S : List ℕ, avg S (fun k => qdot ub (XS w k)) = avg S (fb w) := by
  intro S
  congr 1
  funext k
  simp [XS, qdot, ub, pos, fb]

theorem attn2 (w : List ℕ) (j : ℕ) :
    hd2.attn (w.length + 1) (XS w) j
      = [0,0,0,0,0,avg (hd2.sel (w.length + 1) (XS w) j) (fb w),0,0,0,0,0,0,0,0,0] := by
  unfold Head.attn
  rw [hd2_V]
  simp only [List.map_cons, List.map_nil, hz2 w, hub2 w]

theorem attn3 (w : List ℕ) (j : ℕ) :
    hd3.attn (w.length + 1) (XS w) j
      = [0,0,0,0,0,0,avg (hd3.sel (w.length + 1) (XS w) j) (fb w),0,0,0,0,0,0,0,0] := by
  unfold Head.attn
  rw [hd3_V]
  simp only [List.map_cons, List.map_nil, hz2 w, hub2 w]

set_option maxHeartbeats 1600000 in
theorem out_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) :
    net.out w i = 3 - avg (hd2.sel (w.length + 1) (XS w) i) (fb w)
      - avg (hd3.sel (w.length + 1) (XS w) i) (fb w) := by
  have hx1 : blk1.apply (w.length + 1) (net.init w) = XS w := funext (x1_eq w hw)
  have hrun : net.run w = blk2.apply (w.length + 1) (blk1.apply (w.length + 1) (net.init w)) := rfl
  rw [hx1] at hrun
  have hB : blk2.apply (w.length + 1) (XS w) i
      = vadd (vadd (vadd (XS w i) (hd2.attn (w.length + 1) (XS w) i))
            (hd3.attn (w.length + 1) (XS w) i))
          (affine blk2.W2 blk2.b2
            ((affine blk2.W1 blk2.b1
              (vadd (vadd (XS w i) (hd2.attn (w.length + 1) (XS w) i))
                (hd3.attn (w.length + 1) (XS w) i))).map (fun v => max v 0))) := rfl
  unfold TNet.out
  rw [hrun, hB, attn2 w i, attn3 w i]
  simp [XS, vadd, affine, blk2, w2rows, z, pos, qdot, net] <;> ring

/-! ### the selected sets -/

theorem w4_sel_val (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (h : Head)
    (hm : h.mask = Mask.all) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ w.length) (q : ℚ) (hq : q ≠ 0)
    (hs : ∀ k, h.score (XS w i) (XS w k) = q * fb w k) :
    avg (h.sel (w.length + 1) (XS w) i) (fb w) = if 0 < q then 1 else 0 := by
  have hc : ∀ k, k ∈ cand h.mask (w.length + 1) i ↔ k < w.length + 1 := by
    intro k
    rw [hm]
    exact mem_cand_all
  have fb0 : fb w 0 = 1 := by simp [fb, g0, tokAt_zero]
  have fbk : ∀ k, 1 ≤ k → k < w.length + 1 → fb w k = 0 := by
    intro k hk1 hk2
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hm' : m < w.length := by omega
    have ht := tokAt_succ w m hm'
    have hge := (hw w[m] (List.getElem_mem hm')).1
    simp [fb, g0, ht]
    omega
  have hcne : cand h.mask (w.length + 1) i ≠ [] := by
    intro hnil
    have h0 : 0 ∈ cand h.mask (w.length + 1) i := (hc 0).2 (by omega)
    rw [hnil] at h0
    simp at h0
  have hne : h.sel (w.length + 1) (XS w) i ≠ [] := sel_ne_nil h _ _ i hcne
  by_cases hpos : 0 < q
  · have hsel : h.sel (w.length + 1) (XS w) i = [0] := by
      apply sel_unique h _ _ i 0 ((hc 0).2 (by omega))
      intro k hk hk0
      rw [hs k, hs 0, fbk k (by omega) ((hc k).1 hk), fb0]
      linarith
    rw [hsel, avg_singleton, fb0, if_pos hpos]
  · have hneg : q < 0 := lt_of_le_of_ne (not_lt.1 hpos) hq
    have hall : ∀ k ∈ h.sel (w.length + 1) (XS w) i, fb w k = 0 := by
      intro k hk
      rw [mem_sel] at hk
      obtain ⟨hk1, hk2⟩ := hk
      by_cases hk0 : k = 0
      · exfalso
        subst hk0
        have h1 := hk2 1 ((hc 1).2 (by omega))
        rw [hs 1, hs 0, fbk 1 (le_refl 1) (by omega), fb0] at h1
        linarith
      · exact fbk k (by omega) ((hc k).1 hk1)
    rw [avg_const _ _ 0 hne hall, if_neg hpos]

theorem S1_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) :
    S1 w = (cA w : ℚ) / ((w.length + 1 : ℕ) : ℚ) := by
  have e1 : ((List.range (w.length + 1)).map (fun k => g1 (tokAt w k))).sum = (cA w : ℚ) := by
    rw [w4_sum_tok g1 w]
    have h0 : g1 0 = 0 := by simp [g1]
    have h2 := w4_sum_map w g1 (fun s => decide (s < 2)) (by
      intro x hx
      have h' := hw x hx
      have : x = 1 ∨ x = 2 ∨ x = 3 := by omega
      rcases this with rfl | rfl | rfl <;> simp [g1])
    rw [h0, h2]
    simp [cA]
  unfold S1 avg
  rw [e1, List.length_range]

theorem S2_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) :
    S2 w = (cB w : ℚ) / ((w.length + 1 : ℕ) : ℚ) := by
  have e1 : ((List.range (w.length + 1)).map (fun k => g12 (tokAt w k))).sum = (cB w : ℚ) := by
    rw [w4_sum_tok g12 w]
    have h0 : g12 0 = 0 := by simp [g12, g1, g2]
    have h2 := w4_sum_map w g12 (fun s => decide (s < 3)) (by
      intro x hx
      have h' := hw x hx
      have : x = 1 ∨ x = 2 ∨ x = 3 := by omega
      rcases this with rfl | rfl | rfl <;> simp [g12, g1, g2])
    rw [h0, h2]
    simp [cB]
  unfold S2 avg
  rw [e1, List.length_range]

theorem R2_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i ≤ w.length) :
    avg (hd2.sel (w.length + 1) (XS w) i) (fb w) = if i ≤ cA w then 1 else 0 := by
  have hN : (0 : ℚ) < ((w.length + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos _
  have hq : Q2 w i = ((cA w : ℚ) + 1 / 2 - (i : ℚ)) / ((w.length + 1 : ℕ) : ℚ) := by
    unfold Q2
    rw [S1_eq w hw]
    ring
  by_cases h : i ≤ cA w
  · have hle : (i : ℚ) ≤ (cA w : ℚ) := by exact_mod_cast h
    have hpos : 0 < Q2 w i := by
      rw [hq]
      refine div_pos ?_ hN
      linarith
    rw [w4_sel_val w hw hd2 rfl i hi1 hi2 (Q2 w i) hpos.ne' (score2 w i), if_pos hpos, if_pos h]
  · have h' : cA w + 1 ≤ i := by omega
    have hlt : (cA w : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast h'
    have hneg : Q2 w i < 0 := by
      rw [hq]
      refine div_neg_of_neg_of_pos ?_ hN
      linarith
    rw [w4_sel_val w hw hd2 rfl i hi1 hi2 (Q2 w i) hneg.ne (score2 w i),
      if_neg (not_lt.2 hneg.le), if_neg h]

theorem R3_eq (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i ≤ w.length) :
    avg (hd3.sel (w.length + 1) (XS w) i) (fb w) = if i ≤ cB w then 1 else 0 := by
  have hN : (0 : ℚ) < ((w.length + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos _
  have hq : Q3 w i = ((cB w : ℚ) + 1 / 2 - (i : ℚ)) / ((w.length + 1 : ℕ) : ℚ) := by
    unfold Q3
    rw [S2_eq w hw]
    ring
  by_cases h : i ≤ cB w
  · have hle : (i : ℚ) ≤ (cB w : ℚ) := by exact_mod_cast h
    have hpos : 0 < Q3 w i := by
      rw [hq]
      refine div_pos ?_ hN
      linarith
    rw [w4_sel_val w hw hd3 rfl i hi1 hi2 (Q3 w i) hpos.ne' (score3 w i), if_pos hpos, if_pos h]
  · have h' : cB w + 1 ≤ i := by omega
    have hlt : (cB w : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast h'
    have hneg : Q3 w i < 0 := by
      rw [hq]
      refine div_neg_of_neg_of_pos ?_ hN
      linarith
    rw [w4_sel_val w hw hd3 rfl i hi1 hi2 (Q3 w i) hneg.ne (score3 w i),
      if_neg (not_lt.2 hneg.le), if_neg h]

theorem net_correct : Statement net := by
  intro w hv i hi1 hi2
  have hw := hv.2
  have hout := out_eq w hw i
  have R2v := R2_eq w hw i hi1 hi2
  have R3v := R3_eq w hw i hi1 hi2
  have hab : cA w ≤ cB w := by
    unfold cA cB
    exact w4_cp_le w _ _ (by
      intro x hx
      simp only [decide_eq_true_eq] at hx ⊢
      omega)
  have hw1 : ∀ t ∈ w, 1 ≤ t := fun t ht => (hw t ht).1
  have hw3 : ∀ t ∈ w, t ≤ 3 := fun t ht => (hw t ht).2
  by_cases h1 : i ≤ cA w
  · refine ⟨1, ?_, ?_⟩
    · rw [hout, R2v, R3v, if_pos h1, if_pos (le_trans h1 hab)]
      norm_num
    · unfold IsRank
      refine ⟨?_, ?_⟩
      · rw [w4_cp_zero w hw1]
        omega
      · rw [w4_cp_eq w (fun s => decide (s ≤ 1)) (fun s => decide (s < 2))
          (fun x _ => by simp only [decide_eq_decide]; omega)]
        exact h1
  · by_cases h2 : i ≤ cB w
    · refine ⟨2, ?_, ?_⟩
      · rw [hout, R2v, R3v, if_neg h1, if_pos h2]
        norm_num
      · unfold IsRank
        refine ⟨?_, ?_⟩
        · have : cA w < i := by omega
          exact this
        · rw [w4_cp_eq w (fun s => decide (s ≤ 2)) (fun s => decide (s < 3))
            (fun x _ => by simp only [decide_eq_decide]; omega)]
          exact h2
    · refine ⟨3, ?_, ?_⟩
      · rw [hout, R2v, R3v, if_neg h1, if_neg h2]
        norm_num
      · unfold IsRank
        refine ⟨?_, ?_⟩
        · have : cB w < i := by omega
          exact this
        · rw [w4_cp_len w hw3]
          exact hi2

end Lane4.Case
