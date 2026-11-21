set_option linter.unusedVariables false

namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

abbrev kt_SR (M M' : List (List ℚ)) : Prop :=
  M.length = M'.length ∧ ∀ k, (M.getD k []).length = (M'.getD k []).length

abbrev kt_MR (M M' : List (List ℚ)) (d d' : ℕ → ℕ → ℝ) (i : ℕ) : Prop :=
  ∀ k, k < M.length → ∀ c, c < (M.getD k []).length →
    (((M.getD k []).getD c 0 : ℚ) : ℝ) + d (i + k) c
      = (((M'.getD k []).getD c 0 : ℚ) : ℝ) + d' (i + k) c

abbrev kt_SH (h k : AHead) : Prop :=
  kt_SR h.A k.A ∧ kt_SR h.V k.V ∧ h.mask = k.mask ∧ h.g.length = k.g.length

abbrev kt_SB (B C : ABlock) : Prop :=
  B.heads.length = C.heads.length ∧
  (∀ k, kt_SH (B.heads.getD k nilHead) (C.heads.getD k nilHead)) ∧
  kt_SR B.W1 C.W1 ∧ B.b1.length = C.b1.length ∧ kt_SR B.W2 C.W2 ∧ B.b2.length = C.b2.length

theorem kt_getD_oob {α : Type} (l : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    l.getD n d = d := by
  first
    | exact List.getD_eq_default l d h
    | simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem kt_SR_nil : kt_SR [] [] := ⟨rfl, fun k => by simp⟩

theorem kt_SH_nil : kt_SH nilHead nilHead := ⟨kt_SR_nil, kt_SR_nil, rfl, rfl⟩

theorem kt_SB_nil : kt_SB nilBlock nilBlock :=
  ⟨rfl, fun k => by
    show kt_SH (([] : List AHead).getD k nilHead) (([] : List AHead).getD k nilHead)
    rw [List.getD_nil]
    exact kt_SH_nil, kt_SR_nil, rfl, kt_SR_nil, rfl⟩

theorem kt_zw_all {α β : Type} (f : α → β → Bool) (da : α) (db : β) :
    ∀ (L : List α) (L' : List β), L.length = L'.length →
      (List.zipWith f L L').all id = true → ∀ k, k < L.length →
        f (L.getD k da) (L'.getD k db) = true
  | [], [], _, _, k, hk => by simp at hk
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | a :: L, b :: L', hl, h, k, hk => by
    have h2 : (f a b && (List.zipWith f L L').all id) = true := h
    simp only [Bool.and_eq_true] at h2
    cases k with
    | zero => simpa using h2.1
    | succ k =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact kt_zw_all f da db L L' (by simpa using hl) h2.2 k (by simpa using hk)

theorem kt_sameRows_sr : ∀ (A B : List (List ℚ)), sameRows A B = true → kt_SR A B
  | [], [], _ => ⟨rfl, fun k => by simp⟩
  | [], b :: B, h => by simp [sameRows] at h
  | a :: A, [], h => by simp [sameRows] at h
  | a :: A, b :: B, h => by
    have h2 : ((A.length + 1 == B.length + 1) &&
        ((a.length == b.length) &&
          ((List.zipWith (fun a b => a.length == b.length) A B).all id))) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨hl, hh, ht⟩ := h2
    have h' : sameRows A B = true := by
      unfold sameRows
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨by omega, ht⟩
    have ih := kt_sameRows_sr A B h'
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    intro k
    cases k with
    | zero => simpa using hh
    | succ k => simpa using ih.2 k

theorem kt_sameHead_sh (h k : AHead) (hh : sameHead h k = true) : kt_SH h k := by
  unfold sameHead at hh
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hh
  exact ⟨kt_sameRows_sr _ _ h1, kt_sameRows_sr _ _ h2, h3, h4⟩

theorem kt_sameBlock_sb (B C : ABlock) (hh : sameBlock B C = true) : kt_SB B C := by
  unfold sameBlock at hh
  simp only [Bool.and_eq_true, beq_iff_eq] at hh
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hh
  refine ⟨h1, ?_, kt_sameRows_sr _ _ h3, h4, kt_sameRows_sr _ _ h5, h6⟩
  intro k
  by_cases hk : k < B.heads.length
  · exact kt_sameHead_sh _ _ (kt_zw_all sameHead nilHead nilHead B.heads C.heads h1 h2 k hk)
  · rw [kt_getD_oob B.heads nilHead k (by omega), kt_getD_oob C.heads nilHead k (by omega)]
    exact kt_SH_nil

theorem kt_sameShape_parts (W T : ANet) (hs : sameShape W T = true) :
    kt_SR W.embed T.embed ∧ W.blocks.length = T.blocks.length ∧
      (∀ b, kt_SB (blk W b) (blk T b)) ∧ W.outW.length = T.outW.length := by
  unfold sameShape at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  refine ⟨kt_sameRows_sr _ _ h1, h2, ?_, h4⟩
  intro b
  by_cases hb : b < W.blocks.length
  · exact kt_sameBlock_sb _ _ (kt_zw_all sameBlock nilBlock nilBlock W.blocks T.blocks h2 h3 b hb)
  · have e1 : blk W b = nilBlock := kt_getD_oob W.blocks nilBlock b (by omega)
    have e2 : blk T b = nilBlock := kt_getD_oob T.blocks nilBlock b (by omega)
    rw [e1, e2]
    exact kt_SB_nil

/-! ### congruence lemmas -/

theorem kt_asw_congr (fl : ℝ → ℝ) (a a' : ℚ) (d d' : ℝ) (h : (a : ℝ) + d = (a' : ℝ) + d') :
    asw fl a d = asw fl a' d' := by
  unfold asw
  rw [h]

theorem kt_head_hyp {a a' : ℚ} {r r' : List ℚ} {d d' : ℕ → ℝ} {j : ℕ}
    (hd : ∀ k, k < (a :: r).length →
      (((a :: r).getD k 0 : ℚ) : ℝ) + d (j + k) = (((a' :: r').getD k 0 : ℚ) : ℝ) + d' (j + k)) :
    (a : ℝ) + d j = (a' : ℝ) + d' j := by
  have := hd 0 (by simp only [List.length_cons]; omega)
  simpa using this

theorem kt_tail_hyp {a a' : ℚ} {r r' : List ℚ} {d d' : ℕ → ℝ} {j : ℕ}
    (hd : ∀ k, k < (a :: r).length →
      (((a :: r).getD k 0 : ℚ) : ℝ) + d (j + k) = (((a' :: r').getD k 0 : ℚ) : ℝ) + d' (j + k)) :
    ∀ k, k < r.length →
      ((r.getD k 0 : ℚ) : ℝ) + d (j + 1 + k) = ((r'.getD k 0 : ℚ) : ℝ) + d' (j + 1 + k) := by
  intro k hk
  have := hd (k + 1) (by simp only [List.length_cons]; omega)
  simp only [List.getD_cons_succ] at this
  rw [show j + (k + 1) = j + 1 + k by omega] at this
  exact this

theorem kt_mr_head {r r' : List ℚ} {M M' : List (List ℚ)} {d d' : ℕ → ℕ → ℝ} {i : ℕ}
    (hm : kt_MR (r :: M) (r' :: M') d d' i) :
    ∀ k, k < r.length →
      ((r.getD k 0 : ℚ) : ℝ) + d i (0 + k) = ((r'.getD k 0 : ℚ) : ℝ) + d' i (0 + k) := by
  intro k hk
  have := hm 0 (by simp only [List.length_cons]; omega) k (by simpa using hk)
  simpa using this

theorem kt_mr_tail {r r' : List ℚ} {M M' : List (List ℚ)} {d d' : ℕ → ℕ → ℝ} {i : ℕ}
    (hm : kt_MR (r :: M) (r' :: M') d d' i) : kt_MR M M' d d' (i + 1) := by
  intro k hk c hc
  have := hm (k + 1) (by simp only [List.length_cons]; omega) c (by simpa using hc)
  simp only [List.getD_cons_succ] at this
  rw [show i + (k + 1) = i + 1 + k by omega] at this
  exact this

theorem kt_aswRow_gen (fl : ℝ → ℝ) : ∀ (r r' : List ℚ) (d d' : ℕ → ℝ) (j : ℕ),
    r.length = r'.length →
    (∀ k, k < r.length → ((r.getD k 0 : ℚ) : ℝ) + d (j + k) = ((r'.getD k 0 : ℚ) : ℝ) + d' (j + k)) →
    aswRow fl r d j = aswRow fl r' d' j
  | [], [], d, d', j, _, _ => rfl
  | [], _ :: _, d, d', j, hl, _ => by simp at hl
  | _ :: _, [], d, d', j, hl, _ => by simp at hl
  | a :: r, a' :: r', d, d', j, hl, hd => by
    have h0 := kt_head_hyp hd
    simp only [aswRow]
    rw [kt_asw_congr fl a a' (d j) (d' j) h0,
      kt_aswRow_gen fl r r' d d' (j + 1) (by simpa using hl) (kt_tail_hyp hd)]

theorem kt_ardot_gen (fl : ℝ → ℝ) : ∀ (r r' : List ℚ) (x : Vec) (d d' : ℕ → ℝ) (j : ℕ) (acc : ℝ),
    r.length = r'.length →
    (∀ k, k < r.length → ((r.getD k 0 : ℚ) : ℝ) + d (j + k) = ((r'.getD k 0 : ℚ) : ℝ) + d' (j + k)) →
    ardot fl r x d j acc = ardot fl r' x d' j acc
  | [], [], x, d, d', j, acc, _, _ => by first | rfl | simp [ardot]
  | [], _ :: _, x, d, d', j, acc, hl, _ => by simp at hl
  | _ :: _, [], x, d, d', j, acc, hl, _ => by simp at hl
  | a :: r, a' :: r', [], d, d', j, acc, hl, hd => by first | rfl | simp [ardot]
  | a :: r, a' :: r', v :: x, d, d', j, acc, hl, hd => by
    have h0 := kt_head_hyp hd
    simp only [ardot]
    rw [kt_asw_congr fl a a' (d j) (d' j) h0]
    exact kt_ardot_gen fl r r' x d d' (j + 1) _ (by simpa using hl) (kt_tail_hyp hd)

theorem kt_armat_gen (fl : ℝ → ℝ) : ∀ (M M' : List (List ℚ)) (x : Vec) (d d' : ℕ → ℕ → ℝ) (i : ℕ),
    M.length = M'.length → (∀ k, (M.getD k []).length = (M'.getD k []).length) →
    kt_MR M M' d d' i → armat fl M x d i = armat fl M' x d' i
  | [], [], x, d, d', i, _, _, _ => rfl
  | [], _ :: _, x, d, d', i, hl, _, _ => by simp at hl
  | _ :: _, [], x, d, d', i, hl, _, _ => by simp at hl
  | r :: M, r' :: M', x, d, d', i, hl, hr, hm => by
    have hr0 : r.length = r'.length := by simpa using hr 0
    simp only [armat]
    rw [kt_ardot_gen fl r r' x (d i) (d' i) 0 0 hr0 (kt_mr_head hm),
      kt_armat_gen fl M M' x d d' (i + 1) (by simpa using hl)
        (fun k => by simpa using hr (k + 1)) (kt_mr_tail hm)]

theorem kt_araffine_gen (fl : ℝ → ℝ) : ∀ (M M' : List (List ℚ)) (b b' : List ℚ) (x : Vec)
    (dW dW' : ℕ → ℕ → ℝ) (db db' : ℕ → ℝ) (i : ℕ),
    M.length = M'.length → b.length = b'.length →
    (∀ k, (M.getD k []).length = (M'.getD k []).length) →
    kt_MR M M' dW dW' i →
    (∀ k, k < b.length → ((b.getD k 0 : ℚ) : ℝ) + db (i + k) = ((b'.getD k 0 : ℚ) : ℝ) + db' (i + k)) →
    araffine fl M b x dW db i = araffine fl M' b' x dW' db' i := by
  intro M
  induction M with
  | nil =>
    intro M' b b' x dW dW' db db' i hl hb hr hm hbd
    cases M' with
    | nil => first | rfl | simp [araffine]
    | cons _ _ => simp at hl
  | cons r M ih =>
    intro M' b b' x dW dW' db db' i hl hb hr hm hbd
    cases M' with
    | nil => simp at hl
    | cons r' M' =>
      cases b with
      | nil =>
        cases b' with
        | nil => first | rfl | simp [araffine]
        | cons _ _ => simp at hb
      | cons c b =>
        cases b' with
        | nil => simp at hb
        | cons c' b' =>
          have hr0 : r.length = r'.length := by simpa using hr 0
          have hrow : ardot fl r x (dW i) 0 0 = ardot fl r' x (dW' i) 0 0 :=
            kt_ardot_gen fl r r' x (dW i) (dW' i) 0 0 hr0 (kt_mr_head hm)
          have hc : asw fl c (db i) = asw fl c' (db' i) :=
            kt_asw_congr fl c c' (db i) (db' i) (kt_head_hyp hbd)
          simp only [araffine]
          rw [hrow, hc]
          rw [ih M' b b' x dW dW' db db' (i + 1) (by simpa using hl) (by simpa using hb)
            (fun k => by simpa using hr (k + 1)) (kt_mr_tail hm)
            (by
              intro k hk
              have := hbd (k + 1) (by simp only [List.length_cons]; omega)
              simp only [List.getD_cons_succ] at this
              rw [show i + (k + 1) = i + 1 + k by omega] at this
              exact this)]

theorem kt_aattnRows_gen (fl ex : ℝ → ℝ) : ∀ (M M' : List (List ℚ)) (dV dV' : ℕ → ℕ → ℝ)
    (c c' : List ℕ) (s s' : ℕ → ℝ) (x : ℕ → Vec) (i : ℕ),
    M.length = M'.length → (∀ k, (M.getD k []).length = (M'.getD k []).length) →
    kt_MR M M' dV dV' i → c = c' → s = s' →
    aattnRows fl ex M dV c s x i = aattnRows fl ex M' dV' c' s' x i
  | [], [], dV, dV', c, c', s, s', x, i, _, _, _, hc, hs => by
    subst hc; subst hs; rfl
  | [], _ :: _, dV, dV', c, c', s, s', x, i, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], dV, dV', c, c', s, s', x, i, hl, _, _, _, _ => by simp at hl
  | r :: M, r' :: M', dV, dV', c, c', s, s', x, i, hl, hr, hm, hc, hs => by
    subst hc; subst hs
    have hr0 : r.length = r'.length := by simpa using hr 0
    simp only [aattnRows]
    have e : (fun j => ardot fl r (x j) (dV i) 0 0) = (fun j => ardot fl r' (x j) (dV' i) 0 0) :=
      funext fun j => kt_ardot_gen fl r r' (x j) (dV i) (dV' i) 0 0 hr0 (kt_mr_head hm)
    rw [e, kt_aattnRows_gen fl ex M M' dV dV' c c s s x (i + 1) (by simpa using hl)
      (fun k => by simpa using hr (k + 1)) (kt_mr_tail hm) rfl rfl]

theorem kt_attn_gen (fl ex : ℝ → ℝ) (h h' : AHead) (dA dA' dV dV' : ℕ → ℕ → ℝ) (dmm dmm' : ℝ)
    (dg dg' : ℕ → ℝ) (dgb dgb' : ℝ) (n : ℕ) (x : ℕ → Vec) (i : ℕ)
    (hs : kt_SH h h') (hA : kt_MR h.A h'.A dA dA' 0) (hV : kt_MR h.V h'.V dV dV' 0)
    (hm : (h.m : ℝ) + dmm = (h'.m : ℝ) + dmm')
    (hg : ∀ k, k < h.g.length →
      ((h.g.getD k 0 : ℚ) : ℝ) + dg (0 + k) = ((h'.g.getD k 0 : ℚ) : ℝ) + dg' (0 + k))
    (hgb : (h.gb : ℝ) + dgb = (h'.gb : ℝ) + dgb') :
    h.attn fl ex dA dV dmm dg dgb n x i = h'.attn fl ex dA' dV' dmm' dg' dgb' n x i := by
  have hgate : ∀ xj, h.gate fl dg dgb xj = h'.gate fl dg' dgb' xj := by
    intro xj
    unfold AHead.gate
    rw [kt_ardot_gen fl h.g h'.g xj dg dg' 0 0 hs.2.2.2 hg,
      kt_asw_congr fl h.gb h'.gb dgb dgb' hgb]
  have hc : h.cands fl dg dgb n x i = h'.cands fl dg' dgb' n x i := by
    unfold AHead.cands
    simp only [hgate, hs.2.2.1]
  have hbias : ∀ i j, h.bias fl dmm i j = h'.bias fl dmm' i j := by
    intro i j
    unfold AHead.bias
    rw [kt_asw_congr fl h.m h'.m dmm dmm' hm]
  have hsc : ∀ j, h.score fl dA dmm x i j = h'.score fl dA' dmm' x i j := by
    intro j
    unfold AHead.score
    rw [hbias, kt_armat_gen fl h.A h'.A (x j) dA dA' 0 hs.1.1 hs.1.2 hA]
  unfold AHead.attn
  exact kt_aattnRows_gen fl ex h.V h'.V dV dV' _ _ _ _ x 0 hs.2.1.1 hs.2.1.2 hV hc (funext hsc)

theorem kt_mr_diff (M M' : List (List ℚ)) : kt_MR M M' (dm M M') (fun _ _ => 0) 0 := by
  intro k _ c _
  simp only [dm, dq, Nat.zero_add]
  push_cast
  ring

theorem kt_dq_hyp (r r' : List ℚ) (k : ℕ) :
    ((r.getD k 0 : ℚ) : ℝ) + dq r r' (0 + k) = ((r'.getD k 0 : ℚ) : ℝ) + 0 := by
  simp only [dq, Nat.zero_add]
  push_cast
  ring

theorem kt_attn_diff (h h' : AHead) (hs : kt_SH h h') (fl ex : ℝ → ℝ) (n : ℕ) (x : ℕ → Vec)
    (i : ℕ) :
    h.attn fl ex (dm h.A h'.A) (dm h.V h'.V) (((h'.m - h.m : ℚ)) : ℝ) (dq h.g h'.g)
        (((h'.gb - h.gb : ℚ)) : ℝ) n x i =
      h'.attn fl ex (fun _ _ => 0) (fun _ _ => 0) 0 (fun _ => 0) 0 n x i :=
  kt_attn_gen fl ex h h' (dm h.A h'.A) (fun _ _ => 0) (dm h.V h'.V) (fun _ _ => 0)
    (((h'.m - h.m : ℚ)) : ℝ) 0 (dq h.g h'.g) (fun _ => 0) (((h'.gb - h.gb : ℚ)) : ℝ) 0
    n x i hs (kt_mr_diff _ _) (kt_mr_diff _ _) (by push_cast; ring)
    (fun k _ => kt_dq_hyp h.g h'.g k) (by push_cast; ring)

theorem kt_aheadsApply_gen (fl ex : ℝ → ℝ) (p p' : APert) (b n : ℕ) (x : ℕ → Vec) (i : ℕ) :
    ∀ (hs hs' : List AHead) (acc : Vec) (k : ℕ), hs.length = hs'.length →
    (∀ j, j < hs.length →
      (hs.getD j nilHead).attn fl ex (p.A b (k + j)) (p.V b (k + j)) (p.m b (k + j))
          (p.g b (k + j)) (p.gb b (k + j)) n x i =
        (hs'.getD j nilHead).attn fl ex (p'.A b (k + j)) (p'.V b (k + j)) (p'.m b (k + j))
          (p'.g b (k + j)) (p'.gb b (k + j)) n x i) →
    aheadsApply fl ex p b n x i hs acc k = aheadsApply fl ex p' b n x i hs' acc k
  | [], [], acc, k, _, _ => rfl
  | [], _ :: _, acc, k, hl, _ => by simp at hl
  | _ :: _, [], acc, k, hl, _ => by simp at hl
  | h :: hs, h' :: hs', acc, k, hl, H => by
    have h0 := H 0 (by simp only [List.length_cons]; omega)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    simp only [aheadsApply]
    rw [h0]
    refine kt_aheadsApply_gen fl ex p p' b n x i hs hs' _ (k + 1) (by simpa using hl) ?_
    intro j hj
    have := H (j + 1) (by simp only [List.length_cons]; omega)
    simp only [List.getD_cons_succ] at this
    rw [show k + (j + 1) = k + 1 + j by omega] at this
    exact this

theorem kt_block_eq (W T : ANet) (b : ℕ) (hSB : kt_SB (blk W b) (blk T b)) (fl ex : ℝ → ℝ)
    (n : ℕ) (x : ℕ → Vec) :
    ABlock.apply (blk W b) fl ex (diffP W T) b n x = ABlock.apply (blk T b) fl ex zeroP b n x := by
  funext i
  have h1 : aheadsApply fl ex (diffP W T) b n x i (blk W b).heads (x i) 0 =
      aheadsApply fl ex zeroP b n x i (blk T b).heads (x i) 0 := by
    refine kt_aheadsApply_gen fl ex (diffP W T) zeroP b n x i _ _ _ _ hSB.1 ?_
    intro j hj
    simp only [Nat.zero_add]
    exact kt_attn_diff ((blk W b).heads.getD j nilHead) ((blk T b).heads.getD j nilHead)
      (hSB.2.1 j) fl ex n x i
  have h2 : ∀ Y, araffine fl (blk W b).W1 (blk W b).b1 Y ((diffP W T).W1 b) ((diffP W T).b1 b) 0 =
      araffine fl (blk T b).W1 (blk T b).b1 Y (zeroP.W1 b) (zeroP.b1 b) 0 := fun Y =>
    kt_araffine_gen fl _ _ _ _ Y _ _ _ _ 0 hSB.2.2.1.1 hSB.2.2.2.1 hSB.2.2.1.2
      (kt_mr_diff (blk W b).W1 (blk T b).W1)
      (fun k _ => kt_dq_hyp (blk W b).b1 (blk T b).b1 k)
  have h3 : ∀ Z, araffine fl (blk W b).W2 (blk W b).b2 Z ((diffP W T).W2 b) ((diffP W T).b2 b) 0 =
      araffine fl (blk T b).W2 (blk T b).b2 Z (zeroP.W2 b) (zeroP.b2 b) 0 := fun Z =>
    kt_araffine_gen fl _ _ _ _ Z _ _ _ _ 0 hSB.2.2.2.2.1.1 hSB.2.2.2.2.2 hSB.2.2.2.2.1.2
      (kt_mr_diff (blk W b).W2 (blk T b).W2)
      (fun k _ => kt_dq_hyp (blk W b).b2 (blk T b).b2 k)
  simp only [ABlock.apply]
  rw [h1, h2, h3]

theorem kt_arunFrom_gen (fl ex : ℝ → ℝ) (p p' : APert) (n : ℕ) :
    ∀ (LW LT : List ABlock) (b : ℕ) (x : ℕ → Vec), LW.length = LT.length →
    (∀ k, k < LW.length → ∀ x', ABlock.apply (LW.getD k nilBlock) fl ex p (b + k) n x' =
        ABlock.apply (LT.getD k nilBlock) fl ex p' (b + k) n x') →
    arunFrom fl ex p n LW b x = arunFrom fl ex p' n LT b x
  | [], [], b, x, _, _ => rfl
  | [], _ :: _, b, x, hl, _ => by simp at hl
  | _ :: _, [], b, x, hl, _ => by simp at hl
  | B :: Bs, B' :: Bs', b, x, hl, H => by
    have h0 := H 0 (by simp only [List.length_cons]; omega)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    simp only [arunFrom]
    rw [h0 x]
    refine kt_arunFrom_gen fl ex p p' n Bs Bs' (b + 1) _ (by simpa using hl) ?_
    intro k hk x'
    have := H (k + 1) (by simp only [List.length_cons]; omega) x'
    simp only [List.getD_cons_succ] at this
    rw [show b + (k + 1) = b + 1 + k by omega] at this
    exact this

theorem kt_init_diff (W T : ANet) (hE : kt_SR W.embed T.embed) (fl : ℝ → ℝ) (w : List ℕ) :
    ANet.init W fl (diffP W T) w = ANet.init T fl zeroP w := by
  funext i
  simp only [ANet.init]
  exact kt_aswRow_gen fl _ _ _ _ 0 (hE.2 (tokAt w i))
    (fun k _ => kt_dq_hyp (W.embed.getD (tokAt w i) []) (T.embed.getD (tokAt w i) []) k)

theorem kt_run_diff (W T : ANet) (hs : sameShape W T = true) (fl ex : ℝ → ℝ) (w : List ℕ) :
    ANet.run W fl ex (diffP W T) w = ANet.run T fl ex zeroP w := by
  obtain ⟨hE, hlen, hB, hout⟩ := kt_sameShape_parts W T hs
  unfold ANet.run
  rw [kt_init_diff W T hE fl w]
  exact kt_arunFrom_gen fl ex (diffP W T) zeroP _ W.blocks T.blocks 0 _ hlen (fun k hk x' => by
    simp only [Nat.zero_add]
    exact kt_block_eq W T k (hB k) fl ex _ x')

theorem out_shift : OutShift := by
  intro W T hs fl ex w i
  obtain ⟨hE, hlen, hB, hout⟩ := kt_sameShape_parts W T hs
  have hrun := kt_run_diff W T hs fl ex w
  unfold ANet.out
  rw [hrun]
  rw [kt_ardot_gen fl W.outW T.outW (ANet.run T fl ex zeroP w i) (diffP W T).oW zeroP.oW 0 0 hout
      (fun k _ => kt_dq_hyp W.outW T.outW k),
    kt_asw_congr fl W.outB T.outB (diffP W T).oB zeroP.oB (by
      show (W.outB : ℝ) + ((T.outB - W.outB : ℚ) : ℝ) = (T.outB : ℝ) + 0
      push_cast
      ring)]

/-! ### DiffWithin -/

theorem kt_nearQ_abs {δ a b : ℚ} (h : nearQ δ a b = true) : |((b - a : ℚ) : ℝ)| ≤ (δ : ℝ) := by
  unfold nearQ at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : ((b - a : ℚ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h1
  have h2' : ((a - b : ℚ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h2
  rw [abs_le]
  push_cast at h1' h2' ⊢
  constructor <;> linarith

theorem kt_nearL_abs {δ : ℚ} (hδ : 0 ≤ δ) (a b : List ℚ) (h : nearL δ a b = true)
    (hl : a.length = b.length) (c : ℕ) : |dq a b c| ≤ (δ : ℝ) := by
  by_cases hc : c < a.length
  · have := kt_zw_all (nearQ δ) 0 0 a b hl h c hc
    exact kt_nearQ_abs this
  · unfold dq
    rw [kt_getD_oob a 0 c (by omega), kt_getD_oob b 0 c (by omega)]
    have : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
    simpa using this

theorem kt_nearM_abs {δ : ℚ} (hδ : 0 ≤ δ) (A B : List (List ℚ)) (h : nearM δ A B = true)
    (hs : kt_SR A B) (r c : ℕ) : |dm A B r c| ≤ (δ : ℝ) := by
  have hl := hs.1
  unfold dm
  by_cases hr : r < A.length
  · exact kt_nearL_abs hδ _ _ (kt_zw_all (nearL δ) [] [] A B hs.1 h r hr) (hs.2 r) c
  · rw [kt_getD_oob A [] r (by omega), kt_getD_oob B [] r (by omega)]
    exact kt_nearL_abs hδ [] [] (by first | rfl | simp [nearL]) rfl c

theorem kt_nearHead_parts {δ : ℚ} {h k : AHead} (hh : nearHead δ h k = true) :
    nearM δ h.A k.A = true ∧ nearM δ h.V k.V = true ∧ nearQ δ h.m k.m = true ∧
      nearL δ h.g k.g = true ∧ nearQ δ h.gb k.gb = true := by
  unfold nearHead at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := hh
  exact ⟨a, b, c, d, e⟩

theorem kt_nearBlock_parts {δ : ℚ} {B C : ABlock} (hh : nearBlock δ B C = true) :
    (List.zipWith (nearHead δ) B.heads C.heads).all id = true ∧ nearM δ B.W1 C.W1 = true ∧
      nearL δ B.b1 C.b1 = true ∧ nearM δ B.W2 C.W2 = true ∧ nearL δ B.b2 C.b2 = true := by
  unfold nearBlock at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := hh
  exact ⟨a, b, c, d, e⟩

theorem kt_nearHead_nil {δ : ℚ} (hδ : 0 ≤ δ) : nearHead δ nilHead nilHead = true := by
  simp [nearHead, nearM, nearL, nearQ, nilHead, hδ]

theorem kt_nearBlock_nil (δ : ℚ) : nearBlock δ nilBlock nilBlock = true := by
  first | rfl | simp [nearBlock, nearM, nearL, nilBlock]

theorem diff_within : DiffWithin := by
  intro W T δ hδ hs hn
  obtain ⟨hE, hlen, hB, hout⟩ := kt_sameShape_parts W T hs
  unfold nearNet at hn
  simp only [Bool.and_eq_true] at hn
  obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hn
  have nb : ∀ b, nearBlock δ (blk W b) (blk T b) = true := by
    intro b
    by_cases hb : b < W.blocks.length
    · exact kt_zw_all (nearBlock δ) nilBlock nilBlock W.blocks T.blocks hlen n2 b hb
    · have e1 : blk W b = nilBlock := kt_getD_oob W.blocks nilBlock b (by omega)
      have e2 : blk T b = nilBlock := kt_getD_oob T.blocks nilBlock b (by omega)
      rw [e1, e2]
      exact kt_nearBlock_nil δ
  have nh : ∀ b k, nearHead δ (hd W b k) (hd T b k) = true := by
    intro b k
    have hl := (hB b).1
    have hh := (kt_nearBlock_parts (nb b)).1
    by_cases hk : k < (blk W b).heads.length
    · exact kt_zw_all (nearHead δ) nilHead nilHead (blk W b).heads (blk T b).heads hl hh k hk
    · have e1 : hd W b k = nilHead := kt_getD_oob (blk W b).heads nilHead k (by omega)
      have e2 : hd T b k = nilHead := kt_getD_oob (blk T b).heads nilHead k (by omega)
      rw [e1, e2]
      exact kt_nearHead_nil hδ
  exact
  { E := fun t c => kt_nearM_abs hδ _ _ n1 hE t c
    A := fun b h r c => kt_nearM_abs hδ _ _ (kt_nearHead_parts (nh b h)).1 ((hB b).2.1 h).1 r c
    V := fun b h r c => kt_nearM_abs hδ _ _ (kt_nearHead_parts (nh b h)).2.1 ((hB b).2.1 h).2.1 r c
    m := fun b h => kt_nearQ_abs (kt_nearHead_parts (nh b h)).2.2.1
    g := fun b h c =>
      kt_nearL_abs hδ _ _ (kt_nearHead_parts (nh b h)).2.2.2.1 ((hB b).2.1 h).2.2.2 c
    gb := fun b h => kt_nearQ_abs (kt_nearHead_parts (nh b h)).2.2.2.2
    W1 := fun b r c => kt_nearM_abs hδ _ _ (kt_nearBlock_parts (nb b)).2.1 (hB b).2.2.1 r c
    b1 := fun b r => kt_nearL_abs hδ _ _ (kt_nearBlock_parts (nb b)).2.2.1 (hB b).2.2.2.1 r
    W2 := fun b r c => kt_nearM_abs hδ _ _ (kt_nearBlock_parts (nb b)).2.2.2.1 (hB b).2.2.2.2.1 r c
    b2 := fun b r => kt_nearL_abs hδ _ _ (kt_nearBlock_parts (nb b)).2.2.2.2 (hB b).2.2.2.2.2 r
    oW := fun c => kt_nearL_abs hδ _ _ n3 hout c
    oB := kt_nearQ_abs n4 }

end Lane4.Case
