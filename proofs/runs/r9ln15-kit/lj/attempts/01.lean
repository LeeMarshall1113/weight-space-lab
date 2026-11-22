set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate Lane4.LN Lane4.R7KT Lane4.LNT
open Lane4.Seq (Mask cand tokAt)

theorem ln_scale_gen (fl : ℝ → ℝ) (s : ℝ) : ∀ (c : Vec) (g g' b b' : List ℚ)
    (dg dg' db db' : ℕ → ℝ) (k : ℕ), g.length = g'.length → b.length = b'.length →
    (∀ j, j < g.length → ((g.getD j 0 : ℚ) : ℝ) + dg (k + j) = ((g'.getD j 0 : ℚ) : ℝ) + dg' (k + j)) →
    (∀ j, j < b.length → ((b.getD j 0 : ℚ) : ℝ) + db (k + j) = ((b'.getD j 0 : ℚ) : ℝ) + db' (k + j)) →
    lnScale fl s c g b dg db k = lnScale fl s c g' b' dg' db' k := by
  intro c
  induction c with
  | nil =>
    intro g g' b b' dg dg' db db' k hg hb hgd hbd
    cases g <;> cases b <;> cases g' <;> cases b' <;> simp [lnScale]
  | cons x cs ih =>
    intro g g' b b' dg dg' db db' k hg hb hgd hbd
    cases g with
    | nil =>
      cases g' with
      | nil => cases b <;> cases b' <;> simp [lnScale]
      | cons a' g' => simp at hg
    | cons a g =>
      cases g' with
      | nil => simp at hg
      | cons a' g' =>
        cases b with
        | nil =>
          cases b' with
          | nil => simp [lnScale]
          | cons e' b' => simp at hb
        | cons e b =>
          cases b' with
          | nil => simp at hb
          | cons e' b' =>
            have h0 := kt_head_hyp hgd
            have h1 := kt_head_hyp hbd
            simp only [lnScale]
            rw [kt_asw_congr fl a a' (dg k) (dg' k) h0, kt_asw_congr fl e e' (db k) (db' k) h1,
              ih g g' b b' dg dg' db db' (k + 1) (by simpa using hg) (by simpa using hb)
                (kt_tail_hyp hgd) (kt_tail_hyp hbd)]

theorem lnorm_diff (fl sq : ℝ → ℝ) (g g' b b' : List ℚ) (hg : g.length = g'.length)
    (hb : b.length = b'.length) (x : Vec) :
    lnorm fl sq g b (dq g g') (dq b b') x = lnorm fl sq g' b' (fun _ => 0) (fun _ => 0) x := by
  unfold lnorm
  exact ln_scale_gen fl _ _ g g' b b' _ _ _ _ 0 hg hb (fun k _ => kt_dq_hyp g g' k)
    (fun k _ => kt_dq_hyp b b' k)

theorem diff_within_l : DiffWithinL := by
  intro W T δ hδ hs hn
  unfold sameShapeL at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨hsn, hg1⟩, hb1⟩, hg2⟩, hb2⟩, hgf⟩, hbf⟩ := hs
  unfold nearNetL at hn
  simp only [Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨nn, n1⟩, m1⟩, n2⟩, m2⟩, n3⟩, m3⟩ := hn
  exact
  { a := Lane4.R7KT.diff_within W.net T.net δ hδ hsn nn
    g1 := fun k => kt_nearL_abs hδ _ _ n1 hg1 k
    b1 := fun k => kt_nearL_abs hδ _ _ m1 hb1 k
    g2 := fun k => kt_nearL_abs hδ _ _ n2 hg2 k
    b2 := fun k => kt_nearL_abs hδ _ _ m2 hb2 k
    gf := fun k => kt_nearL_abs hδ _ _ n3 hgf k
    bf := fun k => kt_nearL_abs hδ _ _ m3 hbf k }

theorem out_shift_l : OutShiftL := by
  intro W T hs fl ex sq w i
  unfold sameShapeL at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨hsn, hg1⟩, hb1⟩, hg2⟩, hb2⟩, hgf⟩, hbf⟩ := hs
  obtain ⟨hE, hlen, hB, hout⟩ := kt_sameShape_parts W.net T.net hsn
  have hSB := hB 0
  have hinit : W.net.init fl (diffPL W T).a w = T.net.init fl zeroPL.a w :=
    kt_init_diff W.net T.net hE fl w
  have hhid : W.hid fl sq (diffPL W T) w = T.hid fl sq zeroPL w := by
    funext j
    unfold LNNet.hid
    rw [hinit]
    exact lnorm_diff fl sq W.g1 T.g1 W.b1 T.b1 hg1 hb1 _
  have hmid : LNNet.mid W (blk W.net 0) fl ex sq (diffPL W T) w i =
      LNNet.mid T (blk T.net 0) fl ex sq zeroPL w i := by
    unfold LNNet.mid
    rw [hhid, hinit]
    refine kt_aheadsApply_gen fl ex _ _ 0 (w.length + 1) _ i _ _ _ 0 hSB.1 ?_
    intro j hj
    simp only [Nat.zero_add]
    exact kt_attn_diff ((blk W.net 0).heads.getD j nilHead) ((blk T.net 0).heads.getD j nilHead)
      (hSB.2.1 j) fl ex _ _ i
  have hpost : ∀ y, LNNet.post W (blk W.net 0) fl sq (diffPL W T) y =
      LNNet.post T (blk T.net 0) fl sq zeroPL y := by
    intro y
    unfold LNNet.post
    have hl2 : lnorm fl sq W.g2 W.b2 (diffPL W T).g2 (diffPL W T).b2 y =
        lnorm fl sq T.g2 T.b2 zeroPL.g2 zeroPL.b2 y := lnorm_diff fl sq W.g2 T.g2 W.b2 T.b2 hg2 hb2 y
    rw [hl2]
    have h2 : ∀ Y, araffine fl (blk W.net 0).W1 (blk W.net 0).b1 Y ((diffPL W T).a.W1 0)
        ((diffPL W T).a.b1 0) 0 =
        araffine fl (blk T.net 0).W1 (blk T.net 0).b1 Y (zeroPL.a.W1 0) (zeroPL.a.b1 0) 0 := fun Y =>
      kt_araffine_gen fl _ _ _ _ Y _ _ _ _ 0 hSB.2.2.1.1 hSB.2.2.2.1 hSB.2.2.1.2
        (kt_mr_diff (blk W.net 0).W1 (blk T.net 0).W1)
        (fun k _ => kt_dq_hyp (blk W.net 0).b1 (blk T.net 0).b1 k)
    have h3 : ∀ Z, araffine fl (blk W.net 0).W2 (blk W.net 0).b2 Z ((diffPL W T).a.W2 0)
        ((diffPL W T).a.b2 0) 0 =
        araffine fl (blk T.net 0).W2 (blk T.net 0).b2 Z (zeroPL.a.W2 0) (zeroPL.a.b2 0) 0 := fun Z =>
      kt_araffine_gen fl _ _ _ _ Z _ _ _ _ 0 hSB.2.2.2.2.1.1 hSB.2.2.2.2.2 hSB.2.2.2.2.1.2
        (kt_mr_diff (blk W.net 0).W2 (blk T.net 0).W2)
        (fun k _ => kt_dq_hyp (blk W.net 0).b2 (blk T.net 0).b2 k)
    rw [h2, h3]
  have hread : ∀ z, LNNet.read W fl sq (diffPL W T) z = LNNet.read T fl sq zeroPL z := by
    intro z
    unfold LNNet.read
    have hl : lnorm fl sq W.gf W.bf (diffPL W T).gf (diffPL W T).bf z =
        lnorm fl sq T.gf T.bf zeroPL.gf zeroPL.bf z := lnorm_diff fl sq W.gf T.gf W.bf T.bf hgf hbf z
    rw [hl]
    rw [kt_ardot_gen fl _ _ _ (diffPL W T).a.oW zeroPL.a.oW 0 0 hout
        (fun k _ => kt_dq_hyp W.net.outW T.net.outW k),
      kt_asw_congr fl W.net.outB T.net.outB (diffPL W T).a.oB zeroPL.a.oB (by
        show (W.net.outB : ℝ) + ((T.net.outB - W.net.outB : ℚ) : ℝ) = (T.net.outB : ℝ) + 0
        push_cast
        ring)]
  have main : LNNet.read W fl sq (diffPL W T)
      (LNNet.post W (blk W.net 0) fl sq (diffPL W T)
        (LNNet.mid W (blk W.net 0) fl ex sq (diffPL W T) w i)) =
      LNNet.read T fl sq zeroPL
      (LNNet.post T (blk T.net 0) fl sq zeroPL
        (LNNet.mid T (blk T.net 0) fl ex sq zeroPL w i)) := by
    rw [hmid, hpost, hread]
  have hlen' := hlen
  unfold LNNet.out
  rcases hW : W.net.blocks with _ | ⟨B, _ | ⟨B2, Bs⟩⟩ <;>
    rcases hT : T.net.blocks with _ | ⟨B', _ | ⟨B2', Bs'⟩⟩
  all_goals first
    | (exfalso; rw [hW, hT] at hlen'; simp at hlen'; done)
    | skip
  all_goals first
    | (dsimp only; done)
    | skip
  all_goals first
    | (dsimp only; rfl)
    | skip
  all_goals
    have e : blk W.net 0 = B := by simp [blk, hW]
    have e' : blk T.net 0 = B' := by simp [blk, hT]
    rw [e, e'] at main
    exact main

end Lane4.Case
