/-
Lane 4, rung 7 kit module, assembled by tools/r7_assemble.py from kit case k5
(runs/r7-kit/k5): statements by the lane, proofs by a Sonnet doctor, checked by tools/check.py.
-/
import Lane4.R7B5

namespace Lane4.R7K5
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2

/-- The statement to prove is `Lane4.Cert.Sound` of R7Cert.lean, unchanged. -/
abbrev Goal : Prop := Lane4.Cert.Sound

end Lane4.R7K5


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Lane4.R7K5
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2

theorem mem_of_contains' {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : l.contains a = true) : a ∈ l := by
  first
  | exact List.contains_iff_mem.mp h
  | exact List.elem_iff.mp h
  | exact List.mem_of_elem_eq_true h
  | simpa using h

theorem check_open {δ : ℚ} {N : ANet} {T : Task} {c : Cert} (h : check δ N T c = true) :
    ∃ B : ABlock, N.blocks = [B] ∧ N.shapeOK T.ntok = true ∧ weightsOK N B = true ∧
      c.cands.length = B.heads.length ∧
      (List.zipWith (fun h cd => headOK δ (N.embed.map (embIV δ)) h cd) B.heads c.cands).all id = true ∧
      (∀ st ∈ c.states, st.2.length = B.heads.length) ∧
      absInit T c.cands ∈ c.states ∧
      (∀ st ∈ c.states, ∀ t, 1 ≤ t → t ≤ T.ntok →
         caseOK δ N B T c (N.embed.map (embIV δ)) st t = true) := by
  unfold check at h
  split at h
  · rename_i B hB
    refine ⟨B, hB, ?_⟩
    try dsimp only at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    refine ⟨h1, h2, beq_iff_eq.mp h3, h4, ?_, mem_of_contains' h6, ?_⟩
    · intro st hst
      exact beq_iff_eq.mp (List.all_eq_true.mp h5 st hst)
    · intro st hst t ht1 ht2
      have h' : caseOK δ N B T c (N.embed.map (embIV δ)) st (t - 1 + 1) = true :=
        List.all_eq_true.mp (List.all_eq_true.mp h7 st hst) (t - 1) (List.mem_range.mpr (by omega))
      have e : t - 1 + 1 = t := by omega
      rw [e] at h'
      exact h'
  · simp at h

theorem shape_facts {N : ANet} {ntok : ℕ} (h : N.shapeOK ntok = true) :
    ∃ d : ℕ, d ≤ 24 ∧ N.embed.length = ntok + 1 ∧ (∀ r ∈ N.embed, r.length = d) ∧
      (∀ B ∈ N.blocks, B.shapeOK d = true) ∧ N.outW.length = d := by
  unfold ANet.shapeOK at h
  split at h
  · simp at h
  · rename_i e es hE
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, rowsOK] at h
    obtain ⟨⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨e.length, h1, h2, h3, h5, h6⟩

theorem block_shape {B : ABlock} {d : ℕ} (h : B.shapeOK d = true) :
    B.heads.length ≤ 4 ∧ (∀ hd ∈ B.heads, hd.shapeOK d = true) ∧ B.b1.length ≤ 32 ∧
    B.W1.length = B.b1.length ∧ (∀ r ∈ B.W1, r.length = d) ∧
    B.W2.length = d ∧ (∀ r ∈ B.W2, r.length = B.b1.length) ∧ B.b2.length = d := by
  unfold ABlock.shapeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, rowsOK] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩⟩, ⟨h6, h7⟩⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem head_shape {hd : AHead} {d : ℕ} (h : hd.shapeOK d = true) :
    hd.A.length = d ∧ hd.V.length = d := by
  unfold AHead.shapeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, rowsOK] at h
  obtain ⟨⟨⟨hA, _⟩, ⟨hV, _⟩⟩, _⟩ := h
  exact ⟨hA, hV⟩

theorem weights_facts {N : ANet} {B : ABlock} (h : weightsOK N B = true) :
    smallM N.embed = true ∧ smallQ N.outW = true ∧ smallQ [N.outB] = true ∧
    smallM B.W1 = true ∧ smallQ B.b1 = true ∧ smallM B.W2 = true ∧ smallQ B.b2 = true ∧
    (∀ hd ∈ B.heads, smallM hd.A = true ∧ smallM hd.V = true ∧ smallQ hd.g = true ∧
      smallQ [hd.gb] = true) := by
  unfold weightsOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun hd hm => ?_⟩
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h8 hd hm
  exact ⟨a, b, c, d⟩

theorem headOK_mask {δ : ℚ} {E : List (List IV)} {hd : AHead} {cd : List Bool}
    (h : headOK δ E hd cd = true) : hd.mask ≠ Mask.all := by
  unfold headOK at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1.1.1.1.1

theorem caseOK_facts {δ : ℚ} {N : ANet} {B : ABlock} {T : Task} {c : Cert} {E : List (List IV)}
    {st : ℕ × List (Option ℕ)} {t : ℕ} (h : caseOK δ N B T c E st t = true) :
    outOK δ N B E c.cands t
      (List.zipWith (fun hc p => pickAt hc.1 hc.2 t p) (List.zip B.heads c.cands) st.2) = true ∧
    qabs ((outIV δ N B E c.cands t
      (List.zipWith (fun hc p => pickAt hc.1 hc.2 t p) (List.zip B.heads c.cands) st.2)).1
        - (T.out st.1 t : ℚ)) +
      (outIV δ N B E c.cands t
      (List.zipWith (fun hc p => pickAt hc.1 hc.2 t p) (List.zip B.heads c.cands) st.2)).2 ≤ 1 / 4 ∧
    absStep T c.cands st t ∈ c.states := by
  unfold caseOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, mem_of_contains' h3⟩

theorem outOK_facts {δ : ℚ} {N : ANet} {B : ABlock} {E : List (List IV)} {cds : List (List Bool)}
    {t : ℕ} {sel : List (Option ℕ)} (h : outOK δ N B E cds t sel = true) :
    headsOK δ E B.heads cds sel (E.getD t []) = true ∧
    (affIV δ B.W1 B.b1 (headsOut δ E B.heads cds sel (E.getD t []))).all small = true ∧
    (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 (headsOut δ E B.heads cds sel (E.getD t []))).map
      reluIV)).all small = true ∧
    (addIV (headsOut δ E B.heads cds sel (E.getD t []))
      (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 (headsOut δ E B.heads cds sel (E.getD t []))).map
        reluIV))).all small = true ∧
    small (outIV δ N B E cds t sel) = true := by
  unfold outOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem zipWith_all_getD {α β : Type} (f : α → β → Bool) (da : α) (db : β) :
    ∀ (l1 : List α) (l2 : List β), l2.length = l1.length →
    (List.zipWith f l1 l2).all id = true → ∀ a, a < l1.length →
      f (l1.getD a da) (l2.getD a db) = true
  | [], l2, _, _, a, ha => by simp at ha
  | x :: xs, [], hl, _, a, _ => by simp at hl
  | x :: xs, y :: ys, hl, hall, a, ha => by
      simp only [List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true, id_eq] at hall
      cases a with
      | zero => simpa using hall.1
      | succ a =>
        simp only [List.getD_cons_succ]
        exact zipWith_all_getD f da db xs ys (by simpa using hl) hall.2 a (by simpa using ha)

theorem addIV_length (a b : List IV) : (addIV a b).length = min a.length b.length := by
  simp [addIV]

theorem affIV_length (δ : ℚ) (M : List (List ℚ)) (b : List ℚ) (x : List IV) :
    (affIV δ M b x).length = min M.length b.length := by
  simp [affIV]

theorem headOut_length {δ : ℚ} {E : List (List IV)} {hd : AHead} {cd : List Bool}
    {q : Option ℕ} {d : ℕ} (hv : hd.V.length = d) : (headOut δ E hd cd q).length = d := by
  cases q <;> simp [headOut, matIV, valBound, hv]

theorem bdd15_16 {v : List IV} (h : Bdd 15 v) : Bdd 16 v :=
  fun a ha => ⟨(h a ha).1, by have := (h a ha).2; linarith⟩

def dfltHead : AHead := ⟨[], [], Mask.all, 0, [], 0⟩

def GoodHead (fl ex : ℝ → ℝ) (δ : ℚ) (E : List (List IV)) (p : APert) (n : ℕ) (x : ℕ → Vec)
    (i t d : ℕ) (a : ℕ) (hd : AHead) (cd : List Bool) (q : Option ℕ) : Prop :=
  hd.V.length = d ∧
  InIVs (hd.attn fl ex (p.A 0 a) (p.V 0 a) (p.m 0 a) (p.g 0 a) (p.gb 0 a) n x i)
    (headOut δ E hd cd (pickAt hd cd t q)) ∧
  ∀ v ∈ headOut δ E hd cd (pickAt hd cd t q), 0 ≤ v.2

theorem heads_ind {u η M : ℝ} {fl ex : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ}
    (E : List (List IV)) (p : APert) (n : ℕ) (x : ℕ → Vec) (i t d : ℕ) :
    ∀ (hs : List AHead) (cds : List (List Bool)) (sts : List (Option ℕ)) (k : ℕ)
      (acc : List ℝ) (accv : List IV),
      cds.length = hs.length → sts.length = hs.length → accv.length = d →
      InIVs acc accv → Bdd 16 accv →
      (∀ j, j < hs.length → GoodHead fl ex δ E p n x i t d (k + j) (hs.getD j dfltHead)
        (cds.getD j []) (sts.getD j none)) →
      headsOK δ E hs cds (List.zipWith (fun hc q => pickAt hc.1 hc.2 t q) (List.zip hs cds) sts)
        accv = true →
      InIVs (aheadsApply fl ex p 0 n x i hs acc k)
        (headsOut δ E hs cds (List.zipWith (fun hc q => pickAt hc.1 hc.2 t q) (List.zip hs cds) sts)
          accv) ∧
      Bdd 16 (headsOut δ E hs cds
        (List.zipWith (fun hc q => pickAt hc.1 hc.2 t q) (List.zip hs cds) sts) accv) ∧
      (headsOut δ E hs cds
        (List.zipWith (fun hc q => pickAt hc.1 hc.2 t q) (List.zip hs cds) sts) accv).length = d := by
  intro hs
  induction hs with
  | nil =>
    intro cds sts k acc accv _ _ hlen hin hb _ _
    exact ⟨hin, hb, hlen⟩
  | cons hd hs ih =>
    intro cds sts k acc accv hl1 hl2 hlen hin hb hg hok
    cases cds with
    | nil => simp at hl1
    | cons cd cds =>
      cases sts with
      | nil => simp at hl2
      | cons q sts =>
        have g0 := hg 0 (Nat.succ_pos _)
        simp only [List.getD_cons_zero, Nat.add_zero] at g0
        obtain ⟨hV, hattn, hnn⟩ := g0
        have hok' : ((addIV accv (headOut δ E hd cd (pickAt hd cd t q))).all small &&
            headsOK δ E hs cds
              (List.zipWith (fun hc q => pickAt hc.1 hc.2 t q) (List.zip hs cds) sts)
              (addIV accv (headOut δ E hd cd (pickAt hd cd t q)))) = true := hok
        rw [Bool.and_eq_true] at hok'
        obtain ⟨hsm, hrest⟩ := hok'
        obtain ⟨hin', hb15⟩ := add_sound u η M fl hC acc _ accv _ hin hattn
          (fun v hv => (hb v hv).1) hnn hsm
        have hlen' : (addIV accv (headOut δ E hd cd (pickAt hd cd t q))).length = d := by
          rw [addIV_length, hlen, headOut_length hV, min_self]
        have hg' : ∀ j, j < hs.length → GoodHead fl ex δ E p n x i t d (k + 1 + j)
            (hs.getD j dfltHead) (cds.getD j []) (sts.getD j none) := by
          intro j hj
          have := hg (j + 1) (by simp only [List.length_cons]; omega)
          simp only [List.getD_cons_succ] at this
          rwa [show k + (j + 1) = k + 1 + j by omega] at this
        exact ih cds sts (k + 1) _ _ (by simpa using hl1) (by simpa using hl2) hlen' hin'
          (bdd15_16 hb15) hg' hrest

def outIVy (δ : ℚ) (N : ANet) (B : ABlock) (y : List IV) : IV :=
  let z := addIV y (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 y).map reluIV))
  ((dotIV δ N.outW z).1 + N.outB, (dotIV δ N.outW z).2 + e0 δ + rnd)

theorem mlp_readout {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2)
    {N : ANet} {B : ABlock} {d : ℕ} (hd24 : d ≤ 24) (hb1l : B.b1.length ≤ 32)
    (hW1l : B.W1.length = B.b1.length) (hW1r : ∀ r ∈ B.W1, r.length = d)
    (hW2l : B.W2.length = d) (hW2r : ∀ r ∈ B.W2, r.length = B.b1.length) (hb2l : B.b2.length = d)
    (houtW : N.outW.length = d) (wOut : smallQ N.outW = true) (wOutB : smallQ [N.outB] = true)
    (wW1 : smallM B.W1 = true) (wb1 : smallQ B.b1 = true) (wW2 : smallM B.W2 = true)
    (wb2 : smallQ B.b2 = true) {p : APert} (hp : p.Within (δ : ℝ))
    (y : List ℝ) (yv : List IV) (hyIn : InIVs y yv) (hyB : Bdd 16 yv) (hylen : yv.length = d)
    (ha1 : (affIV δ B.W1 B.b1 yv).all small = true)
    (ha2 : (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 yv).map reluIV)).all small = true)
    (hadd : (addIV yv (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 yv).map reluIV))).all small = true)
    (hsm : small (outIVy δ N B yv) = true) :
    InIV (fl (ardot fl N.outW (radd fl y (araffine fl B.W2 B.b2
        ((araffine fl B.W1 B.b1 y (p.W1 0) (p.b1 0) 0).map Lane4.relu) (p.W2 0) (p.b2 0) 0))
        p.oW 0 0 + asw fl N.outB p.oB)) (outIVy δ N B yv) := by
  have hylen' : y.length = d := by rw [hyIn.1, hylen]
  obtain ⟨h1a, h1b⟩ := aff_sound u η M fl hC δ hδ0 hδ1 B.W1 B.b1 y yv (p.W1 0) (p.b1 0)
    (hp.W1 0) (hp.b1 0) (fun r hr => by rw [hW1r r hr, hylen']) (by omega) wW1 wb1 hyIn hyB ha1
  obtain ⟨h2a, h2b⟩ := relu_sound _ _ h1a h1b
  obtain ⟨h3a, h3b⟩ := aff_sound u η M fl hC δ hδ0 hδ1 B.W2 B.b2 _ _ (p.W2 0) (p.b2 0)
    (hp.W2 0) (hp.b2 0)
    (fun r hr => by rw [hW2r r hr, h2a.1, List.length_map, affIV_length, hW1l, min_self])
    (by rw [h2a.1, List.length_map, affIV_length, hW1l, min_self]; exact hb1l)
    wW2 wb2 h2a (bdd15_16 h2b) ha2
  have a2len : (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 yv).map reluIV)).length = d := by
    rw [affIV_length, hW2l, hb2l, min_self]
  obtain ⟨h4a, h4b⟩ := add_sound u η M fl hC y _ yv _ hyIn h3a (fun v hv => (hyB v hv).1)
    (fun v hv => (h3b v hv).1) hadd
  have haff : affIV δ [N.outW] [N.outB]
      (addIV yv (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 yv).map reluIV))) = [outIVy δ N B yv] := rfl
  have hsm' : (affIV δ [N.outW] [N.outB]
      (addIV yv (affIV δ B.W2 B.b2 ((affIV δ B.W1 B.b1 yv).map reluIV)))).all small = true := by
    rw [haff]; simpa using hsm
  obtain ⟨⟨hl5, hk5⟩, _⟩ := aff_sound u η M fl hC δ hδ0 hδ1 [N.outW] [N.outB] _ _
    (fun _ => p.oW) (fun _ => p.oB) (fun i k => hp.oW k) (fun i => hp.oB)
    (fun r hr => by
      rw [List.mem_singleton.mp hr, houtW, h4a.1, addIV_length, hylen, a2len, min_self])
    (by rw [h4a.1, addIV_length, hylen, a2len, min_self]; exact hd24.trans (by norm_num))
    (by simp [smallM, wOut]) wOutB h4a (bdd15_16 h4b) hsm'
  have e : araffine fl [N.outW] [N.outB] (radd fl y (araffine fl B.W2 B.b2
        ((araffine fl B.W1 B.b1 y (p.W1 0) (p.b1 0) 0).map Lane4.relu) (p.W2 0) (p.b2 0) 0))
        (fun _ => p.oW) (fun _ => p.oB) 0 =
      [fl (ardot fl N.outW (radd fl y (araffine fl B.W2 B.b2
        ((araffine fl B.W1 B.b1 y (p.W1 0) (p.b1 0) 0).map Lane4.relu) (p.W2 0) (p.b2 0) 0))
        p.oW 0 0 + asw fl N.outB p.oB)] := rfl
  have hk0 := hk5 0 (by rw [e]; simp)
  rw [e, haff] at hk0
  simpa using hk0

theorem sound_core {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) {N : ANet} {T : Task} {c : Cert}
    (hchk : check δ N T c = true) {u η M : ℝ} {fl ex : ℝ → ℝ} (hC : Ctx u η M fl)
    (hX : ExpM u η ex)
    {p : APert} (hp : p.Within (δ : ℝ)) {w : List ℕ} (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ T.ntok)
    (hu : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100)
    (hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ w.length) :
    |N.out fl ex p w i - ((T.target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨B, hB, hshape, hweights, hcl, hzip, hslen, hinit, hcase⟩ := check_open hchk
  obtain ⟨d, hd24, hembl, hembrows, hblocks, houtW⟩ := shape_facts hshape
  have hBshape : B.shapeOK d = true := hblocks B (by rw [hB]; simp)
  obtain ⟨hhl4, hheadsh, hb1l, hW1l, hW1r, hW2l, hW2r, hb2l⟩ := block_shape hBshape
  obtain ⟨wEmb, wOut, wOutB, wW1, wb1, wW2, wb2, wHeads⟩ := weights_facts hweights
  generalize hE : N.embed.map (embIV δ) = E at hzip hcase
  have hEl : E.length = T.ntok + 1 := by rw [← hE, List.length_map, hembl]
  have hdbd : ∀ k : ℕ, |(fun _ : ℕ => (0 : ℝ)) k| ≤ (δ : ℝ) := fun k => by
    simp only [abs_zero]; exact Rat.cast_nonneg.mpr hδ0
  have hrows : ∀ row ∈ E, row.length = d ∧ Bdd 16 row := by
    intro row hrow
    rw [← hE] at hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    exact ⟨by simp [embIV, hembrows r hr],
      (emb_sound u η M fl hC δ hδ0 hδ1 r (fun _ => 0) hdbd (zsmallM_mem wEmb r hr)).2⟩
  have htok : ∀ j, tokAt w j = 0 ∨ tokAt w j ∈ w := Lane4.Seq.tokAt_zero_or_mem w
  have htokle : ∀ j, tokAt w j ≤ T.ntok := by
    intro j
    rcases htok j with h | h
    · rw [h]; exact Nat.zero_le _
    · exact (hw _ h).2
  have hxE : ∀ j, j < w.length + 1 →
      tokAt w j < E.length ∧ InIVs (N.init fl p w j) (E.getD (tokAt w j) []) := by
    intro j _
    have hlt : tokAt w j < N.embed.length := by have := htokle j; omega
    refine ⟨by rw [hEl]; have := htokle j; omega, ?_⟩
    have hget : E.getD (tokAt w j) [] = embIV δ (N.embed.getD (tokAt w j) []) := by
      rw [← hE]; exact zgetD_map'' (embIV δ) [] [] rfl N.embed _ hlt
    rw [hget]
    exact (emb_sound u η M fl hC δ hδ0 hδ1 _ (p.E (tokAt w j)) (fun k => hp.E _ k)
      (zsmallM_mem wEmb _ (zgetD_mem' [] N.embed _ hlt))).1
  have hrun : N.run fl ex p w = B.apply fl ex p 0 (w.length + 1) (N.init fl p w) := by
    unfold ANet.run; rw [hB]; rfl
  have hpre : ∀ t ∈ w.take (i - 1), 1 ≤ t ∧ t ≤ T.ntok :=
    fun t ht => hw t (List.mem_of_mem_take ht)
  have hstate : absState T c.cands (w.take (i - 1)) ∈ c.states :=
    Lane4.R7K4.abs_closed T c.cands c.states hinit
      (fun st hst t h1 h2 => (caseOK_facts (hcase st hst t h1 h2)).2.2) _ hpre
  have htarget := Lane4.R7K4.abs_target T c.cands w i hi1 hi2
  have hslen' := hslen _ hstate
  generalize hst : absState T c.cands (w.take (i - 1)) = st at hstate htarget hslen'
  have hti : tokAt w i ∈ w := by
    have h1 := Lane4.Seq.tokAt_succ w (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at h1
    rw [h1]; exact List.getElem_mem _
  have hti1 := (hw _ hti).1
  have hti2 := (hw _ hti).2
  obtain ⟨hOK, hbound, _⟩ := caseOK_facts (hcase st hstate (tokAt w i) hti1 hti2)
  generalize hsel : List.zipWith (fun hc p => pickAt hc.1 hc.2 (tokAt w i) p)
    (List.zip B.heads c.cands) st.2 = sel at hOK hbound
  obtain ⟨hHok, ha1, ha2, hadd, hsm⟩ := outOK_facts hOK
  obtain ⟨hlt_i, hxi⟩ := hxE i (by omega)
  have hrow_t := hrows _ (zgetD_mem' [] E _ hlt_i)
  have hgood : ∀ a, a < B.heads.length → GoodHead fl ex δ E p (w.length + 1) (N.init fl p w) i
      (tokAt w i) d a (B.heads.getD a dfltHead) (c.cands.getD a []) (st.2.getD a none) := by
    intro a ha
    have hmem : B.heads.getD a dfltHead ∈ B.heads := zgetD_mem' dfltHead B.heads a ha
    have hOKhd : headOK δ E (B.heads.getD a dfltHead) (c.cands.getD a []) = true :=
      zipWith_all_getD _ dfltHead [] B.heads c.cands hcl hzip a ha
    generalize B.heads.getD a dfltHead = hd at hmem hOKhd ⊢
    have hshd := hheadsh hd hmem
    obtain ⟨wA, wV, wg, wgb⟩ := wHeads hd hmem
    have hne : hd.mask ≠ Mask.all := headOK_mask hOKhd
    obtain ⟨hs1, hs2, hs3⟩ := Lane4.R7K3.head_sound u η M fl ex hC hX δ hδ0 hδ1 hd E
      (c.cands.getD a []) d hOKhd hshd hd24 wA wV wg wgb hrows
      (p.A 0 a) (p.V 0 a) (p.m 0 a) (p.g 0 a) (p.gb 0 a)
      (hp.A 0 a) (hp.V 0 a) (hp.m 0 a) (hp.g 0 a) (hp.gb 0 a)
      (w.length + 1) (N.init fl p w) (tokAt w) hu hη hM (fun j hj => hxE j hj) i (by omega) hti1
    obtain ⟨hp1, hp2⟩ := Lane4.R7K4.abs_pick T c.cands w i a hd hi1 hi2 (by omega) hne
    rw [hst] at hp1 hp2
    refine ⟨(head_shape hshd).2, ?_, hs3 _⟩
    suffices H : ∀ q, pickAt hd (c.cands.getD a []) (tokAt w i) (st.2.getD a none) = q →
        InIVs (hd.attn fl ex (p.A 0 a) (p.V 0 a) (p.m 0 a) (p.g 0 a) (p.gb 0 a) (w.length + 1)
          (N.init fl p w) i) (headOut δ E hd (c.cands.getD a []) q) from H _ rfl
    intro q hq
    cases q with
    | none => exact hs2 (hp1 hq)
    | some t' =>
      obtain ⟨j, hj, hjt⟩ := hp2 t' hq
      subst hjt
      exact hs1 j hj
  have hres := heads_ind hC E p (w.length + 1) (N.init fl p w) i (tokAt w i) d B.heads c.cands
    st.2 0 (N.init fl p w i) (E.getD (tokAt w i) []) hcl hslen' hrow_t.1 hxi hrow_t.2
    (fun j hj => by rw [Nat.zero_add]; exact hgood j hj) (by rw [hsel]; exact hHok)
  rw [hsel] at hres
  obtain ⟨hyIn, hyB, hylen⟩ := hres
  have hmlp := mlp_readout hC hδ0 hδ1 (N := N) (B := B) hd24 hb1l hW1l hW1r hW2l hW2r hb2l houtW
    wOut wOutB wW1 wb1 wW2 wb2 hp _ _ hyIn hyB hylen ha1 ha2 hadd hsm
  have hIn : InIV (N.out fl ex p w i) (outIV δ N B E c.cands (tokAt w i) sel) := by
    have e : N.out fl ex p w i = fl (ardot fl N.outW (radd fl
        (aheadsApply fl ex p 0 (w.length + 1) (N.init fl p w) i B.heads (N.init fl p w i) 0)
        (araffine fl B.W2 B.b2 ((araffine fl B.W1 B.b1
          (aheadsApply fl ex p 0 (w.length + 1) (N.init fl p w) i B.heads (N.init fl p w i) 0)
          (p.W1 0) (p.b1 0) 0).map Lane4.relu) (p.W2 0) (p.b2 0) 0)) p.oW 0 0
        + asw fl N.outB p.oB) := by
      unfold ANet.out; rw [hrun]; rfl
    rw [e]
    exact hmlp
  rw [htarget]
  generalize outIV δ N B E c.cands (tokAt w i) sel = o at hIn hbound
  have hb2 : |((o.1 : ℚ) : ℝ) - ((T.out st.1 (tokAt w i) : ℕ) : ℝ)| + ((o.2 : ℚ) : ℝ) ≤ 1 / 4 := by
    have h1 : (((qabs (o.1 - ((T.out st.1 (tokAt w i) : ℕ) : ℚ)) + o.2 : ℚ)) : ℝ)
        ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hbound
    rw [Rat.cast_add, zqabs_cast] at h1
    push_cast at h1
    linarith
  have h2 := abs_sub_le (N.out fl ex p w i) ((o.1 : ℚ) : ℝ) ((T.out st.1 (tokAt w i) : ℕ) : ℝ)
  unfold InIV at hIn
  linarith

theorem sound : Lane4.Cert.Sound := by
  intro N T c hchk u η M fl ex hR hX hu0 hu1 hη0 hη1 p hp w hw hu hη hM i hi1 hi2
  have hδc : (((1 / 1000 : ℚ)) : ℝ) = 1 / 1000 := by norm_num
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hn2 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hM1 : (2 : ℝ) ^ 40 ≤ M := by nlinarith
  have hCtx : Ctx u η M fl := ⟨hR, hu0, hu1, hη0, hη1, hM1⟩
  have hp' : p.Within (((1 / 1000 : ℚ)) : ℝ) := by rw [hδc]; exact hp
  exact sound_core (δ := 1 / 1000) (by norm_num) (by norm_num) hchk hCtx hX hp' hw hu hη hM hi1 hi2

end Lane4.R7K5

