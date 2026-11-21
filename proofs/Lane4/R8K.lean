/-
Lane 4, rung 7 kit module, assembled by tools/r7_assemble.py from kit case kh
(runs/r8-kit/kh): statements by the lane, proofs by a Sonnet doctor, checked by tools/check.py.
-/
import Lane4.R8B3

namespace Lane4.R8K
end Lane4.R8K


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Lane4.R8K
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

theorem mem_of_contains' {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α}
    (h : l.contains a = true) : a ∈ l := by
  first
  | exact List.contains_iff_mem.mp h
  | exact List.elem_iff.mp h
  | exact List.mem_of_elem_eq_true h
  | simpa using h

theorem check8_open {δ : ℚ} {N : ANet} {T : Task} {c : Cert8} (h : check8 δ N T c = true) :
    ∃ B : ABlock, N.blocks = [B] ∧ 0 ≤ δ ∧ δ ≤ 1 / 2 ∧ N.shapeOK T.ntok = true ∧
      weightsOK N B = true ∧ c.heads.length = B.heads.length ∧
      (List.zipWith (fun h hc => headOK8 δ (N.embed.map (embIV δ)) h hc) B.heads c.heads).all id = true ∧
      (∀ st ∈ c.states, st.2.length = B.heads.length) ∧
      absInit8 T c.heads ∈ c.states ∧
      (∀ st ∈ c.states, ∀ t, 1 ≤ t → t ≤ T.ntok → caseOK8 δ N B T c st t = true) := by
  unfold check8 at h
  split at h
  · rename_i B hB
    refine ⟨B, hB, ?_⟩
    try dsimp only at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    refine ⟨h1, h2, h3, h4, beq_iff_eq.mp h5, h6, ?_, mem_of_contains' h8, ?_⟩
    · intro st hst
      exact beq_iff_eq.mp (List.all_eq_true.mp h7 st hst)
    · intro st hst t ht1 ht2
      have h' : caseOK8 δ N B T c st (t - 1 + 1) = true :=
        List.all_eq_true.mp (List.all_eq_true.mp h9 st hst) (t - 1) (List.mem_range.mpr (by omega))
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

theorem headOK8_facts {δ : ℚ} {E : List (List IV)} {hd : AHead} {hc : HCert}
    (h : headOK8 δ E hd hc = true) : hd.mask ≠ Mask.all ∧ 1 ≤ hc.L := by
  unfold headOK8 at h
  simp only [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1.1.1.1.1.1.1.1.1.1.1.1.1, of_decide_eq_true h.1.1.2⟩

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

theorem getD_getD {α : Type} (d : α) :
    ∀ (l : List α) (a : ℕ), a < l.length → l.getD a (l.getD a d) = l.getD a d
  | [], a, h => by simp at h
  | x :: l, 0, _ => by simp
  | x :: l, a + 1, h => by
      simp only [List.getD_cons_succ]
      exact getD_getD d l a (by simpa using h)

theorem caseOK8_facts {δ : ℚ} {N : ANet} {B : ABlock} {T : Task} {c : Cert8}
    {st : ℕ × List (List ℕ)} {t : ℕ} (h : caseOK8 δ N B T c st t = true) :
    ∃ o : AF, outAF δ N B c t st.2 = some o ∧
      qabs (o.c - (T.out st.1 t : ℚ)) + o.dev ≤ 1 / 4 ∧ absStep8 T c.heads st t ∈ c.states := by
  unfold caseOK8 at h
  split at h
  · simp at h
  · rename_i o ho
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨o, ho, h.1, mem_of_contains' h.2⟩

theorem outAF_open {δ : ℚ} {N : ANet} {B : ABlock} {c : Cert8} {t : ℕ} {wins : List (List ℕ)}
    {o : AF} (h : outAF δ N B c t wins = some o) :
    ∃ y : List AF,
      headsAF δ ((N.embed.getD t []).map (fun a => (⟨a, [], e0 δ⟩ : AF))).length t B.heads c.heads
        wins 0 ((N.embed.getD t []).map (fun a => (⟨a, [], e0 δ⟩ : AF))) = some y ∧
      (affAF δ B.W1 B.b1 y).all AF.small = true ∧
      (affAF δ B.W2 B.b2 ((affAF δ B.W1 B.b1 y).map reluAF)).all AF.small = true ∧
      (addAF y (affAF δ B.W2 B.b2 ((affAF δ B.W1 B.b1 y).map reluAF))).all AF.small = true ∧
      o = (dotAF δ N.outW
        (addAF y (affAF δ B.W2 B.b2 ((affAF δ B.W1 B.b1 y).map reluAF)))).shift N.outB
          (e0 δ + rnd) ∧
      AF.small o = true := by
  unfold outAF at h
  try dsimp only at h
  split at h
  · simp at h
  · rename_i y hy
    refine ⟨y, hy, ?_⟩
    by_cases h1 : (affAF δ B.W1 B.b1 y).all AF.small = true
    · rw [if_pos h1] at h
      by_cases h2 : (affAF δ B.W2 B.b2 ((affAF δ B.W1 B.b1 y).map reluAF)).all AF.small = true
      · rw [if_pos h2] at h
        by_cases h3 : (addAF y (affAF δ B.W2 B.b2
            ((affAF δ B.W1 B.b1 y).map reluAF))).all AF.small = true
        · rw [if_pos h3] at h
          by_cases h4 : AF.small ((dotAF δ N.outW
              (addAF y (affAF δ B.W2 B.b2 ((affAF δ B.W1 B.b1 y).map reluAF)))).shift N.outB
                (e0 δ + rnd)) = true
          · rw [if_pos h4] at h
            have ho := (Option.some.inj h).symm
            subst ho
            exact ⟨h1, h2, h3, rfl, h4⟩
          · rw [if_neg h4] at h; simp at h
        · rw [if_neg h3] at h; simp at h
      · rw [if_neg h2] at h; simp at h
    · rw [if_neg h1] at h; simp at h

theorem small_mag {a : AF} (h : AF.small a = true) : a.mag ≤ 15 := of_decide_eq_true h

theorem affAF_length (δ : ℚ) (M : List (List ℚ)) (b : List ℚ) (x : List AF) :
    (affAF δ M b x).length = min M.length b.length := by
  simp [affAF]

theorem addAF_length (a b : List AF) : (addAF a b).length = min a.length b.length := by
  simp [addAF]

theorem aattnRows_length (fl ex : ℝ → ℝ) :
    ∀ (M : List (List ℚ)) (dV : ℕ → ℕ → ℝ) (c : List ℕ) (s : ℕ → ℝ) (x : ℕ → Vec) (i : ℕ),
      (aattnRows fl ex M dV c s x i).length = M.length
  | [], _, _, _, _, _ => rfl
  | r :: M, dV, c, s, x, i => by
      simp only [aattnRows, List.length_cons, aattnRows_length fl ex M dV c s x (i + 1)]

def dfltHead : AHead := ⟨[], [], Mask.all, 0, [], 0⟩
def dfltHC : HCert := ⟨[], 0, 0, [], [], []⟩

def GoodH (δ : ℚ) (E : List (List IV)) (w : List ℕ) (i d : ℕ) (hd : AHead) (hc : HCert)
    (win : List ℕ) : Prop :=
  headOK8 δ E hd hc = true ∧ hd.shapeOK d = true ∧ smallM hd.A = true ∧ smallM hd.V = true ∧
  smallQ hd.g = true ∧ smallQ [hd.gb] = true ∧
  ∃ P : List ℕ, WinPos hd.mask hc.cands (tokAt w) (w.length + 1) i P ∧
    P.map (tokAt w) = keysAt hd hc (tokAt w i) win ∧
    P.length ≤ fullLen hd hc (tokAt w i) ∧
    (P.length < fullLen hd hc (tokAt w i) →
      ∀ k ∈ cand hd.mask (w.length + 1) i, hc.cands.getD (tokAt w k) false = true → k ∈ P)

theorem heads_ind8 {u η M : ℝ} {fl ex : ℝ → ℝ} (hC : Ctx u η M fl) (hX : ExpM u η ex)
    {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (E : List (List IV)) (p : APert)
    (hp : p.Within (δ : ℝ)) (w : List ℕ) (x : ℕ → Vec) (i d : ℕ) (hd24 : d ≤ 24)
    (hrows : ∀ row ∈ E, row.length = d ∧ Bdd 16 row)
    (hu : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100)
    (hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M)
    (hxE : ∀ j, j < w.length + 1 → tokAt w j < E.length ∧ InIVs (x j) (E.getD (tokAt w j) []))
    (hi : i < w.length + 1) (hti : 1 ≤ tokAt w i) :
    ∀ (hs : List AHead) (hcs : List HCert) (wins : List (List ℕ)) (k pre : ℕ)
      (acc : List AF) (accR : List ℝ) (y : List AF),
      hcs.length = hs.length → wins.length = hs.length → acc.length = d →
      (∀ a ∈ acc, a.mag ≤ 16) →
      (∃ g : ℕ → ℝ, (∀ m, |g m| ≤ 1) ∧
        ∀ e : ℕ → ℝ, Sym e → (∀ m, m < pre → e m = g m) → InAFs e accR acc) →
      (∀ j, j < hs.length → GoodH δ E w i d (hs.getD j dfltHead) (hcs.getD j dfltHC)
        (wins.getD j [])) →
      headsAF δ d (tokAt w i) hs hcs wins pre acc = some y →
      ∃ g : ℕ → ℝ, (∀ m, |g m| ≤ 1) ∧
        InAFs g (aheadsApply fl ex p 0 (w.length + 1) x i hs accR k) y ∧
        (∀ a ∈ y, a.mag ≤ 16) ∧ y.length = d := by
  intro hs
  induction hs with
  | nil =>
    intro hcs wins k pre acc accR y hl1 hl2 hlen hmag hinv hgood hrun
    have e1 : headsAF δ d (tokAt w i) [] hcs wins pre acc = some acc := by
      cases hcs <;> cases wins <;> rfl
    rw [e1] at hrun
    have hy : acc = y := Option.some.inj hrun
    subst hy
    obtain ⟨g, hg1, hg2⟩ := hinv
    exact ⟨g, hg1, hg2 g (fun m => hg1 m) (fun _ _ => rfl), hmag, hlen⟩
  | cons hd hs ih =>
    intro hcs wins k pre acc accR y hl1 hl2 hlen hmag hinv hgood hrun
    cases hcs with
    | nil => simp at hl1
    | cons hc hcs =>
    cases wins with
    | nil => simp at hl2
    | cons win wins =>
    have g0 := hgood 0 (Nat.succ_pos _)
    simp only [List.getD_cons_zero] at g0
    obtain ⟨hOK, hsh, wA, wV, wg, wgb, P, hWin, hPmap, hPle, hPfull⟩ := g0
    simp only [headsAF] at hrun
    cases hha : headAF δ hd hc d pre (tokAt w i) (keysAt hd hc (tokAt w i) win) with
    | none => simp [hha] at hrun
    | some ho =>
      simp only [hha] at hrun
      by_cases hguard : (addAF acc ho).all AF.small = true
      · rw [if_pos hguard] at hrun
        have hpk : (keysAt hd hc (tokAt w i) win).length = P.length := by
          rw [← hPmap]; simp
        have hha' : headAF δ hd hc d pre (tokAt w i) (P.map (tokAt w)) = some ho := by
          rw [hPmap]; exact hha
        obtain ⟨e', he'1, he'2⟩ := Lane4.R8KG.head_sound8 u η M fl ex hC hX δ hδ0 hδ1 hd E hc d
          hOK hsh hd24 wA wV wg wgb hrows
          (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k) (p.gb 0 k)
          (hp.A 0 k) (hp.V 0 k) (hp.m 0 k) (hp.g 0 k) (hp.gb 0 k)
          (w.length + 1) x (tokAt w) hu hη hM hxE i hi hti P pre hWin hPle hPfull ho hha'
        obtain ⟨g, hg1, hg2⟩ := hinv
        obtain ⟨g', hg'def⟩ : ∃ g' : ℕ → ℝ, ∀ m, g' m = if m < pre then g m else e' (m - pre) :=
          ⟨fun m => if m < pre then g m else e' (m - pre), fun _ => rfl⟩
        have hg'1 : ∀ m, |g' m| ≤ 1 := by
          intro m
          rw [hg'def m]
          split_ifs
          · exact hg1 m
          · exact he'1 _
        have hag1 : ∀ e : ℕ → ℝ, (∀ m, m < pre + (P.length - 1) → e m = g' m) →
            (∀ m, m < pre → e m = g m) := by
          intro e hag m hm
          rw [hag m (by omega), hg'def m, if_pos hm]
        have hag2 : ∀ e : ℕ → ℝ, (∀ m, m < pre + (P.length - 1) → e m = g' m) →
            (∀ k', k' < P.length - 1 → e (pre + k') = e' k') := by
          intro e hag k' hk'
          have hn : ¬ (pre + k' < pre) := by omega
          rw [hag _ (by omega), hg'def, if_neg hn, Nat.add_sub_cancel_left]
        have hagg : ∀ m, m < pre + (P.length - 1) → g' m = g' m := fun _ _ => rfl
        have hrep : ∀ e : ℕ → ℝ, Sym e → (∀ m, m < pre + (P.length - 1) → e m = g' m) →
            InAFs e (radd fl accR (hd.attn fl ex (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k)
              (p.gb 0 k) (w.length + 1) x i)) (addAF acc ho) := by
          intro e he hag
          exact Lane4.R8KE.add_af u η M fl hC accR _ acc ho e he (hg2 e he (hag1 e hag))
            (he'2 e (hag2 e hag)) hguard
        have hho := he'2 g' (hag2 g' (fun _ _ => rfl))
        have hattn : (hd.attn fl ex (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k) (p.gb 0 k)
            (w.length + 1) x i).length = d := by
          have h1 : (hd.attn fl ex (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k) (p.gb 0 k)
              (w.length + 1) x i).length = hd.V.length :=
            aattnRows_length fl ex _ _ _ _ _ _
          rw [h1]
          exact (head_shape hsh).2
        have hholen : ho.length = d := by rw [← hho.1]; exact hattn
        have hlen' : (addAF acc ho).length = d := by
          rw [addAF_length, hlen, hholen, min_self]
        have hmag' : ∀ a ∈ addAF acc ho, a.mag ≤ 16 := by
          intro a ha
          have := small_mag (List.all_eq_true.mp hguard a ha)
          linarith
        have hl1' : hcs.length = hs.length := by simpa using hl1
        have hl2' : wins.length = hs.length := by simpa using hl2
        have hgood' : ∀ j, j < hs.length → GoodH δ E w i d (hs.getD j dfltHead)
            (hcs.getD j dfltHC) (wins.getD j []) := by
          intro j hj
          have := hgood (j + 1) (by simp only [List.length_cons]; omega)
          simpa using this
        rw [hpk] at hrun
        exact ih hcs wins (k + 1) (pre + (P.length - 1)) (addAF acc ho)
          (radd fl accR (hd.attn fl ex (p.A 0 k) (p.V 0 k) (p.m 0 k) (p.g 0 k) (p.gb 0 k)
            (w.length + 1) x i)) y hl1' hl2' hlen' hmag' ⟨g', hg'1, hrep⟩ hgood' hrun
      · rw [if_neg hguard] at hrun
        simp at hrun

theorem sound_core8 {δ : ℚ} {N : ANet} {T : Task} {c : Cert8}
    (hchk : check8 δ N T c = true) {u η M : ℝ} {fl ex : ℝ → ℝ} (hC : Ctx u η M fl)
    (hX : ExpM u η ex)
    {p : APert} (hp : p.Within (δ : ℝ)) {w : List ℕ} (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ T.ntok)
    (hu : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (hη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100)
    (hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ w.length) :
    |N.out fl ex p w i - ((T.target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨B, hB, hδ0, hδ1, hshape, hweights, hcl, hzip, hslen, hinit, hcase⟩ := check8_open hchk
  obtain ⟨d, hd24, hembl, hembrows, hblocks, houtW⟩ := shape_facts hshape
  have hBshape : B.shapeOK d = true := hblocks B (by rw [hB]; simp)
  obtain ⟨hhl4, hheadsh, hb1l, hW1l, hW1r, hW2l, hW2r, hb2l⟩ := block_shape hBshape
  obtain ⟨wEmb, wOut, wOutB, wW1, wb1, wW2, wb2, wHeads⟩ := weights_facts hweights
  generalize hE : N.embed.map (embIV δ) = E at hzip
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
  have hstate : absState8 T c.heads (w.take (i - 1)) ∈ c.states :=
    Lane4.R8KF.abs_closed8 T c.heads c.states hinit
      (fun st hst t h1 h2 => (caseOK8_facts (hcase st hst t h1 h2)).choose_spec.2.2) _ hpre
  have htarget := Lane4.R8KF.abs_target8 T c.heads w i hi1 hi2
  have hslen' := hslen _ hstate
  generalize hst : absState8 T c.heads (w.take (i - 1)) = st at hstate htarget hslen'
  have hti : tokAt w i ∈ w := by
    have h1 := Lane4.Seq.tokAt_succ w (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at h1
    rw [h1]; exact List.getElem_mem _
  have hti1 := (hw _ hti).1
  have hti2 := (hw _ hti).2
  obtain ⟨o, hout, hbound, _⟩ := caseOK8_facts (hcase st hstate (tokAt w i) hti1 hti2)
  obtain ⟨y, hy, ha1, ha2, hadd, hoeq, hosm⟩ := outAF_open hout
  have hltN : tokAt w i < N.embed.length := by have := htokle i; omega
  have hrowlen : (N.embed.getD (tokAt w i) []).length = d :=
    hembrows _ (zgetD_mem' [] N.embed _ hltN)
  have hl : ((N.embed.getD (tokAt w i) []).map (fun a => (⟨a, [], e0 δ⟩ : AF))).length = d := by
    rw [List.length_map]; exact hrowlen
  rw [hl] at hy
  have hemb := Lane4.R8KE.emb_af u η M fl hC δ hδ0 hδ1 (N.embed.getD (tokAt w i) [])
    (p.E (tokAt w i)) (fun k => hp.E _ k) (zsmallM_mem wEmb _ (zgetD_mem' [] N.embed _ hltN))
  have hgood : ∀ a, a < B.heads.length → GoodH δ E w i d (B.heads.getD a dfltHead)
      (c.heads.getD a dfltHC) (st.2.getD a []) := by
    intro a ha
    have hmem : B.heads.getD a dfltHead ∈ B.heads := zgetD_mem' dfltHead B.heads a ha
    have hOKhd : headOK8 δ E (B.heads.getD a dfltHead) (c.heads.getD a dfltHC) = true :=
      zipWith_all_getD _ dfltHead dfltHC B.heads c.heads hcl hzip a ha
    have hshd := hheadsh _ hmem
    obtain ⟨wA, wV, wg, wgb⟩ := wHeads _ hmem
    obtain ⟨hne, hL⟩ := headOK8_facts hOKhd
    obtain ⟨P, hP1, hP2, hP3, hP4⟩ := Lane4.R8KF.abs_keys8 T c.heads w i a
      (B.heads.getD a dfltHead) (c.heads.getD a dfltHC) hi1 hi2 (by omega)
      (getD_getD dfltHC c.heads a (by omega)) hne hL
    rw [hst] at hP2
    exact ⟨hOKhd, hshd, wA, wV, wg, wgb, P, hP1, hP2, hP3, hP4⟩
  obtain ⟨g, hg1, hIn, hmag16, hylen⟩ := heads_ind8 hC hX hδ0 hδ1 E p hp w (N.init fl p w) i d
    hd24 hrows hu hη hM hxE (by omega) hti1 B.heads c.heads st.2 0 0 _ (N.init fl p w i) y
    hcl hslen' hl (fun a ha => (hemb (fun _ => 0)).2 a ha)
    ⟨fun _ => 0, fun _ => by norm_num, fun e _ _ => (hemb e).1⟩
    (fun j hj => hgood j hj) hy
  have he : Sym g := fun m => hg1 m
  obtain ⟨yR, hyRdef⟩ : ∃ yR : List ℝ, yR = aheadsApply fl ex p 0 (w.length + 1) (N.init fl p w) i
      B.heads (N.init fl p w i) 0 := ⟨_, rfl⟩
  rw [← hyRdef] at hIn
  have hout_eq : N.out fl ex p w i = fl (ardot fl N.outW (radd fl yR
      (araffine fl B.W2 B.b2 ((araffine fl B.W1 B.b1 yR (p.W1 0) (p.b1 0) 0).map Lane4.relu)
        (p.W2 0) (p.b2 0) 0)) p.oW 0 0 + asw fl N.outB p.oB) := by
    rw [hyRdef]
    unfold ANet.out; rw [hrun]; rfl
  have hyRlen : yR.length = d := by rw [hIn.1, hylen]
  -- MLP
  have hW1 := Lane4.R8KE.aff_af u η M fl hC δ hδ0 hδ1 B.W1 B.b1 yR y (p.W1 0) (p.b1 0)
    (hp.W1 0) (hp.b1 0) (fun r hr => by rw [hW1r r hr, hyRlen])
    (by rw [hyRlen]; exact hd24.trans (by norm_num)) hW1l wW1 wb1 g he hIn hmag16 ha1
  obtain ⟨hrelu1, hrelu2⟩ := Lane4.R8KE.relu_af _ _ g he hW1 ha1
  have hlenA1 : ((affAF δ B.W1 B.b1 y).map reluAF).length = B.b1.length := by
    rw [List.length_map, affAF_length, hW1l, min_self]
  have hxl : ((araffine fl B.W1 B.b1 yR (p.W1 0) (p.b1 0) 0).map Lane4.relu).length
      = B.b1.length := hrelu1.1.trans hlenA1
  have hmagR : ∀ a ∈ (affAF δ B.W1 B.b1 y).map reluAF, a.mag ≤ 16 := by
    intro a ha
    have := small_mag (List.all_eq_true.mp hrelu2 a ha)
    linarith
  have hW2 := Lane4.R8KE.aff_af u η M fl hC δ hδ0 hδ1 B.W2 B.b2
    ((araffine fl B.W1 B.b1 yR (p.W1 0) (p.b1 0) 0).map Lane4.relu)
    ((affAF δ B.W1 B.b1 y).map reluAF) (p.W2 0) (p.b2 0) (hp.W2 0) (hp.b2 0)
    (fun r hr => by rw [hW2r r hr, hxl]) (by rw [hxl]; exact hb1l) (hW2l.trans hb2l.symm)
    wW2 wb2 g he hrelu1 hmagR ha2
  have hZ := Lane4.R8KE.add_af u η M fl hC yR _ y _ g he hIn hW2 hadd
  have hmagZ : ∀ a ∈ addAF y (affAF δ B.W2 B.b2 ((affAF δ B.W1 B.b1 y).map reluAF)),
      a.mag ≤ 16 := by
    intro a ha
    have := small_mag (List.all_eq_true.mp hadd a ha)
    linarith
  have ha2len : (affAF δ B.W2 B.b2 ((affAF δ B.W1 B.b1 y).map reluAF)).length = d := by
    rw [affAF_length, hW2l, hb2l, min_self]
  have hZlen : (addAF y (affAF δ B.W2 B.b2 ((affAF δ B.W1 B.b1 y).map reluAF))).length = d := by
    rw [addAF_length, ha2len, hylen, min_self]
  have hzR : (radd fl yR (araffine fl B.W2 B.b2
      ((araffine fl B.W1 B.b1 yR (p.W1 0) (p.b1 0) 0).map Lane4.relu)
        (p.W2 0) (p.b2 0) 0)).length = d := by rw [hZ.1, hZlen]
  have hDot := Lane4.R8KE.dot_af u η M fl hC δ hδ0 hδ1 N.outW _ _ p.oW (fun k => hp.oW k)
    (by rw [houtW, hzR]) (by rw [houtW]; exact hd24.trans (by norm_num)) wOut g he hZ hmagZ
  -- read-out
  have hasw := zasw_e0 hC hδ0 hδ1 (zsmallQ_mem wOutB N.outB (by simp)) hp.oB
  generalize hv : ardot fl N.outW (radd fl yR (araffine fl B.W2 B.b2
      ((araffine fl B.W1 B.b1 yR (p.W1 0) (p.b1 0) 0).map Lane4.relu)
        (p.W2 0) (p.b2 0) 0)) p.oW 0 0 = v at hDot hout_eq
  generalize hDA : dotAF δ N.outW (addAF y (affAF δ B.W2 B.b2
      ((affAF δ B.W1 B.b1 y).map reluAF))) = DA at hDot hoeq
  have hdiff : v + asw fl N.outB p.oB - (v + ((N.outB : ℚ) : ℝ))
      = asw fl N.outB p.oB - (N.outB : ℝ) := by ring
  have hz : InAF g (v + asw fl N.outB p.oB) (DA.shift N.outB (e0 δ)) := by
    refine Lane4.R8KE.shift_af g v _ DA N.outB (e0 δ) hDot ?_
    rw [hdiff]; exact hasw
  have hm1 := Lane4.R8KE.mag_shift DA N.outB (e0 δ + rnd)
  have hm2 := Lane4.R8KE.mag_shift DA N.outB (e0 δ)
  have hrp := zrnd_pos
  have hosm' : o.mag ≤ 15 := small_mag hosm
  rw [hoeq] at hosm'
  have hmz : (DA.shift N.outB (e0 δ)).mag ≤ 15 := by linarith
  have hb15 := Lane4.R8KE.abs_le_of_small he hz hmz
  have hy' : |v + asw fl N.outB p.oB - (v + ((N.outB : ℚ) : ℝ))| ≤ ((e0 δ : ℚ) : ℝ) := by
    rw [hdiff]; exact hasw
  have hrn := zrnd_step hC hy' hb15
  have hfin : |fl (v + asw fl N.outB p.oB) - (v + ((N.outB : ℚ) : ℝ))|
      ≤ ((e0 δ + rnd : ℚ) : ℝ) := by
    rw [Rat.cast_add, zrnd_real]
    exact hrn
  have hfinal := Lane4.R8KE.shift_af g v _ DA N.outB (e0 δ + rnd) hDot hfin
  rw [← hoeq] at hfinal
  obtain ⟨_, _, hlo, hhi⟩ := Lane4.R8KE.af_range g _ o he hfinal
  rw [hout_eq, htarget]
  have hlo' : (o.c : ℝ) - (o.dev : ℝ) ≤ fl (v + asw fl N.outB p.oB) := by
    have := hlo; push_cast at this; exact this
  have hhi' : fl (v + asw fl N.outB p.oB) ≤ (o.c : ℝ) + (o.dev : ℝ) := by
    have := hhi; push_cast at this; exact this
  have hb2 : |((o.c : ℚ) : ℝ) - ((T.out st.1 (tokAt w i) : ℕ) : ℝ)| + ((o.dev : ℚ) : ℝ) ≤ 1 / 4 := by
    have h1 : (((qabs (o.c - ((T.out st.1 (tokAt w i) : ℕ) : ℚ)) + o.dev : ℚ)) : ℝ)
        ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hbound
    rw [Rat.cast_add, zqabs_cast] at h1
    push_cast at h1
    linarith
  have h2 := abs_sub_le (fl (v + asw fl N.outB p.oB)) ((o.c : ℚ) : ℝ)
    ((T.out st.1 (tokAt w i) : ℕ) : ℝ)
  have h3 : |fl (v + asw fl N.outB p.oB) - ((o.c : ℚ) : ℝ)| ≤ ((o.dev : ℚ) : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

theorem sound8 : Lane4.Cert8.Sound8 := by
  intro δ N T c hchk u η M fl ex hR hX hu0 hu1 hη0 hη1 p hp w hw hu hη hM i hi1 hi2
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hn2 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hM1 : (2 : ℝ) ^ 40 ≤ M := by nlinarith
  have hCtx : Ctx u η M fl := ⟨hR, hu0, hu1, hη0, hη1, hM1⟩
  exact sound_core8 hchk hCtx hX hp hw hu hη hM hi1 hi2

end Lane4.R8K

