namespace Lane4.Case
open Lane4.Seq Lane4.Coll Lane4.TB

def scR (T : List ℕ) (f : ℚ) : ℕ → List ℚ → List ℚ
  | _, [] => []
  | c, v :: vs => (if c ∈ T then v * f else v) :: scR T f (c + 1) vs

theorem scR_length (T : List ℕ) (f : ℚ) (l : List ℚ) :
    ∀ c, (scR T f c l).length = l.length := by
  induction l with
  | nil => intro c; simp [scR]
  | cons v vs ih => intro c; simp [scR, ih]

theorem scR_getD (T : List ℕ) (f : ℚ) (l : List ℚ) :
    ∀ (c k : ℕ), (scR T f c l).getD k 0 = if c + k ∈ T then l.getD k 0 * f else l.getD k 0 := by
  induction l with
  | nil => intro c k; by_cases h : c + k ∈ T <;> simp [scR, h]
  | cons v vs ih =>
    intro c k
    cases k with
    | zero => by_cases h : c ∈ T <;> simp [scR, h]
    | succ k =>
      have e : c + (k + 1) = (c + 1) + k := by omega
      rw [e]
      simp [scR, ih]

theorem fa2_refl {α : Type} {R : α → α → Prop} (h : ∀ x, R x x) :
    ∀ l : List α, List.Forall₂ R l l := by
  intro l
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih => exact List.Forall₂.cons (h a) ih

theorem qRel_refl (τ : ℚ) (h0 : 0 ≤ τ) (a : ℚ) : qRel τ a a := by
  unfold qRel
  rw [sub_self, abs_zero]
  exact mul_nonneg h0 (abs_nonneg a)

theorem vRel_refl (τ : ℚ) (h0 : 0 ≤ τ) (l : List ℚ) : vRel τ l l :=
  fa2_refl (qRel_refl τ h0) l

theorem mRel_refl (τ : ℚ) (h0 : 0 ≤ τ) (l : List (List ℚ)) : mRel τ l l :=
  fa2_refl (vRel_refl τ h0) l

theorem netRel_self (τ : ℚ) (h0 : 0 ≤ τ) (N : TNet) : netRel τ N N :=
  ⟨mRel_refl τ h0 _,
   fa2_refl (fun B => ⟨fa2_refl (fun h => ⟨mRel_refl τ h0 _, mRel_refl τ h0 _, rfl⟩) _,
     mRel_refl τ h0 _, vRel_refl τ h0 _, mRel_refl τ h0 _, vRel_refl τ h0 _⟩) _,
   vRel_refl τ h0 _, qRel_refl τ h0 _⟩

theorem scR_rel (T : List ℕ) (f τ : ℚ) (hf : |f - 1| ≤ τ) :
    ∀ (l : List ℚ) (c : ℕ), vRel τ l (scR T f c l) := by
  have h0 : 0 ≤ τ := le_trans (abs_nonneg _) hf
  intro l
  induction l with
  | nil => intro c; unfold vRel; simp [scR]
  | cons v vs ih =>
    intro c
    unfold vRel at ih ⊢
    simp only [scR]
    refine List.Forall₂.cons ?_ (ih (c + 1))
    unfold qRel
    split_ifs with h
    · have e : v * f - v = v * (f - 1) := by ring
      rw [e, abs_mul]
      nlinarith [abs_nonneg v]
    · rw [sub_self, abs_zero]
      exact mul_nonneg h0 (abs_nonneg v)

def gRow (T : List ℕ) (s o : ℕ) (fs fo : ℚ) (t : ℕ) (row : List ℚ) : List ℚ :=
  if t = s then scR T fs 0 row else if t = o then scR T fo 0 row else row

def scE (T : List ℕ) (s o : ℕ) (fs fo : ℚ) : ℕ → List (List ℚ) → List (List ℚ)
  | _, [] => []
  | t, r :: rs => gRow T s o fs fo t r :: scE T s o fs fo (t + 1) rs

theorem scE_length (T : List ℕ) (s o : ℕ) (fs fo : ℚ) (t : ℕ) (l : List (List ℚ)) :
    (scE T s o fs fo t l).length = l.length := by
  induction l generalizing t with
  | nil => simp [scE]
  | cons r rs ih => simp [scE, ih]

theorem scE_getD (T : List ℕ) (s o : ℕ) (fs fo : ℚ) (l : List (List ℚ)) :
    ∀ (t k : ℕ), (scE T s o fs fo t l).getD k [] = gRow T s o fs fo (t + k) (l.getD k []) := by
  induction l with
  | nil =>
    intro t k
    by_cases h1 : t + k = s <;> by_cases h2 : t + k = o <;>
      simp [scE, gRow, h1, h2, scR]
  | cons r rs ih =>
    intro t k
    cases k with
    | zero => simp [scE]
    | succ k =>
      have e : t + (k + 1) = (t + 1) + k := by omega
      rw [e]
      simp [scE, ih]

theorem scE_rel (T : List ℕ) (s o : ℕ) (fs fo τ : ℚ) (hfs : |fs - 1| ≤ τ) (hfo : |fo - 1| ≤ τ) :
    ∀ (l : List (List ℚ)) (t : ℕ), mRel τ l (scE T s o fs fo t l) := by
  have h0 : 0 ≤ τ := le_trans (abs_nonneg _) hfs
  intro l
  induction l with
  | nil => intro t; unfold mRel; simp [scE]
  | cons r rs ih =>
    intro t
    unfold mRel at ih ⊢
    simp only [scE]
    refine List.Forall₂.cons ?_ (ih (t + 1))
    unfold gRow
    split_ifs
    · exact scR_rel T fs τ hfs r 0
    · exact scR_rel T fo τ hfo r 0
    · exact vRel_refl τ h0 r

def scale (N : TNet) (T : List ℕ) (s o : ℕ) (fs fo : ℚ) : TNet :=
  ⟨scE T s o fs fo 0 N.embed, N.blocks, N.outW, N.outB⟩

theorem scale_netRel (τ : ℚ) (N : TNet) (T : List ℕ) (s o : ℕ) (fs fo : ℚ)
    (hfs : |fs - 1| ≤ τ) (hfo : |fo - 1| ≤ τ) : netRel τ N (scale N T s o fs fo) := by
  have h0 : 0 ≤ τ := le_trans (abs_nonneg _) hfs
  obtain ⟨_, h2, h3, h4⟩ := netRel_self τ h0 N
  exact ⟨scE_rel T s o fs fo τ hfs hfo N.embed 0, h2, h3, h4⟩

theorem sameOff (N : TNet) (T : List ℕ) (s o : ℕ) (fs fo : ℚ) :
    SameOffT N (scale N T s o fs fo) T := by
  refine ⟨rfl, rfl, rfl, scE_length T s o fs fo 0 N.embed, ?_, ?_⟩
  · intro t
    show ((scE T s o fs fo 0 N.embed).getD t []).length = _
    rw [scE_getD, zero_add]
    unfold gRow
    split_ifs <;> simp [scR_length]
  · intro t c hc
    show ((scE T s o fs fo 0 N.embed).getD t []).getD c 0 = _
    rw [scE_getD, zero_add]
    unfold gRow
    split_ifs <;> simp [scR_getD, hc]

theorem ent (N : TNet) (T : List ℕ) (s o : ℕ) (fs fo : ℚ) (t c : ℕ) :
    ((scale N T s o fs fo).embed.getD t []).getD c 0 =
      if c ∈ T then (N.embed.getD t []).getD c 0 *
        (if t = s then fs else if t = o then fo else 1)
      else (N.embed.getD t []).getD c 0 := by
  show ((scE T s o fs fo 0 N.embed).getD t []).getD c 0 = _
  rw [scE_getD, zero_add]
  unfold gRow
  by_cases h1 : t = s <;> by_cases h2 : t = o <;> by_cases hc : c ∈ T <;>
    simp [h1, h2, hc, scR_getD]

theorem sum_getD (g : ℕ → ℚ) (w : List ℕ) :
    ((List.range w.length).map (fun j => g (w.getD j 0))).sum = (w.map g).sum := by
  induction w with
  | nil => simp
  | cons x t ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def, ih]

theorem colsum_gen (g : ℕ → ℚ) (w : List ℕ) :
    ((List.range (w.length + 1)).map (fun j => g (tokAt w j))).sum = g 0 + (w.map g).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, tokAt_zero, List.map_map]
  congr 1
  have h : (fun j => g (tokAt w j)) ∘ Nat.succ = fun j => g (w.getD j 0) := by
    funext j
    simp [Function.comp, tokAt]
  rw [h]
  exact sum_getD g w

theorem colSum_rep (M : TNet) (s o a k c : ℕ) :
    colSum M (List.replicate a s ++ List.replicate k o) c =
      (M.embed.getD 0 []).getD c 0 + (a : ℚ) * (M.embed.getD s []).getD c 0
        + (k : ℚ) * (M.embed.getD o []).getD c 0 := by
  unfold colSum
  refine (colsum_gen (fun t => (M.embed.getD t []).getD c 0) _).trans ?_
  simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul]
  ring

theorem collision_of_invariance : Invariance → Collision := by
  intro hI N ntok T s o htb hs1 hs2 ho1 ho2 τ a b hτ1 ha hb hA hB
  have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have h0 : 0 ≤ τ := by nlinarith
  by_cases hso : s = o
  · have e : List.replicate a s ++ List.replicate (b + 1) o
        = List.replicate (a + 1) s ++ List.replicate b o := by
      rw [← hso, ← List.replicate_add, ← List.replicate_add]
      congr 1 <;> omega
    exact ⟨N, N, netRel_self τ h0 N, netRel_self τ h0 N, fun i _ => by rw [e]⟩
  · have hapos : (0 : ℚ) < a := by linarith
    have hbpos : (0 : ℚ) < b := by linarith
    have key : ∃ d1s d2s d1o d2o : ℚ, |d1s| ≤ τ ∧ |d2s| ≤ τ ∧ |d1o| ≤ τ ∧ |d2o| ≤ τ ∧
        (a : ℚ) * (1 + d1s) = ((a : ℚ) + 1) * (1 + d2s) ∧
        ((b : ℚ) + 1) * (1 + d1o) = (b : ℚ) * (1 + d2o) := by
      refine ⟨(1 - τ * ((a : ℚ) + 1)) / a, -τ, -τ, (1 - τ * ((b : ℚ) + 1)) / b,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [abs_le]
        constructor
        · rw [le_div_iff₀ hapos]; nlinarith
        · rw [div_le_iff₀ hapos]; nlinarith
      · rw [abs_neg, abs_of_nonneg h0]
      · rw [abs_neg, abs_of_nonneg h0]
      · rw [abs_le]
        constructor
        · rw [le_div_iff₀ hbpos]; nlinarith
        · rw [div_le_iff₀ hbpos]; nlinarith
      · have : (a : ℚ) ≠ 0 := ne_of_gt hapos
        field_simp <;> ring
      · have : (b : ℚ) ≠ 0 := ne_of_gt hbpos
        field_simp <;> ring
    obtain ⟨d1s, d2s, d1o, d2o, e1, e2, e3, e4, i1, i2⟩ := key
    have hf : ∀ d : ℚ, |d| ≤ τ → |(1 + d) - 1| ≤ τ := by
      intro d h
      have : 1 + d - 1 = d := by ring
      rw [this]; exact h
    have h0s : ¬ (0 : ℕ) = s := by omega
    have h0o : ¬ (0 : ℕ) = o := by omega
    have hos : ¬ o = s := fun h => hso h.symm
    have v1 : ∀ t ∈ List.replicate a s ++ List.replicate (b + 1) o, 1 ≤ t ∧ t ≤ ntok := by
      intro t ht
      simp only [List.mem_append, List.mem_replicate] at ht
      rcases ht with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨hs1, hs2⟩
      · exact ⟨ho1, ho2⟩
    have v2 : ∀ t ∈ List.replicate (a + 1) s ++ List.replicate b o, 1 ≤ t ∧ t ≤ ntok := by
      intro t ht
      simp only [List.mem_append, List.mem_replicate] at ht
      rcases ht with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨hs1, hs2⟩
      · exact ⟨ho1, ho2⟩
    have hl1 : (List.replicate a s ++ List.replicate (b + 1) o).length = a + b + 1 := by
      rw [List.length_append, List.length_replicate, List.length_replicate]; omega
    have hl2 : (List.replicate (a + 1) s ++ List.replicate b o).length = a + b + 1 := by
      rw [List.length_append, List.length_replicate, List.length_replicate]; omega
    refine ⟨scale N T s o (1 + d1s) (1 + d1o), scale N T s o (1 + d2s) (1 + d2o),
      scale_netRel τ N T s o _ _ (hf _ e1) (hf _ e3),
      scale_netRel τ N T s o _ _ (hf _ e2) (hf _ e4), ?_⟩
    have hc : ∀ c ∈ T,
        colSum (scale N T s o (1 + d1s) (1 + d1o))
          (List.replicate a s ++ List.replicate (b + 1) o) c =
        colSum (scale N T s o (1 + d2s) (1 + d2o))
          (List.replicate (a + 1) s ++ List.replicate b o) c := by
      intro c hcT
      rw [colSum_rep, colSum_rep]
      simp [ent, hcT, h0s, h0o, hso, hos]
      push_cast
      linear_combination ((N.embed.getD s []).getD c 0) * i1 +
        ((N.embed.getD o []).getD c 0) * i2
    intro i hi
    exact hI N _ _ ntok T htb (sameOff N T s o _ _) (sameOff N T s o _ _) _ _ v1 v2
      (hl1.trans hl2.symm) hc i (by rw [hl1]; exact hi)

end Lane4.Case
