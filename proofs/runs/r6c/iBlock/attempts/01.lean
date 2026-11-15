namespace Lane4.Case
open Lane4.Seq Lane4.Coll Lane4.TB Lane4.Inv

theorem vadd_length (a b : Vec) : (vadd a b).length = min a.length b.length := by
  simp [vadd]

theorem vadd_getD (a b : Vec) (d c : ℕ) (ha : a.length = d) (hb : b.length = d) (hc : c < d) :
    (vadd a b).getD c 0 = a.getD c 0 + b.getD c 0 := by
  have h1 : c < a.length := by omega
  have h2 : c < b.length := by omega
  have h3 : c < (vadd a b).length := by
    have := vadd_length a b
    omega
  rw [Lane4.HeadProof.getD_lt _ _ _ h3, Lane4.HeadProof.getD_lt _ _ _ h1,
    Lane4.HeadProof.getD_lt _ _ _ h2]
  simp [vadd]

theorem fold_lemma (d n : ℕ) (x y : ℕ → Vec) (i : ℕ) :
    ∀ (hs : List Head), (∀ h ∈ hs, h.attn n x i = h.attn n y i ∧ (h.attn n x i).length = d) →
    ∀ a b : Vec, a.length = d → b.length = d →
      (hs.foldl (fun acc h => vadd acc (h.attn n x i)) a).length = d ∧
      (hs.foldl (fun acc h => vadd acc (h.attn n y i)) b).length = d ∧
      ∀ c, c < d → (hs.foldl (fun acc h => vadd acc (h.attn n x i)) a).getD c 0 + b.getD c 0
        = (hs.foldl (fun acc h => vadd acc (h.attn n y i)) b).getD c 0 + a.getD c 0 := by
  intro hs
  induction hs with
  | nil =>
    intro _ a b ha hb
    simp only [List.foldl_nil]
    exact ⟨ha, hb, fun c _ => add_comm _ _⟩
  | cons h t ih =>
    intro hh a b ha hb
    obtain ⟨he, hl⟩ := hh h (by simp)
    rw [he] at hl
    have hlen : ∀ u : Vec, u.length = d → (vadd u (h.attn n y i)).length = d := by
      intro u hu
      have := vadd_length u (h.attn n y i)
      omega
    have key := ih (fun h' hh' => hh h' (List.mem_cons_of_mem _ hh'))
      (vadd a (h.attn n y i)) (vadd b (h.attn n y i)) (hlen a ha) (hlen b hb)
    simp only [List.foldl_cons]
    rw [he]
    obtain ⟨l1, l2, l3⟩ := key
    refine ⟨l1, l2, fun c hc => ?_⟩
    have h4 := l3 c hc
    rw [vadd_getD _ _ d c ha hl hc, vadd_getD _ _ d c hb hl hc] at h4
    linarith

theorem affine_congr : ∀ (W : List Vec) (b u v : Vec), (∀ r ∈ W, qdot r u = qdot r v) →
    affine W b u = affine W b v := by
  intro W
  induction W with
  | nil => intro b u v _; simp [affine]
  | cons r t ih =>
    intro b u v h
    cases b with
    | nil => simp [affine]
    | cons c bs =>
      have key := ih bs u v (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      unfold affine at key ⊢
      rw [List.zipWith_cons_cons, List.zipWith_cons_cons, h r (by simp), key]

theorem fin_lemma (d : ℕ) (xj yj Yx Yy M : Vec) (hx : Yx.length = d) (hy : Yy.length = d)
    (hM : M.length = d) (T : List ℕ) (hoff : ∀ c, c ∉ T → Yx.getD c 0 = Yy.getD c 0)
    (hl3 : ∀ c, c < d → Yx.getD c 0 + yj.getD c 0 = Yy.getD c 0 + xj.getD c 0) :
    (vadd Yx M).length = d ∧ (vadd Yy M).length = d ∧
    (∀ c, c ∉ T → (vadd Yx M).getD c 0 = (vadd Yy M).getD c 0) ∧
    ∀ c, c < d → (vadd Yx M).getD c 0 + yj.getD c 0
      = (vadd Yy M).getD c 0 + xj.getD c 0 := by
  have e1 := vadd_length Yx M
  have e2 := vadd_length Yy M
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro c hc
    by_cases hcd : c < d
    · rw [vadd_getD _ _ d c hx hM hcd, vadd_getD _ _ d c hy hM hcd, hoff c hc]
    · have h1 : (vadd Yx M).length ≤ c := by omega
      have h2 : (vadd Yy M).length ≤ c := by omega
      rw [Lane4.HeadProof.getD_ge _ _ _ h1, Lane4.HeadProof.getD_ge _ _ _ h2]
  · intro c hc
    rw [vadd_getD _ _ d c hx hM hc, vadd_getD _ _ d c hy hM hc]
    have := hl3 c hc
    linarith

theorem pos_lemma (T : List ℕ) (d n : ℕ) (x y : ℕ → Vec) (B : Block) (hA : Agree T d n x y)
    (hbb : blockBlind T B = true) (hsh : B.shapeOK d = true) (j : ℕ) (hj : j < n) :
    (B.apply n x j).length = d ∧ (B.apply n y j).length = d ∧
    (∀ c, c ∉ T → (B.apply n x j).getD c 0 = (B.apply n y j).getD c 0) ∧
    ∀ c, c < d → (B.apply n x j).getD c 0 + (y j).getD c 0
        = (B.apply n y j).getD c 0 + (x j).getD c 0 := by
  have hsh' := hsh
  simp only [Block.shapeOK, rowsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hsh'
  obtain ⟨⟨⟨⟨⟨_, hH⟩, _⟩, ⟨_, _⟩⟩, ⟨hW2l, _⟩⟩, hb2⟩ := hsh'
  have hVlen : ∀ h ∈ B.heads, h.V.length = d := by
    intro h hh
    have := hH h hh
    simp only [Head.shapeOK, rowsOK, Bool.and_eq_true, beq_iff_eq] at this
    exact this.2.1
  have hbb' := hbb
  simp only [blockBlind, Bool.and_eq_true, List.all_eq_true] at hbb'
  obtain ⟨hHb, hW1z⟩ := hbb'
  have hatt : ∀ h ∈ B.heads, h.attn n x j = h.attn n y j ∧ (h.attn n x j).length = d := by
    intro h hh
    refine ⟨Lane4.HeadProof.head_step T d n x y h hA (hHb h hh) (hH h hh) j hj, ?_⟩
    simp [Head.attn, hVlen h hh]
  obtain ⟨hl1, hl2, hl3⟩ := fold_lemma d n x y j B.heads hatt (x j) (y j)
    (hA.1 j hj).1 (hA.1 j hj).2
  have hap : ∀ z : ℕ → Vec, B.apply n z j =
      vadd (B.heads.foldl (fun acc h => vadd acc (h.attn n z j)) (z j))
        (affine B.W2 B.b2 ((affine B.W1 B.b1
          (B.heads.foldl (fun acc h => vadd acc (h.attn n z j)) (z j))).map
            (fun v => max v 0))) := fun z => rfl
  rw [hap x, hap y]
  generalize B.heads.foldl (fun acc h => vadd acc (h.attn n x j)) (x j) = Yx at hl1 hl3 ⊢
  generalize B.heads.foldl (fun acc h => vadd acc (h.attn n y j)) (y j) = Yy at hl2 hl3 ⊢
  have hoff : ∀ c, c ∉ T → Yx.getD c 0 = Yy.getD c 0 := by
    intro c hc
    by_cases hcd : c < d
    · have h1 := hl3 c hcd
      have h2 := hA.2.1 j hj c hc
      linarith
    · rw [Lane4.HeadProof.getD_ge _ _ _ (by omega), Lane4.HeadProof.getD_ge _ _ _ (by omega)]
  have hq : ∀ r ∈ B.W1, qdot r Yx = qdot r Yy := by
    intro r hr
    apply Lane4.HeadProof.qdot_congr
    intro c hc
    by_cases hcT : c ∈ T
    · exact absurd (Lane4.HeadProof.zeroOn_get (hW1z r hr) c hcT) hc
    · exact hoff c hcT
  rw [affine_congr B.W1 B.b1 Yx Yy hq]
  have hMl : ∀ u : Vec, (affine B.W2 B.b2 u).length = d := by
    intro u
    simp [affine, hW2l, hb2]
  exact fin_lemma d (x j) (y j) Yx Yy _ hl1 hl2 (hMl _) T hoff hl3

theorem block_step : BlockStep := by
  intro T d n x y B hT hA hbb hsh
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have := pos_lemma T d n x y B hA hbb hsh j hj
    exact ⟨this.1, this.2.1⟩
  · intro j hj c hc
    exact (pos_lemma T d n x y B hA hbb hsh j hj).2.2.1 c hc
  · intro c hc
    have hcd := hT c hc
    have hpt : ∀ j ∈ List.range n,
        (B.apply n x j).getD c 0 + (y j).getD c 0
          = (B.apply n y j).getD c 0 + (x j).getD c 0 :=
      fun j hj => (pos_lemma T d n x y B hA hbb hsh j (List.mem_range.mp hj)).2.2.2 c hcd
    have e1 : ((List.range n).map (fun j => (B.apply n x j).getD c 0 + (y j).getD c 0)).sum
        = ((List.range n).map (fun j => (B.apply n y j).getD c 0 + (x j).getD c 0)).sum := by
      congr 1
      exact List.map_congr_left hpt
    rw [List.sum_map_add, List.sum_map_add] at e1
    have := hA.2.2 c hc
    linarith

end Lane4.Case
