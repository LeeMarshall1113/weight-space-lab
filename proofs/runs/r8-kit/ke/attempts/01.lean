set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-! ### basic facts -/

theorem getD_map_lt {α β : Type} (f : α → β) (d : α) (d' : β) :
    ∀ (l : List α) (k : ℕ), k < l.length → (l.map f).getD k d' = f (l.getD k d)
  | [], k, h => by simp at h
  | a :: l, 0, _ => by simp
  | a :: l, k + 1, h => by
      simp only [List.map_cons, List.getD_cons_succ]
      exact getD_map_lt f d d' l k (by simpa using h)

theorem sumAbs_nonneg : ∀ t : List ℚ, 0 ≤ sumAbs t
  | [] => by show (0 : ℚ) ≤ 0; exact le_refl _
  | a :: l => by
      have h1 := zqabs_nonneg a
      have h2 := sumAbs_nonneg l
      show 0 ≤ qabs a + sumAbs l
      linarith

theorem sumAbs_cons_cast (a : ℚ) (l : List ℚ) :
    ((sumAbs (a :: l) : ℚ) : ℝ) = ((qabs a : ℚ) : ℝ) + ((sumAbs l : ℚ) : ℝ) := by
  rw [show sumAbs (a :: l) = qabs a + sumAbs l from rfl, Rat.cast_add]

theorem linVal_bound {e : ℕ → ℝ} (he : Sym e) : ∀ (t : List ℚ) (k : ℕ),
    |linVal t e k| ≤ ((sumAbs t : ℚ) : ℝ)
  | [], k => by simp [linVal, sumAbs]
  | a :: l, k => by
      have ih := linVal_bound he l (k + 1)
      have h1 : |((a : ℚ) : ℝ) * e k| ≤ ((qabs a : ℚ) : ℝ) := by
        rw [abs_mul, zqabs_cast]
        exact mul_le_of_le_one_right (abs_nonneg _) (he k)
      have e1 : linVal (a :: l) e k = ((a : ℚ) : ℝ) * e k + linVal l e (k + 1) := rfl
      rw [e1, sumAbs_cons_cast]
      exact le_trans (abs_add_le _ _) (by linarith)

theorem af_range : AFRange := by
  intro e v a he h
  have hl := linVal_bound he a.t 0
  have hA : |v - (((a.c : ℚ) : ℝ) + linVal a.t e 0)| ≤ ((a.r : ℚ) : ℝ) := h
  have hr : 0 ≤ ((a.r : ℚ) : ℝ) := le_trans (abs_nonneg _) hA
  have hr' : 0 ≤ a.r := by exact_mod_cast hr
  have hmag : ((a.mag : ℚ) : ℝ) = |((a.c : ℚ) : ℝ)| + (((sumAbs a.t : ℚ) : ℝ) + ((a.r : ℚ) : ℝ)) := by
    unfold AF.mag AF.dev
    push_cast
    rw [zqabs_cast]
  have hdev1 : (((a.c - a.dev : ℚ)) : ℝ) = ((a.c : ℚ) : ℝ) - (((sumAbs a.t : ℚ) : ℝ) + ((a.r : ℚ) : ℝ)) := by
    unfold AF.dev
    push_cast
    ring
  have hdev2 : (((a.c + a.dev : ℚ)) : ℝ) = ((a.c : ℚ) : ℝ) + (((sumAbs a.t : ℚ) : ℝ) + ((a.r : ℚ) : ℝ)) := by
    unfold AF.dev
    push_cast
    ring
  obtain ⟨h1, h2⟩ := abs_le.mp hA
  obtain ⟨h3, h4⟩ := abs_le.mp hl
  refine ⟨hr', ?_, ?_, ?_⟩
  · rw [hmag]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [le_abs_self ((a.c : ℚ) : ℝ), neg_abs_le ((a.c : ℚ) : ℝ)]
  · rw [hdev1]; linarith
  · rw [hdev2]; linarith

/-! ### linearity -/

theorem linVal_addL (e : ℕ → ℝ) : ∀ (s t : List ℚ) (k : ℕ),
    linVal (addL s t) e k = linVal s e k + linVal t e k
  | [], t, k => by
      have h : addL [] t = t := by cases t <;> rfl
      rw [h]; simp [linVal]
  | a :: s, [], k => by
      have h : addL (a :: s) [] = a :: s := rfl
      rw [h]; simp [linVal]
  | a :: s, b :: t, k => by
      have h : addL (a :: s) (b :: t) = (a + b) :: addL s t := rfl
      rw [h]
      have ih := linVal_addL e s t (k + 1)
      show (((a + b : ℚ)) : ℝ) * e k + linVal (addL s t) e (k + 1)
        = (((a : ℚ) : ℝ) * e k + linVal s e (k + 1)) + (((b : ℚ) : ℝ) * e k + linVal t e (k + 1))
      rw [ih]; push_cast; ring

theorem linVal_map (e : ℕ → ℝ) (q : ℚ) : ∀ (t : List ℚ) (k : ℕ),
    linVal (t.map (fun v => q * v)) e k = ((q : ℚ) : ℝ) * linVal t e k
  | [], k => by simp [linVal]
  | a :: t, k => by
      have ih := linVal_map e q t (k + 1)
      show (((q * a : ℚ)) : ℝ) * e k + linVal (t.map (fun v => q * v)) e (k + 1)
        = ((q : ℚ) : ℝ) * ((((a : ℚ) : ℝ)) * e k + linVal t e (k + 1))
      rw [ih]; push_cast; ring

theorem inAF_add {e : ℕ → ℝ} {v w : ℝ} {a b : AF} (h1 : InAF e v a) (h2 : InAF e w b) :
    InAF e (v + w) (a.add b) := by
  have h1' : |v - (((a.c : ℚ) : ℝ) + linVal a.t e 0)| ≤ ((a.r : ℚ) : ℝ) := h1
  have h2' : |w - (((b.c : ℚ) : ℝ) + linVal b.t e 0)| ≤ ((b.r : ℚ) : ℝ) := h2
  have h := zabs_add_pair h1' h2'
  show |v + w - ((((a.c + b.c : ℚ)) : ℝ) + linVal (addL a.t b.t) e 0)| ≤ (((a.r + b.r : ℚ)) : ℝ)
  rw [linVal_addL]
  push_cast
  have e1 : v + w - (((a.c : ℚ) : ℝ) + ((b.c : ℚ) : ℝ) + (linVal a.t e 0 + linVal b.t e 0))
      = (v + w) - ((((a.c : ℚ) : ℝ) + linVal a.t e 0) + (((b.c : ℚ) : ℝ) + linVal b.t e 0)) := by ring
  rw [e1]
  exact h

theorem inAF_scale {e : ℕ → ℝ} {v : ℝ} {a : AF} (q : ℚ) (h : InAF e v a) :
    InAF e (((q : ℚ) : ℝ) * v) (AF.scale q a) := by
  have h' : |v - (((a.c : ℚ) : ℝ) + linVal a.t e 0)| ≤ ((a.r : ℚ) : ℝ) := h
  show |((q : ℚ) : ℝ) * v - ((((q * a.c : ℚ)) : ℝ) + linVal (a.t.map (fun v => q * v)) e 0)|
    ≤ (((qabs q * a.r : ℚ)) : ℝ)
  rw [linVal_map]
  have e1 : ((q : ℚ) : ℝ) * v - ((((q * a.c : ℚ)) : ℝ) + ((q : ℚ) : ℝ) * linVal a.t e 0)
      = ((q : ℚ) : ℝ) * (v - (((a.c : ℚ) : ℝ) + linVal a.t e 0)) := by push_cast; ring
  rw [e1, abs_mul]
  push_cast
  rw [zqabs_cast]
  exact mul_le_mul_of_nonneg_left h' (abs_nonneg _)

theorem shift_af : ShiftAF := by
  intro e v v' a c r h hv
  have h' : |v - (((a.c : ℚ) : ℝ) + linVal a.t e 0)| ≤ ((a.r : ℚ) : ℝ) := h
  show |v' - ((((a.c + c : ℚ)) : ℝ) + linVal a.t e 0)| ≤ (((a.r + r : ℚ)) : ℝ)
  push_cast
  have h3 := abs_add_le (v' - (v + ((c : ℚ) : ℝ))) (v - (((a.c : ℚ) : ℝ) + linVal a.t e 0))
  have e1 : v' - (v + ((c : ℚ) : ℝ)) + (v - (((a.c : ℚ) : ℝ) + linVal a.t e 0))
      = v' - (((a.c : ℚ) : ℝ) + ((c : ℚ) : ℝ) + linVal a.t e 0) := by ring
  rw [e1] at h3
  linarith

/-! ### lists of forms -/

theorem inAFs_nil {e : ℕ → ℝ} : InAFs e ([] : List ℝ) ([] : List AF) :=
  ⟨rfl, fun k hk => absurd hk (by simp)⟩

theorem inAFs_nil_left {e : ℕ → ℝ} {vs : List AF} (h : InAFs e ([] : List ℝ) vs) : vs = [] := by
  obtain ⟨hl, _⟩ := h
  cases vs with
  | nil => rfl
  | cons v vs => simp at hl

theorem inAFs_cons {e : ℕ → ℝ} {a : ℝ} {as : List ℝ} {v : AF} {vs : List AF}
    (h1 : InAF e a v) (h2 : InAFs e as vs) : InAFs e (a :: as) (v :: vs) := by
  obtain ⟨hl, hk⟩ := h2
  refine ⟨by simp [hl], ?_⟩
  intro k hk'
  cases k with
  | zero => simpa using h1
  | succ k =>
    have := hk k (by simpa using hk')
    simpa using this

theorem inAFs_cons_inv {e : ℕ → ℝ} {a : ℝ} {as : List ℝ} {v : AF} {vs : List AF}
    (h : InAFs e (a :: as) (v :: vs)) : InAF e a v ∧ InAFs e as vs := by
  obtain ⟨hl, hk⟩ := h
  refine ⟨?_, ?_⟩
  · have := hk 0 (by simp)
    simpa using this
  · refine ⟨by simpa using hl, ?_⟩
    intro k hk'
    have := hk (k + 1) (by simpa using hk')
    simpa using this

/-! ### embedding -/

theorem emb_af : EmbAF := by
  intro u η M fl hC δ hδ0 hδ1 row d hd hsm e
  have hs := zsmallQ_mem hsm
  have key := emb_sound u η M fl hC δ hδ0 hδ1 row d hd hsm
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨hl, hk⟩, _⟩ := key
    have hlen : (embIV δ row).length = row.length := by unfold embIV; simp
    refine ⟨by rw [hl, hlen]; simp, ?_⟩
    intro k hk'
    have hk2 : k < row.length := by omega
    have h1 := hk k hk'
    have e1 : (embIV δ row).getD k (0, 0) = (row.getD k 0, e0 δ) :=
      getD_map_lt (fun a => (a, e0 δ)) 0 (0, 0) row k hk2
    have e2 : (row.map (fun a => (⟨a, [], e0 δ⟩ : AF))).getD k ⟨0, [], 0⟩
        = ⟨row.getD k 0, [], e0 δ⟩ :=
      getD_map_lt (fun a => (⟨a, [], e0 δ⟩ : AF)) 0 _ row k hk2
    rw [e1] at h1
    rw [e2]
    have h1' := zinIV_iff.mp h1
    simpa [InAF, linVal] using h1'
  · intro a ha
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp ha
    have hbd := (key.2 (b, e0 δ) (List.mem_map.mpr ⟨b, hb, rfl⟩)).2
    have hbd' : qabs b + e0 δ ≤ 16 := hbd
    rw [← hab]
    show qabs b + (0 + e0 δ) ≤ 16
    linarith

/-! ### maxMag -/

theorem maxMag_aux (l : List AF) : ∀ m : ℚ, m ≤ l.foldl (fun m x => max m x.mag) m ∧
    ∀ a ∈ l, a.mag ≤ l.foldl (fun m x => max m x.mag) m := by
  induction l with
  | nil => intro m; simp
  | cons b l ih =>
    intro m
    obtain ⟨h1, h2⟩ := ih (max m b.mag)
    simp only [List.foldl_cons]
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with h3 | ha'
    · rw [h3]
      exact le_trans (le_max_right _ _) h1
    · exact h2 a ha'

theorem maxMag_nonneg (l : List AF) : 0 ≤ maxMag l := (maxMag_aux l 0).1

theorem le_maxMag {l : List AF} {a : AF} (h : a ∈ l) : a.mag ≤ maxMag l := (maxMag_aux l 0).2 a h

theorem maxMag_le_aux (B : ℚ) (l : List AF) : ∀ m : ℚ, m ≤ B → (∀ a ∈ l, a.mag ≤ B) →
    l.foldl (fun m x => max m x.mag) m ≤ B := by
  induction l with
  | nil => intro m hm _; simpa using hm
  | cons b l ih =>
    intro m hm hl
    simp only [List.foldl_cons]
    exact ih _ (max_le hm (hl b (by simp))) (fun a ha => hl a (by simp [ha]))

theorem maxMag_le {l : List AF} {B : ℚ} (hB : 0 ≤ B) (h : ∀ a ∈ l, a.mag ≤ B) : maxMag l ≤ B :=
  maxMag_le_aux B l 0 hB h

/-! ### dot -/

theorem wErr_mag (δ : ℝ) : ∀ (r : List ℚ) (xa : List AF), r.length = xa.length →
    wErr δ r (xa.map (fun _ => (0 : ℝ))) (xa.map (fun a => ((a.mag : ℚ) : ℝ)))
      = δ * ((sumMag xa : ℚ) : ℝ)
  | [], [], _ => by rw [List.map_nil, List.map_nil, zwErr_nl]; simp [sumMag]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: r, x :: xs, h => by
      have ih := wErr_mag δ r xs (by simpa using h)
      have e1 : wErr δ (a :: r) ((x :: xs).map (fun _ => (0 : ℝ)))
          ((x :: xs).map (fun a => ((a.mag : ℚ) : ℝ)))
          = |(a : ℝ)| * 0 + δ * (((x.mag : ℚ) : ℝ) + 0)
            + wErr δ r (xs.map (fun _ => (0 : ℝ))) (xs.map (fun a => ((a.mag : ℚ) : ℝ))) := rfl
      have e2 : ((sumMag (x :: xs) : ℚ) : ℝ) = ((x.mag : ℚ) : ℝ) + ((sumMag xs : ℚ) : ℝ) := by
        rw [show sumMag (x :: xs) = x.mag + sumMag xs from rfl, Rat.cast_add]
      rw [e1, ih, e2]; ring

theorem dotQ_in {e : ℕ → ℝ} : ∀ (r : List ℚ) (x : List ℝ) (xa : List AF), r.length = x.length →
    InAFs e x xa → InAF e (dotQ r x) (linAF r xa) := by
  intro r
  induction r with
  | nil =>
    intro x xa hl hx
    have hx0 : x = [] := by
      cases x with
      | nil => rfl
      | cons _ _ => simp at hl
    subst hx0
    have hxa : xa = [] := inAFs_nil_left hx
    subst hxa
    have e1 : dotQ [] [] = 0 := by simp [dotQ]
    rw [e1]
    show |(0 : ℝ) - (((0 : ℚ) : ℝ) + linVal [] e 0)| ≤ ((0 : ℚ) : ℝ)
    simp [linVal]
  | cons a r ih =>
    intro x xa hl hx
    cases x with
    | nil => simp at hl
    | cons v xs =>
      cases xa with
      | nil => exact absurd hx.1 (by simp)
      | cons w ws =>
        obtain ⟨h1, h2⟩ := inAFs_cons_inv hx
        have ih' := ih xs ws (by simpa using hl) h2
        have e1 : dotQ (a :: r) (v :: xs) = (a : ℝ) * v + dotQ r xs := by simp [dotQ]
        have e2 : linAF (a :: r) (w :: ws) = (AF.scale a w).add (linAF r ws) := rfl
        rw [e1, e2]
        exact inAF_add (inAF_scale a h1) ih'

theorem dot_af : DotAF := by
  intro u η M fl hC δ hδ0 hδ1 r x xa d hd hrx hr32 hsm e he hx hmag
  have hlenx : x.length = xa.length := hx.1
  have hW : maxAbs r ≤ 15 := zsmallQ_le hsm
  have hX16 : maxMag xa ≤ 16 := maxMag_le (by norm_num) hmag
  have hX0 := maxMag_nonneg xa
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 / 2 := zhalf δ hδ1
  have hM : (2 : ℝ) ^ 30 ≤ M := by
    have h1 := hC.M1
    have h2 : (2 : ℝ) ^ 30 ≤ 2 ^ 40 := by norm_num
    linarith
  have hWR : ((maxAbs r : ℚ) : ℝ) ≤ 15 := by exact_mod_cast hW
  have hXR : ((maxMag xa : ℚ) : ℝ) ≤ 16 := by exact_mod_cast hX16
  have hW0 : (0 : ℝ) ≤ ((maxAbs r : ℚ) : ℝ) := by exact_mod_cast zmaxAbs_nonneg r
  have hX0R : (0 : ℝ) ≤ ((maxMag xa : ℚ) : ℝ) := by exact_mod_cast hX0
  have hT : (((maxAbs r : ℚ) : ℝ) + 1) * (((maxMag xa : ℚ) : ℝ) + 0 + 1) ≤ 2 ^ 20 := by
    have h1 : (((maxAbs r : ℚ) : ℝ) + 1) * (((maxMag xa : ℚ) : ℝ) + 0 + 1) ≤ 16 * 17 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    have h2 : (16 : ℝ) * 17 ≤ 2 ^ 20 := by norm_num
    linarith
  have hrW : ∀ a ∈ r, |(a : ℝ)| ≤ ((maxAbs r : ℚ) : ℝ) := by
    intro a ha
    have h3 := zle_maxAbs ha
    have h4 : ((qabs a : ℚ) : ℝ) ≤ ((maxAbs r : ℚ) : ℝ) := by exact_mod_cast h3
    rwa [zqabs_cast] at h4
  have hxk : ∀ k, k < x.length →
      |x.getD k 0| ≤ (((xa.getD k ⟨0, [], 0⟩).mag : ℚ) : ℝ) := by
    intro k hk'
    exact (af_range e _ _ he (hx.2 k hk')).2.1
  have hCL : CloseL x x (xa.map (fun _ => (0 : ℝ))) (xa.map (fun a => ((a.mag : ℚ) : ℝ))) := by
    refine ⟨rfl, by simp [hlenx], by simp [hlenx], ?_⟩
    intro k hk'
    have hk2 : k < xa.length := by omega
    have e1 : (xa.map (fun _ => (0 : ℝ))).getD k 0 = 0 := by
      rw [getD_map_lt (fun _ : AF => (0 : ℝ)) ⟨0, [], 0⟩ 0 xa k hk2]
    have e2 : (xa.map (fun a : AF => ((a.mag : ℚ) : ℝ))).getD k 0
        = (((xa.getD k ⟨0, [], 0⟩).mag : ℚ) : ℝ) :=
      getD_map_lt (fun a : AF => ((a.mag : ℚ) : ℝ)) ⟨0, [], 0⟩ 0 xa k hk2
    rw [e1, e2]
    refine ⟨by simp, hxk k hk'⟩
  have hb : ∀ k, k < x.length →
      (xa.map (fun _ => (0 : ℝ))).getD k 0 ≤ 0 ∧
      (xa.map (fun a => ((a.mag : ℚ) : ℝ))).getD k 0 ≤ ((maxMag xa : ℚ) : ℝ) := by
    intro k hk'
    have hk2 : k < xa.length := by omega
    have e1 : (xa.map (fun _ => (0 : ℝ))).getD k 0 = 0 := by
      rw [getD_map_lt (fun _ : AF => (0 : ℝ)) ⟨0, [], 0⟩ 0 xa k hk2]
    have e2 : (xa.map (fun a : AF => ((a.mag : ℚ) : ℝ))).getD k 0
        = (((xa.getD k ⟨0, [], 0⟩).mag : ℚ) : ℝ) :=
      getD_map_lt (fun a : AF => ((a.mag : ℚ) : ℝ)) ⟨0, [], 0⟩ 0 xa k hk2
    rw [e1, e2]
    refine ⟨le_refl _, ?_⟩
    have h3 := le_maxMag (zgetD_mem' (⟨0, [], 0⟩ : AF) xa k hk2)
    exact_mod_cast h3
  have key := ardot_near_w u η M (δ : ℝ) fl hC.rnd hC.u0 hC.u1 hC.h0 hC.h1 hδR0
    (by linarith) r x x (xa.map (fun _ => (0 : ℝ))) (xa.map (fun a => ((a.mag : ℚ) : ℝ))) d
    ((maxAbs r : ℚ) : ℝ) ((maxMag xa : ℚ) : ℝ) 0
    hrx hr32 hCL hb hd hrW hW0 hX0R (le_refl 0) hT hM
  obtain ⟨k1, _⟩ := key
  have hrxa : r.length = xa.length := by omega
  rw [wErr_mag (δ : ℝ) r xa hrxa] at k1
  have hin := dotQ_in (e := e) r x xa hrx hx
  have hR : (((δ * sumMag xa + (r.length : ℚ) * (maxAbs r + 1) * (maxMag xa + 1) / 2 ^ 16
      + 1 / 2 ^ 100 : ℚ)) : ℝ)
      = (δ : ℝ) * ((sumMag xa : ℚ) : ℝ)
        + (r.length : ℝ) * (((maxAbs r : ℚ) : ℝ) + 1) * (((maxMag xa : ℚ) : ℝ) + 0 + 1) / 2 ^ 16
        + 1 / 2 ^ 100 := by
    push_cast
    ring
  unfold dotAF
  refine shift_af e _ _ (linAF r xa) 0 _ hin ?_
  rw [hR]
  have h0 : ((0 : ℚ) : ℝ) = 0 := Rat.cast_zero
  rw [h0, add_zero]
  exact k1

end Lane4.Case
