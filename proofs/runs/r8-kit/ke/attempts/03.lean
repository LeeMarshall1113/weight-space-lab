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


/-! ### magnitude of shifted forms -/

theorem mag_shift (a : AF) (c e : ℚ) : (a.shift c e).mag = qabs (a.c + c) + (a.dev + e) := by
  show qabs (a.c + c) + (sumAbs a.t + (a.r + e)) = qabs (a.c + c) + ((sumAbs a.t + a.r) + e)
  ring

theorem abs_le_of_small {e : ℕ → ℝ} (he : Sym e) {v : ℝ} {a : AF} (h : InAF e v a)
    (hm : a.mag ≤ 15) : |v| ≤ 15 := by
  have h1 := (af_range e v a he h).2.1
  have h2 : ((a.mag : ℚ) : ℝ) ≤ 15 := by exact_mod_cast hm
  linarith

/-! ### affine map -/

theorem aff_aux {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) {δ : ℚ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (x : List ℝ) (xa : List AF) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ)
    (hdW : ∀ i k, |dW i k| ≤ (δ : ℝ)) (hdb : ∀ i, |db i| ≤ (δ : ℝ)) (hx32 : x.length ≤ 32)
    (e : ℕ → ℝ) (he : Sym e) (hx : InAFs e x xa) (hmag : ∀ a ∈ xa, a.mag ≤ 16) :
    ∀ (A : List (List ℚ)) (b : List ℚ) (i : ℕ), (∀ r ∈ A, r.length = x.length) →
      (∀ r ∈ A, smallQ r = true) → (∀ c ∈ b, qabs c ≤ 15) →
      (∀ a ∈ affAF δ A b xa, AF.small a = true) →
      InAFs e (araffine fl A b x dW db i) (affAF δ A b xa) := by
  intro A
  induction A with
  | nil =>
    intro b i _ _ _ _
    have e1 : affAF δ [] b xa = [] := by cases b <;> rfl
    have e2 : araffine fl [] b x dW db i = [] := by cases b <;> rfl
    rw [e1, e2]
    exact inAFs_nil
  | cons r A ih =>
    intro b i hr hs hb hsm
    cases b with
    | nil =>
      have e1 : affAF δ (r :: A) [] xa = [] := rfl
      have e2 : araffine fl (r :: A) [] x dW db i = [] := rfl
      rw [e1, e2]
      exact inAFs_nil
    | cons c b =>
      have e1 : affAF δ (r :: A) (c :: b) xa
          = ((dotAF δ r xa).shift c (e0 δ + rnd)) :: affAF δ A b xa := rfl
      have e2 : araffine fl (r :: A) (c :: b) x dW db i
          = fl (ardot fl r x (dW i) 0 0 + asw fl c (db i)) :: araffine fl A b x dW db (i + 1) :=
        rfl
      have hsm' : ∀ v ∈ (((dotAF δ r xa).shift c (e0 δ + rnd)) :: affAF δ A b xa),
          AF.small v = true := hsm
      have hsm0s := hsm' ((dotAF δ r xa).shift c (e0 δ + rnd)) (by simp)
      have hsm0 : ((dotAF δ r xa).shift c (e0 δ + rnd)).mag ≤ 15 := of_decide_eq_true hsm0s
      have hsm1 : ∀ v ∈ affAF δ A b xa, AF.small v = true :=
        fun v hv => hsm' v (List.mem_cons_of_mem _ hv)
      have ih1 := ih b (i + 1) (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
        (fun r' h' => hs r' (List.mem_cons_of_mem _ h'))
        (fun c' h' => hb c' (List.mem_cons_of_mem _ h')) hsm1
      have hrx : r.length = x.length := hr r (by simp)
      have hin := dot_af u η M fl hC δ hδ0 hδ1 r x xa (dW i) (hdW i) hrx (by omega)
        (hs r (by simp)) e he hx hmag
      have hasw := zasw_e0 hC hδ0 hδ1 (hb c (by simp)) (hdb i)
      have hdiff : ardot fl r x (dW i) 0 0 + asw fl c (db i)
            - (ardot fl r x (dW i) 0 0 + ((c : ℚ) : ℝ)) = asw fl c (db i) - (c : ℝ) := by ring
      have hz : InAF e (ardot fl r x (dW i) 0 0 + asw fl c (db i))
          ((dotAF δ r xa).shift c (e0 δ)) := by
        refine shift_af e _ _ (dotAF δ r xa) c (e0 δ) hin ?_
        rw [hdiff]
        exact hasw
      have hm1 := mag_shift (dotAF δ r xa) c (e0 δ + rnd)
      have hm2 := mag_shift (dotAF δ r xa) c (e0 δ)
      have hrp := zrnd_pos
      have hmz : ((dotAF δ r xa).shift c (e0 δ)).mag ≤ 15 := by linarith
      have hb15 := abs_le_of_small he hz hmz
      have hy : |ardot fl r x (dW i) 0 0 + asw fl c (db i)
          - (ardot fl r x (dW i) 0 0 + ((c : ℚ) : ℝ))| ≤ ((e0 δ : ℚ) : ℝ) := by
        rw [hdiff]
        exact hasw
      have hrn := zrnd_step hC hy hb15
      have hfin : |fl (ardot fl r x (dW i) 0 0 + asw fl c (db i))
          - (ardot fl r x (dW i) 0 0 + ((c : ℚ) : ℝ))| ≤ ((e0 δ + rnd : ℚ) : ℝ) := by
        rw [Rat.cast_add, zrnd_real]
        exact hrn
      have hr1 := shift_af e _ _ (dotAF δ r xa) c (e0 δ + rnd) hin hfin
      rw [e1, e2]
      exact inAFs_cons hr1 ih1

theorem aff_af : AffAF := by
  intro u η M fl hC δ hδ0 hδ1 A b x xa dW db hdW hdb hr hx32 hAb hsA hsb e he hx hmag hall
  exact aff_aux hC hδ0 hδ1 x xa dW db hdW hdb hx32 e he hx hmag A b 0 hr (zsmallM_mem hsA)
    (zsmallQ_mem hsb) (List.all_eq_true.mp hall)

/-! ### addition -/

theorem add_aux {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (e : ℕ → ℝ) (he : Sym e) :
    ∀ (x y : List ℝ) (a b : List AF), InAFs e x a → InAFs e y b →
      (∀ v ∈ addAF a b, AF.small v = true) → InAFs e (radd fl x y) (addAF a b) := by
  intro x
  induction x with
  | nil =>
    intro y a b ha hb _
    have h0 := inAFs_nil_left ha
    subst h0
    have e1 : radd fl [] y = [] := by cases y <;> rfl
    have e2 : addAF [] b = [] := by cases b <;> rfl
    rw [e1, e2]
    exact inAFs_nil
  | cons x0 x ih =>
    intro y a b ha hb hsm
    cases a with
    | nil => exact absurd ha.1 (by simp)
    | cons u a =>
      cases y with
      | nil =>
        have h0 := inAFs_nil_left hb
        subst h0
        have e1 : radd fl (x0 :: x) [] = [] := rfl
        have e2 : addAF (u :: a) [] = [] := rfl
        rw [e1, e2]
        exact inAFs_nil
      | cons y0 y =>
        cases b with
        | nil => exact absurd hb.1 (by simp)
        | cons w b =>
          obtain ⟨ha1, ha2⟩ := inAFs_cons_inv ha
          obtain ⟨hb1, hb2⟩ := inAFs_cons_inv hb
          have e1 : radd fl (x0 :: x) (y0 :: y) = fl (x0 + y0) :: radd fl x y := rfl
          have e2 : addAF (u :: a) (w :: b) = ((u.add w).shift 0 rnd) :: addAF a b := rfl
          have hsm' : ∀ v ∈ (((u.add w).shift 0 rnd) :: addAF a b), AF.small v = true := hsm
          have hs0 := hsm' ((u.add w).shift 0 rnd) (by simp)
          have hm0 : ((u.add w).shift 0 rnd).mag ≤ 15 := of_decide_eq_true hs0
          have hsm1 : ∀ v ∈ addAF a b, AF.small v = true :=
            fun v hv => hsm' v (List.mem_cons_of_mem _ hv)
          have ih1 := ih y a b ha2 hb2 hsm1
          have hin := inAF_add ha1 hb1
          have hm1 := mag_shift (u.add w) 0 rnd
          have hq : qabs ((u.add w).c + 0) = qabs (u.add w).c := by rw [add_zero]
          have hrp := zrnd_pos
          have hmz : (u.add w).mag ≤ 15 := by
            show qabs (u.add w).c + (u.add w).dev ≤ 15
            linarith
          have hb15 := abs_le_of_small he hin hmz
          have hrn := zrnd_step hC (y := x0 + y0) (t := x0 + y0) (e := 0) (by simp) hb15
          have hfin : |fl (x0 + y0) - ((x0 + y0) + (((0 : ℚ)) : ℝ))| ≤ ((rnd : ℚ) : ℝ) := by
            rw [Rat.cast_zero, add_zero, zrnd_real]
            linarith
          have hr1 := shift_af e _ _ (u.add w) 0 rnd hin hfin
          rw [e1, e2]
          exact inAFs_cons hr1 ih1

theorem add_af : AddAF := by
  intro u η M fl hC x y a b e he hx hy hall
  exact add_aux hC e he x y a b hx hy (List.all_eq_true.mp hall)

/-! ### relu -/

theorem dnB_nonneg (b : ℕ) {x : ℚ} (hx : 0 ≤ x) : 0 ≤ dnB b x := by
  unfold dnB
  have h1 : 0 ≤ x.num := Rat.num_nonneg.mpr hx
  have h2 : (0 : ℤ) ≤ (x.num * 2 ^ b) / (x.den : ℤ) :=
    Int.ediv_nonneg (mul_nonneg h1 (by positivity)) (by positivity)
  have h3 : (0 : ℚ) ≤ (((x.num * 2 ^ b) / (x.den : ℤ) : ℤ) : ℚ) := by exact_mod_cast h2
  exact div_nonneg h3 (by positivity)

theorem dnB_le (b : ℕ) (x : ℚ) : dnB b x ≤ x := by
  unfold dnB
  have hd : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
  have h1 : (x.num * 2 ^ b) / (x.den : ℤ) * (x.den : ℤ) ≤ x.num * 2 ^ b :=
    Int.ediv_mul_le _ (ne_of_gt hd)
  have h2 : ((((x.num * 2 ^ b) / (x.den : ℤ) : ℤ)) : ℚ) * (x.den : ℚ) ≤ (x.num : ℚ) * 2 ^ b := by
    exact_mod_cast h1
  have hx' : x * (x.den : ℚ) = x.num := Rat.mul_den_eq_num x
  have hdq : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.den_pos
  have h3 : (x * 2 ^ b) * (x.den : ℚ) = (x.num : ℚ) * 2 ^ b := by
    rw [mul_right_comm, hx']
  have h4 : ((((x.num * 2 ^ b) / (x.den : ℤ) : ℤ)) : ℚ) * (x.den : ℚ) ≤ (x * 2 ^ b) * (x.den : ℚ) := by
    rw [h3]; exact h2
  have h5 := le_of_mul_le_mul_right h4 hdq
  rw [div_le_iff₀ (by positivity)]
  exact h5

theorem relu_mid (v lo hi lam : ℝ) (hlo : lo ≤ v) (hhi : v ≤ hi) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    0 ≤ Lane4.relu v - lam * v ∧ Lane4.relu v - lam * v ≤ max (-(lam * lo)) ((1 - lam) * hi) := by
  have hr : Lane4.relu v = max v 0 := rfl
  rcases le_or_gt 0 v with hv | hv
  · have h2 : Lane4.relu v = v := by rw [hr]; exact max_eq_left hv
    rw [h2]
    refine ⟨by nlinarith [mul_nonneg (sub_nonneg.2 h1) hv], le_trans ?_ (le_max_right _ _)⟩
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hhi)]
  · have h2 : Lane4.relu v = 0 := by rw [hr]; exact max_eq_right hv.le
    rw [h2]
    refine ⟨by nlinarith [mul_nonneg h0 (neg_nonneg.2 hv.le)], le_trans ?_ (le_max_left _ _)⟩
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hlo)]

theorem neg_le_qabs' (a : ℚ) : -a ≤ qabs a := by
  unfold qabs
  split_ifs with h
  · exact le_refl _
  · push_neg at h; linarith

theorem relu_small (c D lam mu : ℚ) (hD : 0 ≤ D) (hlo : c - D < 0) (hhi : 0 < c + D)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hlam : lam * ((c + D) - (c - D)) ≤ c + D)
    (hmag : qabs c + D ≤ 15)
    (hmu : mu = max (-(lam * (c - D))) ((1 - lam) * (c + D)) / 2) :
    qabs (lam * c + mu) + (lam * D + mu) ≤ 15 := by
  have hc1 := zle_qabs c
  have hc2 := neg_le_qabs' c
  rcases le_or_gt 0 (lam * c + mu) with hp | hp
  · rw [zqabs_of_nonneg hp]
    rw [hmu]
    rcases le_total (-(lam * (c - D))) ((1 - lam) * (c + D)) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  · have : qabs (lam * c + mu) = -(lam * c + mu) := by
      unfold qabs; rw [if_pos hp]
    rw [this]
    have h2 : lam * (D - c) ≤ D - c := by
      nlinarith [mul_nonneg (sub_nonneg.2 hl1) (by linarith : (0 : ℚ) ≤ D - c)]
    nlinarith

def lamOf (a : AF) : ℚ := dnB 20 ((a.c + a.dev) / ((a.c + a.dev) - (a.c - a.dev)))
def muOf (a : AF) : ℚ :=
  max (-(lamOf a * (a.c - a.dev))) ((1 - lamOf a) * (a.c + a.dev)) / 2

theorem reluAF_mid (a : AF) (h1 : ¬ 0 ≤ a.c - a.dev) (h2 : ¬ a.c + a.dev ≤ 0) :
    reluAF a = (AF.scale (lamOf a) a).shift (muOf a) (muOf a) := by
  simp [reluAF, lamOf, muOf, h1, h2]

theorem reluAF_pos (a : AF) (h1 : 0 ≤ a.c - a.dev) : reluAF a = a := by
  unfold reluAF
  simp [h1]

theorem reluAF_neg (a : AF) (h1 : ¬ 0 ≤ a.c - a.dev) (h2 : a.c + a.dev ≤ 0) :
    reluAF a = ⟨0, [], 0⟩ := by
  unfold reluAF
  simp [h1, h2]

theorem qabs_mul (q a : ℚ) : qabs (q * a) = qabs q * qabs a := by
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_mul, zqabs_cast, zqabs_cast, zqabs_cast, Rat.cast_mul]
  exact abs_mul _ _

theorem sumAbs_map (q : ℚ) : ∀ t : List ℚ, sumAbs (t.map (fun v => q * v)) = qabs q * sumAbs t
  | [] => by show (0 : ℚ) = qabs q * 0; ring
  | a :: t => by
      have ih := sumAbs_map q t
      show qabs (q * a) + sumAbs (t.map (fun v => q * v)) = qabs q * (qabs a + sumAbs t)
      rw [ih, qabs_mul]; ring

theorem zero_form_small : AF.small ⟨0, [], 0⟩ = true := by
  apply decide_eq_true
  show qabs 0 + (0 + 0) ≤ 15
  have : qabs (0 : ℚ) = 0 := zqabs_of_nonneg le_rfl
  rw [this]; norm_num

theorem relu_one {e : ℕ → ℝ} (he : Sym e) {v : ℝ} {a : AF} (h : InAF e v a)
    (hs : AF.small a = true) :
    InAF e (Lane4.relu v) (reluAF a) ∧ AF.small (reluAF a) = true := by
  obtain ⟨hr, hvm, hlo, hhi⟩ := af_range e v a he h
  have hmag : a.mag ≤ 15 := of_decide_eq_true hs
  have hmag' : qabs a.c + a.dev ≤ 15 := hmag
  by_cases h1 : 0 ≤ a.c - a.dev
  · rw [reluAF_pos a h1]
    have h0 : (0 : ℝ) ≤ v := by
      have : (0 : ℝ) ≤ (((a.c - a.dev : ℚ)) : ℝ) := by exact_mod_cast h1
      linarith
    have : Lane4.relu v = v := max_eq_left h0
    rw [this]
    exact ⟨h, hs⟩
  by_cases h2 : a.c + a.dev ≤ 0
  · rw [reluAF_neg a h1 h2]
    have h0 : v ≤ 0 := by
      have : (((a.c + a.dev : ℚ)) : ℝ) ≤ 0 := by exact_mod_cast h2
      linarith
    have : Lane4.relu v = 0 := max_eq_right h0
    rw [this]
    refine ⟨?_, zero_form_small⟩
    show |(0 : ℝ) - (((0 : ℚ) : ℝ) + linVal [] e 0)| ≤ ((0 : ℚ) : ℝ)
    simp [linVal]
  · have hlo0 : a.c - a.dev < 0 := not_le.mp h1
    have hhi0 : 0 < a.c + a.dev := not_le.mp h2
    rw [reluAF_mid a h1 h2]
    have hD : 0 ≤ a.dev := by
      show 0 ≤ sumAbs a.t + a.r
      have := sumAbs_nonneg a.t
      linarith
    have hden : 0 < (a.c + a.dev) - (a.c - a.dev) := by linarith
    have hX0 : 0 ≤ (a.c + a.dev) / ((a.c + a.dev) - (a.c - a.dev)) := div_nonneg hhi0.le hden.le
    have hX1 : (a.c + a.dev) / ((a.c + a.dev) - (a.c - a.dev)) ≤ 1 := by
      rw [div_le_one hden]; linarith
    have hl0 : 0 ≤ lamOf a := dnB_nonneg 20 hX0
    have hlX : lamOf a ≤ (a.c + a.dev) / ((a.c + a.dev) - (a.c - a.dev)) := dnB_le 20 _
    have hl1 : lamOf a ≤ 1 := le_trans hlX hX1
    have hlam : lamOf a * ((a.c + a.dev) - (a.c - a.dev)) ≤ a.c + a.dev := by
      calc lamOf a * ((a.c + a.dev) - (a.c - a.dev))
          ≤ ((a.c + a.dev) / ((a.c + a.dev) - (a.c - a.dev))) * ((a.c + a.dev) - (a.c - a.dev)) :=
            mul_le_mul_of_nonneg_right hlX hden.le
        _ = a.c + a.dev := div_mul_cancel₀ _ hden.ne'
    constructor
    · have hl0R : (0 : ℝ) ≤ ((lamOf a : ℚ) : ℝ) := by exact_mod_cast hl0
      have hl1R : ((lamOf a : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hl1
      have hmid := relu_mid v _ _ _ hlo hhi hl0R hl1R
      have hmu : ((muOf a : ℚ) : ℝ)
          = max (-(((lamOf a : ℚ) : ℝ) * (((a.c - a.dev : ℚ)) : ℝ)))
              ((1 - ((lamOf a : ℚ) : ℝ)) * (((a.c + a.dev : ℚ)) : ℝ)) / 2 := by
        unfold muOf
        push_cast
        rfl
      refine shift_af e _ _ (AF.scale (lamOf a) a) (muOf a) (muOf a) (inAF_scale (lamOf a) h) ?_
      rw [hmu]
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith [hmid.1]
      · linarith [hmid.2]
    · have hdev : (AF.scale (lamOf a) a).dev = lamOf a * a.dev := by
        show sumAbs (a.t.map (fun v => lamOf a * v)) + qabs (lamOf a) * a.r
          = lamOf a * (sumAbs a.t + a.r)
        rw [sumAbs_map, zqabs_of_nonneg hl0]; ring
      have hm : ((AF.scale (lamOf a) a).shift (muOf a) (muOf a)).mag
          = qabs (lamOf a * a.c + muOf a) + (lamOf a * a.dev + muOf a) := by
        rw [mag_shift, hdev]
        try rfl
      apply decide_eq_true
      rw [hm]
      exact relu_small a.c a.dev (lamOf a) (muOf a) hD hlo0 hhi0 hl0 hl1 hlam hmag' rfl

theorem exists_idx {α : Type} : ∀ (l : List α) (a : α) (d : α), a ∈ l →
    ∃ k, k < l.length ∧ l.getD k d = a
  | [], a, d, h => by simp at h
  | b :: l, a, d, h => by
      rcases List.mem_cons.mp h with h1 | h1
      · exact ⟨0, by simp, by simp [h1]⟩
      · obtain ⟨k, hk, hk2⟩ := exists_idx l a d h1
        exact ⟨k + 1, by simpa using hk, by simpa using hk2⟩

theorem relu_af : ReluAF := by
  intro x xa e he hx hsm
  have hsm' := List.all_eq_true.mp hsm
  have hl : x.length = xa.length := hx.1
  refine ⟨?_, ?_⟩
  · refine ⟨by simp [hl], ?_⟩
    intro k hk'
    have hk1 : k < x.length := by simpa using hk'
    have hk2 : k < xa.length := by omega
    have e1 : (x.map Lane4.relu).getD k 0 = Lane4.relu (x.getD k 0) :=
      getD_map_lt Lane4.relu 0 0 x k hk1
    have e2 : (xa.map reluAF).getD k ⟨0, [], 0⟩ = reluAF (xa.getD k ⟨0, [], 0⟩) :=
      getD_map_lt reluAF ⟨0, [], 0⟩ _ xa k hk2
    rw [e1, e2]
    exact (relu_one he (hx.2 k hk1) (hsm' _ (zgetD_mem' _ xa k hk2))).1
  · apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨a, ha, hab⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, hka⟩ := exists_idx xa a ⟨0, [], 0⟩ ha
    have hk1 : k < x.length := by omega
    rw [← hab]
    rw [← hka]
    exact (relu_one he (hx.2 k hk1) (hsm' _ (zgetD_mem' _ xa k hk))).2

end Lane4.Case
