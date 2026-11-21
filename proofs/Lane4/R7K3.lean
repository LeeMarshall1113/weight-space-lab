/-
Lane 4, rung 7 kit module, assembled by tools/r7_assemble.py from kit case k3
(runs/r7-kit/k3): statements by the lane, proofs by a Sonnet doctor, checked by tools/check.py.
-/
import Lane4.R7B3

namespace Lane4.R7K3
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2

/-- THE HEAD LEMMA. A head that passes `headOK` against the interval table `E` of the
embedding rows returns, at every query position `i` of an input of any length:

* if `j` is the latest candidate position of the query (`Latest`), a vector inside
  `headOut ... (some (tok j))`: the head's value at the token of position `j`, widened by
  the softmax error;
* if no position the mask allows holds a candidate token, a vector inside
  `headOut ... none` (all zeros).

`x j` is the state at position `j` (the block's input), known to lie in row `tok j` of `E`;
`n` is the number of positions; the query's token is a real token (not BOS). -/
def HeadSound : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Ctx u η M fl → ExpM u η ex →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (E : List (List IV)) (cd : List Bool) (dd : ℕ),
  headOK δ E h cd = true → h.shapeOK dd = true → dd ≤ 24 →
  smallM h.A = true → smallM h.V = true → smallQ h.g = true → smallQ [h.gb] = true →
  (∀ row ∈ E, row.length = dd ∧ Bdd 16 row) →
  ∀ (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ) (dgb : ℝ),
  (∀ i k, |dA i k| ≤ (δ : ℝ)) → (∀ i k, |dV i k| ≤ (δ : ℝ)) → |dm| ≤ (δ : ℝ) →
  (∀ k, |dg k| ≤ (δ : ℝ)) → |dgb| ≤ (δ : ℝ) →
  ∀ (n : ℕ) (x : ℕ → Vec) (tok : ℕ → ℕ),
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 → 2 ^ 40 * (n : ℝ) ^ 2 ≤ M →
  (∀ j, j < n → tok j < E.length ∧ InIVs (x j) (E.getD (tok j) [])) →
  ∀ i, i < n → 1 ≤ tok i →
    (∀ j, Latest h.mask cd tok n i j →
       InIVs (h.attn fl ex dA dV dm dg dgb n x i) (headOut δ E h cd (some (tok j))))
    ∧ ((∀ j ∈ cand h.mask n i, cd.getD (tok j) false = false) →
       InIVs (h.attn fl ex dA dV dm dg dgb n x i) (headOut δ E h cd none))
    ∧ (∀ p : Option ℕ, ∀ v ∈ headOut δ E h cd p, 0 ≤ v.2)

end Lane4.R7K3


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Lane4.R7K3
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2

/-! ### list helpers -/

theorem hs_mem_drop (E : List (List IV)) (t : ℕ) (h1 : 1 ≤ t) (ht : t < E.length) :
    E.getD t [] ∈ E.drop 1 := by
  cases E with
  | nil => simp at ht
  | cons e es =>
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [List.getD_cons_succ]
    exact zgetD_mem' [] es t' (by simpa using ht)

theorem hs_mem_zip : ∀ (E : List (List IV)) (cd : List Bool), cd.length = E.length →
    ∀ t, t < E.length → (E.getD t [], cd.getD t false) ∈ List.zip E cd
  | [], cd, _, t, ht => by simp at ht
  | e :: es, [], hl, t, _ => by simp at hl
  | e :: es, c :: cs, hl, 0, _ => by simp
  | e :: es, c :: cs, hl, t + 1, ht => by
      have ih := hs_mem_zip es cs (by simpa using hl) t (by simpa using ht)
      simp only [List.getD_cons_succ, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ ih

theorem hs_zipWith_all (f : List IV → Bool → Bool) : ∀ (E : List (List IV)) (cd : List Bool),
    cd.length = E.length → (List.zipWith f E cd).all id = true →
    ∀ t, t < E.length → f (E.getD t []) (cd.getD t false) = true
  | [], cd, _, _, t, ht => by simp at ht
  | e :: es, [], hl, _, t, _ => by simp at hl
  | e :: es, c :: cs, hl, hall, t, ht => by
      simp only [List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true, id_eq] at hall
      cases t with
      | zero => simpa using hall.1
      | succ t =>
        simp only [List.getD_cons_succ]
        exact hs_zipWith_all f es cs (by simpa using hl) hall.2 t (by simpa using ht)

theorem hs_or3 {P : Prop} [Decidable P] {a b : Bool} (h : (!a || !b || decide P) = true)
    (ha : a = true) (hb : b = true) : P := by
  subst ha; subst hb; simpa using h

theorem hs_or2 {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  subst ha; simpa using h

theorem hs_foldl_max {α : Type} (g : α → ℚ) : ∀ (L : List α) (m0 : ℚ),
    m0 ≤ L.foldl (fun m a => max m (g a)) m0 ∧
    ∀ a ∈ L, g a ≤ L.foldl (fun m a => max m (g a)) m0
  | [], m0 => by simp
  | b :: L, m0 => by
      have ih := hs_foldl_max g L (max m0 (g b))
      simp only [List.foldl_cons]
      refine ⟨le_trans (le_max_left _ _) ih.1, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_trans (le_max_right _ _) ih.1
      · exact ih.2 a ha

def hs_Bf (δ : ℚ) (E : List (List IV)) (cd : List Bool) (r : List ℚ) : ℚ :=
  ((List.zip E cd).filter (fun a => a.2)).foldl
    (fun m a => max m (qabs (dotIV δ r a.1).1 + (dotIV δ r a.1).2)) 0

theorem hs_Bf_nonneg (δ : ℚ) (E : List (List IV)) (cd : List Bool) (r : List ℚ) :
    0 ≤ hs_Bf δ E cd r :=
  (hs_foldl_max (fun a : List IV × Bool => qabs (dotIV δ r a.1).1 + (dotIV δ r a.1).2)
    ((List.zip E cd).filter (fun a => a.2)) 0).1

theorem hs_Bf_ge (δ : ℚ) (E : List (List IV)) (cd : List Bool) (hlen : cd.length = E.length)
    (r : List ℚ) {t : ℕ} (ht : t < E.length) (hcd : cd.getD t false = true) :
    qabs (dotIV δ r (E.getD t [])).1 + (dotIV δ r (E.getD t [])).2 ≤ hs_Bf δ E cd r := by
  have hmem : (E.getD t [], cd.getD t false) ∈ (List.zip E cd).filter (fun a => a.2) := by
    rw [List.mem_filter]
    exact ⟨hs_mem_zip E cd hlen t ht, by simpa using hcd⟩
  have key := (hs_foldl_max (fun a : List IV × Bool => qabs (dotIV δ r a.1).1 + (dotIV δ r a.1).2)
    ((List.zip E cd).filter (fun a => a.2)) 0).2 (E.getD t [], cd.getD t false) hmem
  unfold hs_Bf
  exact key

theorem hs_getD_rad {E : List (List IV)} {dd : ℕ}
    (hrows : ∀ row ∈ E, row.length = dd ∧ Bdd 16 row) (t : ℕ) :
    ∀ a ∈ E.getD t [], 0 ≤ a.2 := by
  by_cases ht : t < E.length
  · exact fun a ha => ((hrows _ (zgetD_mem' [] E t ht)).2 a ha).1
  · have : E.getD t [] = [] := by
      first
        | exact List.getD_eq_default _ _ (by omega)
        | simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show E.length ≤ t by omega)]
    rw [this]
    intro a ha
    simp at ha

theorem hs_cand_lt {m : Mask} {n i k : ℕ} (hi : i < n) (hk : k ∈ cand m n i) : k < n := by
  cases m <;> simp [cand] at hk <;> omega

theorem hs_cand_len (m : Mask) (n i : ℕ) (hi : i < n) : (cand m n i).length ≤ n := by
  cases m <;> simp [cand] <;> omega

theorem hs_shape {h : AHead} {dd : ℕ} (hs : h.shapeOK dd = true) :
    h.A.length = dd ∧ (∀ r ∈ h.A, r.length = dd) ∧ h.V.length = dd ∧
    (∀ r ∈ h.V, r.length = dd) ∧ h.g.length = dd := by
  unfold AHead.shapeOK rowsOK at hs
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨hA1, hA2⟩, hV1, hV2⟩, hg⟩ := hs
  exact ⟨hA1, hA2, hV1, hV2, hg⟩

/-! ### the checker's facts -/

theorem hs_headOK_open {δ : ℚ} {h : AHead} {E : List (List IV)} {cd : List Bool}
    (hok : headOK δ E h cd = true) :
    1 ≤ h.m ∧ h.m ≤ 1024 ∧ cd.length = E.length ∧
    (∀ t, t < E.length → gateDec δ h (E.getD t []) = some (cd.getD t false)) ∧
    (∀ B ∈ valBound δ E h cd, B ≤ 2 ^ 20) ∧
    (∀ tq, 1 ≤ tq → tq < E.length → ∀ t, t < E.length → cd.getD t false = true →
       scoreOK δ h (E.getD tq []) (E.getD t []) = true) ∧
    (∀ tq, 1 ≤ tq → tq < E.length → ∀ ta, ta < E.length → ∀ tb, tb < E.length →
       cd.getD ta false = true → cd.getD tb false = true →
       (scoreIV δ h (E.getD tq []) (E.getD tb [])).1
         - (scoreIV δ h (E.getD tq []) (E.getD ta [])).1
         + (scoreIV δ h (E.getD tq []) (E.getD ta [])).2
         + (scoreIV δ h (E.getD tq []) (E.getD tb [])).2 ≤ slopeRoom δ h) := by
  unfold headOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hm1⟩, hm2⟩, hlen⟩, hg⟩, hv⟩, hs⟩, hp⟩ := hok
  refine ⟨hm1, hm2, hlen, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have := hs_zipWith_all (fun x b => gateDec δ h x == some b) E cd hlen hg t ht
    simpa using this
  · intro B hB
    have := List.all_eq_true.mp hv B hB
    simpa using this
  · intro tq h1 htq t ht hcd
    have a1 := List.all_eq_true.mp hs (E.getD tq []) (hs_mem_drop E tq h1 htq)
    have a2 := List.all_eq_true.mp a1 (E.getD t [], cd.getD t false) (hs_mem_zip E cd hlen t ht)
    exact hs_or2 a2 hcd
  · intro tq h1 htq ta hta tb htb hca hcb
    have a1 := List.all_eq_true.mp hp (E.getD tq []) (hs_mem_drop E tq h1 htq)
    have a2 := List.all_eq_true.mp a1 (E.getD ta [], cd.getD ta false) (hs_mem_zip E cd hlen ta hta)
    have a3 := List.all_eq_true.mp a2 (E.getD tb [], cd.getD tb false) (hs_mem_zip E cd hlen tb htb)
    exact hs_or3 a3 hca hcb

/-! ### arithmetic -/

theorem hs_Sb {M m : ℝ} {n : ℕ} (hn : 1 ≤ n) (hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M) (hm1 : 1 ≤ m)
    (hm2 : m ≤ 1024) :
    2 ^ 12 * ((n : ℝ) + 1) ≤ M ∧
    2 * ((m + 2) * ((n : ℝ) + 1) + 1024 + (m + 2) / 256 + 1 / 4096) ≤ M ∧
    4 * (2 : ℝ) ^ 20 + 4 ≤ M ∧
    (m + 2) * ((n : ℝ) + 1) + 1024 ≤ M := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h40 : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  rw [h40] at hM
  rw [h12, h20]
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hmn : (m + 2) * ((n : ℝ) + 1) ≤ 1026 * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem hs_round_sum {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) {m n b c : ℝ}
    (hm : m + 2 ≤ 1026) (hm0 : 0 ≤ m + 2) (hn0 : 0 ≤ n)
    (hb : |b| ≤ (m + 2) * (n + 1)) (hc : |c| ≤ 1024) (hun : u * n ≤ 1 / 256)
    (hM : (m + 2) * (n + 1) + 1024 ≤ M) :
    |fl (b + c) - (b + c)| ≤ (m + 2) / 256 + 1 / 4096 := by
  have hy : |b + c| ≤ (m + 2) * (n + 1) + 1024 := le_trans (abs_add_le b c) (by linarith)
  have h1 := hr.abs hu0 hy hM
  have h24 : (2 : ℝ) ^ 24 = 16777216 := by norm_num
  rw [h24] at hu
  have hη' : η ≤ 1 / 1000000000000 := le_trans hη (by norm_num)
  have P1 : (m + 2) * (u * n) ≤ (m + 2) * (1 / 256) := mul_le_mul_of_nonneg_left hun hm0
  have P2 : (m + 2) * u ≤ 1026 * (1 / 16777216) := mul_le_mul hm hu hu0 (by norm_num)
  have P3 : u * 1024 ≤ 1024 * (1 / 16777216) := by linarith
  have e1 : u * ((m + 2) * (n + 1) + 1024) = (m + 2) * (u * n) + (m + 2) * u + u * 1024 := by
    ring
  rw [e1] at h1
  linarith

theorem hs_bias_abs {u η M δ : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : AHead) (dm : ℝ) (hdm : |dm| ≤ δ) (hm1 : (1 : ℝ) ≤ (h.m : ℝ)) (hm2 : (h.m : ℝ) ≤ 1024)
    (n i t : ℕ) (htn : t ≤ n) (hin : i ≤ n) (hun : u * (n : ℝ) ≤ 1 / 256)
    (hηn : η * (n : ℝ) ≤ 1 / 2 ^ 100) (hM : 2 ^ 12 * ((n : ℝ) + 1) ≤ M) :
    |h.bias fl dm i t| ≤ ((h.m : ℝ) + 2) * ((n : ℝ) + 1) := by
  have h24 : (2 : ℝ) ^ 24 = 16777216 := by norm_num
  have hη' : η ≤ 1 / 1000000000000 := le_trans hη (by norm_num)
  rw [h24] at hu
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htn' : (t : ℝ) ≤ n := by exact_mod_cast htn
  have hin' : (i : ℝ) ≤ n := by exact_mod_cast hin
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hM' : 4096 * ((n : ℝ) + 1) ≤ M := by
    have : (2 : ℝ) ^ 12 * ((n : ℝ) + 1) = 4096 * ((n : ℝ) + 1) := by norm_num
    linarith
  have hmM : (h.m : ℝ) + 1 ≤ M := by linarith
  have habs : |(h.m : ℝ)| = (h.m : ℝ) := abs_of_nonneg (by linarith)
  have hSb := asw_bound hr hu0 h.m hdm (by rw [habs]; linarith)
  rw [habs] at hSb
  have hbias : h.bias fl dm i t = fl (asw fl h.m dm * ((t : ℝ) - (i : ℝ))) := by
    simp [AHead.bias]
  rw [hbias]
  generalize asw fl h.m dm = S at hSb ⊢
  have hu1 : u * ((h.m : ℝ) + δ) ≤ u * ((h.m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hu0
  have hu2 : u * ((h.m : ℝ) + 1) ≤ (1 / 16777216) * ((h.m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hu (by linarith)
  have hS2 : |S| ≤ (h.m : ℝ) + 2 := by linarith
  have hti : |(t : ℝ) - (i : ℝ)| ≤ n := by
    rw [abs_le]; constructor <;> linarith
  have hm2' : (0 : ℝ) ≤ (h.m : ℝ) + 2 := by linarith
  have ha : |S * ((t : ℝ) - (i : ℝ))| ≤ ((h.m : ℝ) + 2) * n := by
    rw [abs_mul]; exact mul_le_mul hS2 hti (abs_nonneg _) hm2'
  have hBM : ((h.m : ℝ) + 2) * n ≤ M := by
    have := mul_le_mul_of_nonneg_right (by linarith : (h.m : ℝ) + 2 ≤ 1026) hn0
    linarith
  have hbound := hr.bound hu0 ha hBM
  have P4 : ((h.m : ℝ) + 2) * (u * n) ≤ ((h.m : ℝ) + 2) * (1 / 256) :=
    mul_le_mul_of_nonneg_left hun hm2'
  linarith [hbound, P4, hη', hη0]

/-! ### rows -/

theorem hs_rows_aux (fl ex : ℝ → ℝ) (dV : ℕ → ℕ → ℝ) (c : List ℕ) (s : ℕ → ℝ) (x : ℕ → Vec)
    (F : List ℚ → IV) : ∀ (V' : List (List ℚ)),
    (∀ r ∈ V', ∀ i', InIV (savg fl ex c s (fun k => ardot fl r (x k) (dV i') 0 0)) (F r)) →
    ∀ i0, InIVs (aattnRows fl ex V' dV c s x i0) (V'.map F)
  | [], _, i0 => by
      simp only [aattnRows, List.map_nil]
      exact zinIVs_nil
  | r :: M, hrow, i0 => by
      simp only [aattnRows, List.map_cons]
      exact zinIVs_cons (hrow r (by simp) i0)
        (hs_rows_aux fl ex dV c s x F M (fun r' hr' i' => hrow r' (by simp [hr']) i') (i0 + 1))

theorem hs_headOut_none (δ : ℚ) (E : List (List IV)) (h : AHead) (cd : List Bool) :
    headOut δ E h cd none = h.V.map (fun _ => ((0 : ℚ), (0 : ℚ))) := by
  first | rfl | simp [headOut]

theorem hs_headOut_some (δ : ℚ) (E : List (List IV)) (h : AHead) (cd : List Bool) (t : ℕ) :
    headOut δ E h cd (some t) = h.V.map (fun r =>
      ((dotIV δ r (E.getD t [])).1,
       (dotIV δ r (E.getD t [])).2 + hs_Bf δ E cd r / 100 + 1 / 2 ^ 90)) := by
  simp only [headOut, matIV, valBound, hs_Bf]
  generalize h.V = L
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.zipWith_cons_cons]
    rw [ih]

/-! ### the environment -/

structure HEnv (u η M : ℝ) (fl : ℝ → ℝ) (δ : ℚ) (h : AHead) (E : List (List IV))
    (cd : List Bool) (dd : ℕ) (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ) (dgb : ℝ) (n : ℕ)
    (x : ℕ → Vec) (tok : ℕ → ℕ) : Prop where
  ctx : Ctx u η M fl
  d0 : 0 ≤ δ
  d1 : δ ≤ 1 / 2
  shape : h.shapeOK dd = true
  dd24 : dd ≤ 24
  sA : smallM h.A = true
  sV : smallM h.V = true
  sg : smallQ h.g = true
  sgb : smallQ [h.gb] = true
  rows : ∀ row ∈ E, row.length = dd ∧ Bdd 16 row
  m1 : 1 ≤ h.m
  m2 : h.m ≤ 1024
  hlen : cd.length = E.length
  gate : ∀ t, t < E.length → gateDec δ h (E.getD t []) = some (cd.getD t false)
  val : ∀ B ∈ valBound δ E h cd, B ≤ 2 ^ 20
  sc : ∀ tq, 1 ≤ tq → tq < E.length → ∀ t, t < E.length → cd.getD t false = true →
       scoreOK δ h (E.getD tq []) (E.getD t []) = true
  pair : ∀ tq, 1 ≤ tq → tq < E.length → ∀ ta, ta < E.length → ∀ tb, tb < E.length →
       cd.getD ta false = true → cd.getD tb false = true →
       (scoreIV δ h (E.getD tq []) (E.getD tb [])).1
         - (scoreIV δ h (E.getD tq []) (E.getD ta [])).1
         + (scoreIV δ h (E.getD tq []) (E.getD ta [])).2
         + (scoreIV δ h (E.getD tq []) (E.getD tb [])).2 ≤ slopeRoom δ h
  hdA : ∀ i k, |dA i k| ≤ (δ : ℝ)
  hdV : ∀ i k, |dV i k| ≤ (δ : ℝ)
  hdm : |dm| ≤ (δ : ℝ)
  hdg : ∀ k, |dg k| ≤ (δ : ℝ)
  hdgb : |dgb| ≤ (δ : ℝ)
  hun : u * (n : ℝ) ≤ 1 / 256
  hηn : η * (n : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M
  hx : ∀ j, j < n → tok j < E.length ∧ InIVs (x j) (E.getD (tok j) [])

section
variable {u η M : ℝ} {fl : ℝ → ℝ} {δ : ℚ} {h : AHead} {E : List (List IV)} {cd : List Bool}
  {dd : ℕ} {dA dV : ℕ → ℕ → ℝ} {dm : ℝ} {dg : ℕ → ℝ} {dgb : ℝ} {n : ℕ} {x : ℕ → Vec}
  {tok : ℕ → ℕ}

theorem hs_const (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) :
    (1 : ℝ) ≤ (h.m : ℝ) ∧ (h.m : ℝ) ≤ 1024 ∧ (0 : ℝ) ≤ (δ : ℝ) ∧ (δ : ℝ) ≤ 1 := by
  refine ⟨by exact_mod_cast env.m1, by exact_mod_cast env.m2, by exact_mod_cast env.d0, ?_⟩
  have := zhalf δ env.d1
  linarith

theorem hs_gate (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) {k : ℕ} (hk : k < n) :
    h.gate fl dg dgb (x k) = 0 ↔ cd.getD (tok k) false = true := by
  obtain ⟨hqk, hxk⟩ := env.hx k hk
  have rk := env.rows _ (zgetD_mem' [] E _ hqk)
  obtain ⟨-, -, -, -, sg1⟩ := hs_shape env.shape
  have lk : (x k).length = dd := by rw [zinIVs_len hxk]; exact rk.1
  have hdd := env.dd24
  exact gate_sound u η M fl env.ctx δ env.d0 env.d1 h (x k) _ dg dgb env.hdg env.hdgb
    (by rw [sg1, lk]) (by omega) env.sg env.sgb hxk rk.2 _ (env.gate (tok k) hqk)

theorem hs_mem_cands (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) {i : ℕ}
    (hi : i < n) (k : ℕ) :
    k ∈ h.cands fl dg dgb n x i ↔ k ∈ cand h.mask n i ∧ cd.getD (tok k) false = true := by
  rw [AHead.mem_cands]
  constructor
  · rintro ⟨hk, hg⟩
    exact ⟨hk, (hs_gate env (hs_cand_lt hi hk)).mp hg⟩
  · rintro ⟨hk, hc⟩
    exact ⟨hk, (hs_gate env (hs_cand_lt hi hk)).mpr hc⟩

theorem hs_key_content (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) {i : ℕ}
    (hi : i < n) (hti : 1 ≤ tok i) {t : ℕ} (ht : t < n) (hcd : cd.getD (tok t) false = true) :
    InIV (pdot fl (x i) (armat fl h.A (x t) dA 0) 0)
      (scoreIV δ h (E.getD (tok i) []) (E.getD (tok t) []))
    ∧ 0 ≤ (scoreIV δ h (E.getD (tok i) []) (E.getD (tok t) [])).2
    ∧ |pdot fl (x i) (armat fl h.A (x t) dA 0) 0| ≤ 1024 := by
  obtain ⟨hqi, hxi⟩ := env.hx i hi
  obtain ⟨hqt, hxt⟩ := env.hx t ht
  have rq := env.rows _ (zgetD_mem' [] E _ hqi)
  have rt := env.rows _ (zgetD_mem' [] E _ hqt)
  obtain ⟨sA1, sA2, -, -, -⟩ := hs_shape env.shape
  have lq : (x i).length = dd := by rw [zinIVs_len hxi]; exact rq.1
  have lt' : (x t).length = dd := by rw [zinIVs_len hxt]; exact rt.1
  have hdd := env.dd24
  exact score_sound u η M fl env.ctx δ env.d0 env.d1 h (x i) (x t) _ _ dA env.hdA
    (fun r hr => by rw [sA2 r hr, lt']) (by omega) (by rw [sA1, lq]) (by omega) env.sA hxi
    rq.2 hxt rt.2 (env.sc (tok i) hti hqi (tok t) hqt hcd)

theorem hs_dot_key (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) {r : List ℚ}
    (hr : r ∈ h.V) {k : ℕ} (hk : k < n) (i' : ℕ) :
    InIV (ardot fl r (x k) (dV i') 0 0) (dotIV δ r (E.getD (tok k) []))
    ∧ 0 ≤ (dotIV δ r (E.getD (tok k) [])).2 := by
  obtain ⟨hqk, hxk⟩ := env.hx k hk
  have rk := env.rows _ (zgetD_mem' [] E _ hqk)
  obtain ⟨-, -, -, sV2, -⟩ := hs_shape env.shape
  have lk : (x k).length = dd := by rw [zinIVs_len hxk]; exact rk.1
  have hdd := env.dd24
  have hr' := zsmallM_mem env.sV r hr
  have hrl := sV2 r hr
  exact dot_sound u η M fl env.ctx δ env.d0 env.d1 r (x k) _ (dV i') (env.hdV i')
    (by rw [hrl, lk]) (by omega) hr' hxk rk.2

theorem hs_score_pack (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) {i : ℕ}
    (hi : i < n) (hti : 1 ≤ tok i) {t : ℕ} (ht : t < n) (hcd : cd.getD (tok t) false = true) :
    |h.bias fl dm i t| ≤ ((h.m : ℝ) + 2) * ((n : ℝ) + 1) ∧
    |h.score fl dA dm x i t - (h.bias fl dm i t + pdot fl (x i) (armat fl h.A (x t) dA 0) 0)|
      ≤ ((h.m : ℝ) + 2) / 256 + 1 / 4096 := by
  obtain ⟨-, -, kc3⟩ := hs_key_content env hi hti ht hcd
  have C := env.ctx
  obtain ⟨hm1R, hm2R, hδ0R, hδ1R⟩ := hs_const env
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hM12, -, -, hMS⟩ := hs_Sb hn1 env.hM hm1R hm2R
  have hb := hs_bias_abs C.rnd C.u0 C.u1 C.h0 C.h1 hδ0R hδ1R h dm env.hdm hm1R hm2R n i t
    ht.le hi.le env.hun env.hηn hM12
  refine ⟨hb, ?_⟩
  exact hs_round_sum C.rnd C.u0 C.u1 C.h0 C.h1 (m := (h.m : ℝ)) (n := (n : ℝ))
    (by linarith) (by linarith) (Nat.cast_nonneg n) hb kc3 env.hun hMS

theorem hs_score_abs (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) {i : ℕ}
    (hi : i < n) (hti : 1 ≤ tok i) {t : ℕ} (ht : t < n) (hcd : cd.getD (tok t) false = true) :
    |h.score fl dA dm x i t| ≤
      ((h.m : ℝ) + 2) * ((n : ℝ) + 1) + 1024 + ((h.m : ℝ) + 2) / 256 + 1 / 4096 := by
  obtain ⟨pb, pr⟩ := hs_score_pack env hi hti ht hcd
  obtain ⟨-, -, kc3⟩ := hs_key_content env hi hti ht hcd
  obtain ⟨y1, y2⟩ := abs_le.mp (le_trans
    (abs_add_le (h.bias fl dm i t) (pdot fl (x i) (armat fl h.A (x t) dA 0) 0))
    (add_le_add pb kc3))
  obtain ⟨r1, r2⟩ := abs_le.mp pr
  rw [abs_le]
  constructor <;> linarith

theorem hs_gap (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) {i : ℕ}
    (hi : i < n) (hti : 1 ≤ tok i) {j k : ℕ} (hkj : k < j) (hj : j < n)
    (hcj : cd.getD (tok j) false = true) (hck : cd.getD (tok k) false = true) :
    h.score fl dA dm x i k ≤ h.score fl dA dm x i j - 12 * (ndist j k : ℝ) := by
  have hkn : k < n := lt_trans hkj hj
  obtain ⟨kc1, kc2, kc3⟩ := hs_key_content env hi hti hkn hck
  obtain ⟨jc1, jc2, jc3⟩ := hs_key_content env hi hti hj hcj
  obtain ⟨pk1, pk2⟩ := hs_score_pack env hi hti hkn hck
  obtain ⟨pj1, pj2⟩ := hs_score_pack env hi hti hj hcj
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hm1R, hm2R, hδ0R, hδ1R⟩ := hs_const env
  obtain ⟨hM12, -, -, -⟩ := hs_Sb hn1 env.hM hm1R hm2R
  have C := env.ctx
  have hB := bias_gap u η M (δ : ℝ) fl C.rnd C.u0 C.u1 C.h0 C.h1 hδ0R hδ1R h dm env.hdm hm1R
    hm2R n i j k hkj hj.le hi.le env.hun env.hηn hM12
  have hB1 := hB.1
  obtain ⟨hqj, hxj⟩ := env.hx j hj
  obtain ⟨hqk, hxk⟩ := env.hx k hkn
  obtain ⟨hqi, hxi⟩ := env.hx i hi
  have hp := env.pair (tok i) hti hqi (tok j) hqj (tok k) hqk hcj hck
  have hp0 := env.pair (tok i) hti hqi (tok j) hqj (tok j) hqj hcj hcj
  set Sj := scoreIV δ h (E.getD (tok i) []) (E.getD (tok j) []) with hSj
  set Sk := scoreIV δ h (E.getD (tok i) []) (E.getD (tok k) []) with hSk
  have hpR : ((Sk.1 : ℚ) : ℝ) - ((Sj.1 : ℚ) : ℝ) + ((Sj.2 : ℚ) : ℝ) + ((Sk.2 : ℚ) : ℝ)
      ≤ ((slopeRoom δ h : ℚ) : ℝ) := by exact_mod_cast hp
  have hsl0 : (0 : ℚ) ≤ slopeRoom δ h := by linarith [hp0, jc2]
  have hsr : ((slopeRoom δ h : ℚ) : ℝ) = (h.m : ℝ) - (δ : ℝ) - 12 - 3 * ((h.m : ℝ) + 2) / 64 := by
    unfold slopeRoom Lane4.Cert.gap
    push_cast <;> ring
  have hsl0R : (0 : ℝ) ≤ ((slopeRoom δ h : ℚ) : ℝ) := by exact_mod_cast hsl0
  have hmd : 0 ≤ (h.m : ℝ) - (δ : ℝ) - 12 := by
    rw [hsr] at hsl0R
    linarith
  have hnd : (ndist j k : ℝ) = (j : ℝ) - (k : ℝ) := by
    rw [ndist_cast]
    apply abs_of_nonneg
    have : (k : ℝ) ≤ j := by exact_mod_cast hkj.le
    linarith
  have hJ : (1 : ℝ) ≤ (j : ℝ) - (k : ℝ) := by
    have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
    linarith
  have hprod := mul_nonneg hmd (by linarith : (0 : ℝ) ≤ (j : ℝ) - (k : ℝ) - 1)
  unfold InIV at kc1 jc1
  obtain ⟨k1, k2⟩ := abs_le.mp kc1
  obtain ⟨j1, j2⟩ := abs_le.mp jc1
  obtain ⟨a1, a2⟩ := abs_le.mp pj2
  obtain ⟨b1, b2⟩ := abs_le.mp pk2
  rw [hnd]
  linarith

theorem hs_Bf_bound (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) :
    ∀ r ∈ h.V, hs_Bf δ E cd r ≤ 2 ^ 20 := by
  intro r hr
  apply env.val
  unfold valBound
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

theorem hs_row_one (env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok) {ex : ℝ → ℝ}
    (hex : ExpM u η ex)
    {i : ℕ} (hi : i < n) (hti : 1 ≤ tok i) {j : ℕ} (hjc : j ∈ cand h.mask n i)
    (hjcd : cd.getD (tok j) false = true)
    (hlat : ∀ k ∈ cand h.mask n i, cd.getD (tok k) false = true → k ≤ j)
    {r : List ℚ} (hr : r ∈ h.V) (i' : ℕ) :
    InIV (savg fl ex (h.cands fl dg dgb n x i) (fun j => h.score fl dA dm x i j)
            (fun k => ardot fl r (x k) (dV i') 0 0))
      ((dotIV δ r (E.getD (tok j) [])).1,
       (dotIV δ r (E.getD (tok j) [])).2 + hs_Bf δ E cd r / 100 + 1 / 2 ^ 90) := by
  have C := env.ctx
  have hjn : j < n := hs_cand_lt hi hjc
  have hmem := hs_mem_cands env hi
  have hjC : j ∈ h.cands fl dg dgb n x i := (hmem j).mpr ⟨hjc, hjcd⟩
  have hnd := AHead.cands_nodup h fl dg dgb n x i
  have hlen : (h.cands fl dg dgb n x i).length ≤ n := by
    unfold AHead.cands
    exact le_trans (List.length_filter_le _ _) (hs_cand_len h.mask n i hi)
  obtain ⟨hm1R, hm2R, hδ0R, hδ1R⟩ := hs_const env
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hSM, hBM0, -⟩ := hs_Sb hn1 env.hM hm1R hm2R
  have hgap : ∀ k ∈ h.cands fl dg dgb n x i, k ≠ j →
      h.score fl dA dm x i k ≤ h.score fl dA dm x i j - 12 * (ndist j k : ℝ) := by
    intro k hk hkj
    obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
    exact hs_gap env hi hti (lt_of_le_of_ne (hlat k hk1 hk2) hkj) hjn hjcd hk2
  have hSb : ∀ k ∈ h.cands fl dg dgb n x i, |h.score fl dA dm x i k| ≤
      ((h.m : ℝ) + 2) * ((n : ℝ) + 1) + 1024 + ((h.m : ℝ) + 2) / 256 + 1 / 4096 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
    exact hs_score_abs env hi hti (hs_cand_lt hi hk1) hk2
  have hB0 : 0 ≤ hs_Bf δ E cd r := hs_Bf_nonneg δ E cd r
  have hB20 : hs_Bf δ E cd r ≤ 2 ^ 20 := hs_Bf_bound env r hr
  have hB20R : ((hs_Bf δ E cd r : ℚ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hB20
  have hB0R : (0 : ℝ) ≤ ((hs_Bf δ E cd r : ℚ) : ℝ) := by exact_mod_cast hB0
  have hBM : 4 * ((hs_Bf δ E cd r : ℚ) : ℝ) + 4 ≤ M := by linarith
  have hBk : ∀ k ∈ h.cands fl dg dgb n x i,
      |ardot fl r (x k) (dV i') 0 0| ≤ ((hs_Bf δ E cd r : ℚ) : ℝ) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
    have hkn := hs_cand_lt hi hk1
    obtain ⟨d1, d2⟩ := hs_dot_key env hr hkn i'
    have hqk := (env.hx k hkn).1
    have hb := hs_Bf_ge δ E cd env.hlen r hqk hk2
    have hbR : |(((dotIV δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)|
        + (((dotIV δ r (E.getD (tok k) [])).2 : ℚ) : ℝ) ≤ ((hs_Bf δ E cd r : ℚ) : ℝ) := by
      have : ((qabs (dotIV δ r (E.getD (tok k) [])).1 + (dotIV δ r (E.getD (tok k) [])).2 : ℚ) : ℝ)
          ≤ ((hs_Bf δ E cd r : ℚ) : ℝ) := by exact_mod_cast hb
      rw [Rat.cast_add, zqabs_cast] at this
      exact this
    unfold InIV at d1
    obtain ⟨e1, e2⟩ := abs_le.mp d1
    have f1 := neg_abs_le (((dotIV δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)
    have f2 := le_abs_self (((dotIV δ r (E.getD (tok k) [])).1 : ℚ) : ℝ)
    rw [abs_le]
    constructor <;> linarith
  have main := Lane4.R7K1.savg_near12 u η M fl ex C.rnd hex C.u0 C.u1 C.h0 C.h1
    (h.cands fl dg dgb n x i) hnd n hlen env.hun env.hηn
    (fun j => h.score fl dA dm x i j) (fun k => ardot fl r (x k) (dV i') 0 0) j hjC hgap
    (((h.m : ℝ) + 2) * ((n : ℝ) + 1) + 1024 + ((h.m : ℝ) + 2) / 256 + 1 / 4096) hSb hSM
    ((hs_Bf δ E cd r : ℚ) : ℝ) hBk hBM
  have hs1 : |savg fl ex (h.cands fl dg dgb n x i) (fun j => h.score fl dA dm x i j)
      (fun k => ardot fl r (x k) (dV i') 0 0) - ardot fl r (x j) (dV i') 0 0|
      ≤ ((hs_Bf δ E cd r : ℚ) : ℝ) / 100 + 1 / 2 ^ 90 := main.1
  obtain ⟨d1, d2⟩ := hs_dot_key env hr hjn i'
  unfold InIV at d1
  have hcast : (((dotIV δ r (E.getD (tok j) [])).2 + hs_Bf δ E cd r / 100 + 1 / 2 ^ 90 : ℚ) : ℝ)
      = (((dotIV δ r (E.getD (tok j) [])).2 : ℚ) : ℝ) + ((hs_Bf δ E cd r : ℚ) : ℝ) / 100
        + 1 / 2 ^ 90 := by
    push_cast <;> ring
  unfold InIV
  show |savg fl ex (h.cands fl dg dgb n x i) (fun j => h.score fl dA dm x i j)
      (fun k => ardot fl r (x k) (dV i') 0 0) - (((dotIV δ r (E.getD (tok j) [])).1 : ℚ) : ℝ)|
      ≤ (((dotIV δ r (E.getD (tok j) [])).2 + hs_Bf δ E cd r / 100 + 1 / 2 ^ 90 : ℚ) : ℝ)
  rw [hcast]
  obtain ⟨s1, s2⟩ := abs_le.mp hs1
  obtain ⟨e1, e2⟩ := abs_le.mp d1
  rw [abs_le]
  constructor <;> linarith

end

theorem head_sound : HeadSound := by
  intro u η M fl ex hC hex δ hδ0 hδ1 h E cd dd hok hsh hdd sA sV sg sgb hrows dA dV dm dg dgb
    hdA hdV hdm hdg hdgb n x tok hun hηn hM hx i hi hti
  obtain ⟨hm1, hm2, hlen, hgate, hval, hsc, hpair⟩ := hs_headOK_open hok
  have env : HEnv u η M fl δ h E cd dd dA dV dm dg dgb n x tok :=
    ⟨hC, hδ0, hδ1, hsh, hdd, sA, sV, sg, sgb, hrows, hm1, hm2, hlen, hgate, hval, hsc, hpair,
      hdA, hdV, hdm, hdg, hdgb, hun, hηn, hM, hx⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j hL
    obtain ⟨hjc, hjcd, hlat⟩ := hL
    unfold AHead.attn
    rw [hs_headOut_some]
    exact hs_rows_aux fl ex dV _ _ x _ h.V
      (fun r hr i' => hs_row_one env hex hi hti hjc hjcd hlat hr i') 0
  · intro hno
    have hc : h.cands fl dg dgb n x i = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro k hk
      obtain ⟨hk1, hk2⟩ := (hs_mem_cands env hi k).mp hk
      rw [hno k hk1] at hk2
      exact absurd hk2 (by simp)
    unfold AHead.attn
    rw [hc, hs_headOut_none]
    refine hs_rows_aux fl ex dV [] _ x (fun _ => ((0 : ℚ), (0 : ℚ))) h.V ?_ 0
    intro r _ i'
    have h0 : savg fl ex ([] : List ℕ) (fun j => h.score fl dA dm x i j)
        (fun k => ardot fl r (x k) (dV i') 0 0) = 0 := soft_zeros hC.rnd (by simp)
    unfold InIV
    rw [h0]
    simp
  · intro p v hv
    cases p with
    | none =>
      rw [hs_headOut_none, List.mem_map] at hv
      obtain ⟨r, _, rfl⟩ := hv
      simp
    | some t =>
      rw [hs_headOut_some, List.mem_map] at hv
      obtain ⟨r, hr, rfl⟩ := hv
      show 0 ≤ (dotIV δ r (E.getD t [])).2 + hs_Bf δ E cd r / 100 + 1 / 2 ^ 90
      have h1 := zdot_nonneg hδ0 r (E.getD t []) (hs_getD_rad hrows t)
      have h2 := hs_Bf_nonneg δ E cd r
      have h3 : (0 : ℚ) < 1 / 2 ^ 90 := by norm_num
      linarith

end Lane4.R7K3

