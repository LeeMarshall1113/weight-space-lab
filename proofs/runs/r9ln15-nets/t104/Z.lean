import R9LN15.t104.A

namespace Lane4.LNNetFile
open Lane4.RSeq (Vec)
open Lane4.Case Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.LNT Lane4.Bin32
open Lane4.Seq (Mask cand tokAt)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem st0 : (List.range task.ntok).all (fun k => caseOKLN (1/32768) (floorQ (1/32768)) lnetNB0 task cert 8 s0 (k + 1)) = true :=
  range5_all _ c0_1 c0_2 c0_3 c0_4 c0_5
theorem st1 : (List.range task.ntok).all (fun k => caseOKLN (1/32768) (floorQ (1/32768)) lnetNB0 task cert 8 s1 (k + 1)) = true :=
  range5_all _ c1_1 c1_2 c1_3 c1_4 c1_5
theorem st2 : (List.range task.ntok).all (fun k => caseOKLN (1/32768) (floorQ (1/32768)) lnetNB0 task cert 8 s2 (k + 1)) = true :=
  range5_all _ c2_1 c2_2 c2_3 c2_4 c2_5
theorem st3 : (List.range task.ntok).all (fun k => caseOKLN (1/32768) (floorQ (1/32768)) lnetNB0 task cert 8 s3 (k + 1)) = true :=
  range5_all _ c3_1 c3_2 c3_3 c3_4 c3_5
theorem st4 : (List.range task.ntok).all (fun k => caseOKLN (1/32768) (floorQ (1/32768)) lnetNB0 task cert 8 s4 (k + 1)) = true :=
  range5_all _ c4_1 c4_2 c4_3 c4_4 c4_5
theorem st5 : (List.range task.ntok).all (fun k => caseOKLN (1/32768) (floorQ (1/32768)) lnetNB0 task cert 8 s5 (k + 1)) = true :=
  range5_all _ c5_1 c5_2 c5_3 c5_4 c5_5

/-- THE CHECKER ACCEPTS: every conjunct evaluated by the kernel, put together by `checkLN_of`. -/
theorem accept : checkLN (1/32768) lnet task cert = true :=
  checkLN_of (1/32768) lnet task cert lnetNB0 8 rfl hdim rd0 rd1 shape wts lnw nh2 d1 iwq bxs bxk len
    (heads_cons _ _ _ _ _ hd0 (heads_cons _ _ _ _ _ hd1 (heads_nil _))) stl ini
    (all_cons_of _ _ _ st0 (all_cons_of _ _ _ st1 (all_cons_of _ _ _ st2 (all_cons_of _ _ _ st3 (all_cons_of _ _ _ st4 (all_cons_of _ _ _ st5 (all_nil_of _)))))))

theorem fold_last (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    (w.take (k + 1)).foldl (fun _ t => t - 1) 0 = w.getD k 0 - 1 := by
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem target_eq (w : List ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    task.target w i = target w i := by
  by_cases h : 2 ≤ i
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    have e := fold_last w k (by omega)
    show ((w.getD (k + 2 - 1) 0 - 1) + (w.take (k + 2 - 1)).foldl (fun _ t => t - 1) 0) % 5
      = ((w.getD (k + 2 - 1) 0 - 1) + (if 2 ≤ k + 2 then w.getD (k + 2 - 2) 0 - 1 else 0)) % 5
    rw [if_pos h,show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl, e]
  · have hi : i = 1 := by omega
    subst hi
    show ((w.getD (1 - 1) 0 - 1) + (w.take (1 - 1)).foldl (fun _ t => t - 1) 0) % 5
      = ((w.getD (1 - 1) 0 - 1) + (if 2 ≤ 1 then w.getD (1 - 2) 0 - 1 else 0)) % 5
    simp

theorem rad_cast : (((1/32768 : ℚ)) : ℝ) = 1/32768 := by norm_num

/-- The registered statement for the skeleton `lnet`: every network within the additive ball of
radius 1/32768 (LayerNorm gains and biases included), every length the rounding model covers. -/
theorem skeleton_ok : Statement lnet := by
  have s := Lane4.LNKI.sound_ln
  unfold Lane4.LNC.SoundLN at s
  intro u η M fl ex sq hr he hs hu0 hu hη0 hη p hp w hw h1 h2 h3 i hi1 hi2
  have hp' : p.Within (((1/32768 : ℚ)) : ℝ) := by rw [rad_cast]; exact hp
  have h := s (1/32768) lnet task cert accept u η M fl ex sq hr he hs hu0 hu hη0 hη p hp' w hw h1 h2 h3 i hi1 hi2
  rw [target_eq w i hi1 hi2] at h
  exact h

theorem exact_all_lengths (p : LPert) (hp : p.Within (1/32768)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |LNNet.out lnet (fun x => x) Real.exp Real.sqrt p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  skeleton_ok 0 0 (2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2) (fun x => x) Real.exp Real.sqrt
    (rnd_id (by positivity)) expM_real sqrtM_real le_rfl (by positivity) le_rfl (by positivity)
    p hp w hw (by simp) (by simp) le_rfl i h1 h2

/-- binary32: `fl` is round-to-nearest on the binary32 range; `ex` and `sq` are ASSUMED to satisfy
the exponential and square-root models (binary32 square root is correctly rounded). -/
theorem binary32 (rn fl ex sq : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex) (hsq : SqrtM (1 / 2 ^ 24) (1 / 2 ^ 149) sq)
    (p : LPert) (hp : p.Within (1/32768))
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |LNNet.out lnet fl ex sq p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 :=
  skeleton_ok (1 / 2 ^ 24) (1 / 2 ^ 149) maxF fl ex sq (bin32_rnd' hrn hfl) hex hsq (by positivity) le_rfl
    (by positivity) le_rfl p hp w hw (side_u hlen) (side_eta hlen) (range_ok hlen) i h1 h2


/-! The network exactly as trained. -/

theorem same : sameShapeL lnet trained = true := by decide +kernel
theorem near : nearNetL (1/32768) lnet trained = true := by decide +kernel

theorem trained_in_ball : (diffPL lnet trained).Within (1/32768) := by
  have d := Lane4.LNKJ.diff_within_l
  unfold Lane4.LNT.DiffWithinL at d
  have h := d lnet trained (1/32768) (by norm_num) same near
  rwa [rad_cast] at h

theorem shift (fl ex sq : ℝ → ℝ) (w : List ℕ) (i : ℕ) :
    LNNet.out lnet fl ex sq (diffPL lnet trained) w i = LNNet.out trained fl ex sq zeroPL w i := by
  have o := Lane4.LNKJ.out_shift_l
  unfold Lane4.LNT.OutShiftL at o
  exact o lnet trained same fl ex sq w i

/-- THE HEADLINE: the network AS TRAINED (float32 weights, no rounding of weights, no
perturbation), exact real arithmetic, every input length. -/
theorem trained_exact_all_lengths (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |LNNet.out trained (fun x => x) Real.exp Real.sqrt zeroPL w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  rw [← shift]
  exact exact_all_lengths _ trained_in_ball w hw i h1 h2

/-- The network AS TRAINED, binary32 arithmetic (exponential and square root assumed as in
`binary32`), at most 65,535 input tokens. -/
theorem trained_binary32 (rn fl ex sq : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex) (hsq : SqrtM (1 / 2 ^ 24) (1 / 2 ^ 149) sq)
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |LNNet.out trained fl ex sq zeroPL w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  rw [← shift]
  exact binary32 rn fl ex sq hrn hfl hex hsq _ trained_in_ball w hw hlen i h1 h2


end Lane4.LNNetFile
#print axioms Lane4.LNNetFile.accept
#print axioms Lane4.LNNetFile.skeleton_ok
#print axioms Lane4.LNNetFile.binary32
#print axioms Lane4.LNNetFile.trained_exact_all_lengths
#print axioms Lane4.LNNetFile.trained_binary32
