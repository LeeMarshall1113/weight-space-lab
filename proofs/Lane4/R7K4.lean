/-
Lane 4, rung 7 kit module, assembled by tools/r7_assemble.py from kit case k4
(runs/r7-kit/k4): statements by the lane, proofs by a Sonnet doctor, checked by tools/check.py.
-/
import Lane4.R7Defs

namespace Lane4.R7K4
open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate Lane4.Cert

/-- A set of abstract states that contains the initial one and is closed under reading a
token contains the abstract state of every input prefix. -/
def AbsClosed : Prop :=
  ∀ (T : Task) (cands : List (List Bool)) (states : List (ℕ × List (Option ℕ))),
  absInit T cands ∈ states →
  (∀ st ∈ states, ∀ t, 1 ≤ t → t ≤ T.ntok → absStep T cands st t ∈ states) →
  ∀ pre : List ℕ, (∀ t ∈ pre, 1 ≤ t ∧ t ≤ T.ntok) → absState T cands pre ∈ states

/-- The abstract state carries one pick per head. -/
def AbsLen : Prop :=
  ∀ (T : Task) (cands : List (List Bool)) (pre : List ℕ),
    (absState T cands pre).2.length = cands.length

/-- The task's target at position `i` is the automaton's output on the abstract state of the
first `i - 1` tokens and the token at `i`. -/
def AbsTarget : Prop :=
  ∀ (T : Task) (cands : List (List Bool)) (w : List ℕ) (i : ℕ), 1 ≤ i → i ≤ w.length →
    T.target w i = T.out (absState T cands (w.take (i - 1))).1 (tokAt w i)

/-- What the pick of head number `a` means at query position `i`: with `p` the pick stored
in the abstract state of the first `i - 1` tokens and `q = pickAt h cd (token at i) p`:
if `q` is `none`, no position the mask allows holds a candidate token; if `q` is `some t`,
the latest candidate position exists and holds token `t`. Positions run over `0..w.length`
(position 0 is BOS, token 0), `cd` is the candidate set of head `a`. -/
def AbsPick : Prop :=
  ∀ (T : Task) (cands : List (List Bool)) (w : List ℕ) (i a : ℕ) (h : AHead),
  1 ≤ i → i ≤ w.length → a < cands.length → h.mask ≠ Mask.all →
    (pickAt h (cands.getD a []) (tokAt w i)
        ((absState T cands (w.take (i - 1))).2.getD a none) = none →
      ∀ j ∈ cand h.mask (w.length + 1) i, (cands.getD a []).getD (tokAt w j) false = false)
    ∧ (∀ t, pickAt h (cands.getD a []) (tokAt w i)
        ((absState T cands (w.take (i - 1))).2.getD a none) = some t →
      ∃ j, Latest h.mask (cands.getD a []) (tokAt w) (w.length + 1) i j ∧ tokAt w j = t)

end Lane4.R7K4


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Lane4.R7K4
open Lane4.Seq (Mask cand tokAt)
open Lane4.AGate Lane4.Cert

theorem absState_snoc (T : Task) (cands : List (List Bool)) (l : List ℕ) (a : ℕ) :
    absState T cands (l ++ [a]) = absStep T cands (absState T cands l) a := by
  simp [absState, List.foldl_append]

theorem abs_closed : AbsClosed := by
  intro T cands states h0 hs pre
  induction pre using List.reverseRecOn with
  | nil => intro _; simpa [absState] using h0
  | append_singleton l a ih =>
    intro hall
    have h1 : ∀ t ∈ l, 1 ≤ t ∧ t ≤ T.ntok := fun t ht => hall t (by simp [ht])
    have h2 := hall a (by simp)
    rw [absState_snoc]
    exact hs _ (ih h1) a h2.1 h2.2

theorem abs_len : AbsLen := by
  intro T cands pre
  induction pre using List.reverseRecOn with
  | nil => simp [absState, absInit]
  | append_singleton l a ih =>
    rw [absState_snoc]
    simp [absStep, List.length_zipWith, ih]

theorem abs_fst (T : Task) (cands : List (List Bool)) (pre : List ℕ) :
    (absState T cands pre).1 = pre.foldl T.step T.init := by
  induction pre using List.reverseRecOn with
  | nil => simp [absState, absInit]
  | append_singleton l a ih =>
    rw [absState_snoc]
    simp [absStep, ih, List.foldl_append]

theorem abs_target : AbsTarget := by
  intro T cands w i h1 h2
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Task.target, abs_fst, Nat.add_sub_cancel]
  simp [tokAt]

theorem zw_getD (f : List Bool → Option ℕ → Option ℕ) :
    ∀ (cands : List (List Bool)) (l : List (Option ℕ)) (a : ℕ), a < cands.length →
      l.length = cands.length →
      (List.zipWith f cands l).getD a none = f (cands.getD a []) (l.getD a none) := by
  intro cands
  induction cands with
  | nil => intro l a h; simp at h
  | cons c cs ih =>
    intro l a ha hl
    cases l with
    | nil => simp at hl
    | cons p ps =>
      cases a with
      | zero => simp
      | succ a =>
        simp only [List.zipWith_cons_cons, List.getD_cons_succ]
        exact ih ps a (by simpa using ha) (by simpa using hl)

theorem map_getD (g : List Bool → Option ℕ) :
    ∀ (cands : List (List Bool)) (a : ℕ), a < cands.length →
      (cands.map g).getD a none = g (cands.getD a []) := by
  intro cands
  induction cands with
  | nil => intro a h; simp at h
  | cons c cs ih =>
    intro a ha
    cases a with
    | zero => simp
    | succ a =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih a (by simpa using ha)

theorem inv_pick (T : Task) (cands : List (List Bool)) (w : List ℕ) (a : ℕ)
    (ha : a < cands.length) :
    ∀ k, k ≤ w.length →
      (((absState T cands (w.take k)).2.getD a none = none →
        ∀ j ≤ k, (cands.getD a []).getD (tokAt w j) false = false) ∧
      (∀ t, (absState T cands (w.take k)).2.getD a none = some t →
        ∃ j ≤ k, tokAt w j = t ∧ (cands.getD a []).getD t false = true ∧
          ∀ j2 ≤ k, (cands.getD a []).getD (tokAt w j2) false = true → j2 ≤ j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    have e : (absState T cands (w.take 0)).2.getD a none =
        (if (cands.getD a []).getD 0 false = true then some 0 else none) := by
      simp only [List.take_zero, absState, List.foldl_nil, absInit]
      exact map_getD (fun cd => if cd.getD 0 false = true then some 0 else none) cands a ha
    rw [e]
    have t0 : tokAt w 0 = 0 := by simp [tokAt]
    by_cases hc : (cands.getD a []).getD 0 false = true
    · simp only [hc, if_true]
      refine ⟨by simp, fun t ht => ?_⟩
      have : t = 0 := by simpa using ht.symm
      subst this
      exact ⟨0, le_refl _, t0, hc, fun j2 hj2 _ => hj2⟩
    · simp only [hc, if_false]
      refine ⟨fun _ j hj => ?_, by simp⟩
      have : j = 0 := by omega
      subst this
      rw [t0]; simpa using hc
  | succ k ih =>
    intro hk
    have hk' : k < w.length := by omega
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have tk : tokAt w (k + 1) = w.getD k 0 := by simp [tokAt]
    have ht : w.take (k + 1) = w.take k ++ [w.getD k 0] := by
      rw [List.take_succ]
      simp [List.getElem?_eq_getElem hk', List.getD_eq_getElem?_getD]
    have hlen := abs_len T cands (w.take k)
    have e : (absState T cands (w.take (k + 1))).2.getD a none =
        pickNext (cands.getD a []) (w.getD k 0) ((absState T cands (w.take k)).2.getD a none) := by
      rw [ht, absState_snoc]
      exact zw_getD (fun cd p => pickNext cd (w.getD k 0) p) cands _ a ha hlen
    rw [e]
    unfold pickNext
    by_cases hc : (cands.getD a []).getD (w.getD k 0) false = true
    · simp only [hc, if_true]
      refine ⟨by simp, fun t ht' => ?_⟩
      have : w.getD k 0 = t := by simpa using ht'
      subst this
      exact ⟨k + 1, le_refl _, tk, hc, fun j2 hj2 _ => hj2⟩
    · simp only [hc, if_false]
      refine ⟨fun hn j hj => ?_, fun t ht' => ?_⟩
      · by_cases hjk : j = k + 1
        · subst hjk; rw [tk]; simpa using hc
        · exact ih1 hn j (by omega)
      · obtain ⟨j, hj, h1, h2, h3⟩ := ih2 t ht'
        refine ⟨j, by omega, h1, h2, fun j2 hj2 hcd => ?_⟩
        by_cases hjk : j2 = k + 1
        · subst hjk; rw [tk] at hcd; exact absurd hcd hc
        · exact h3 j2 (by omega) hcd

theorem abs_pick : AbsPick := by
  intro T cands w i a h h1 h2 ha hm
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k ≤ w.length := by omega
  obtain ⟨I1, I2⟩ := inv_pick T cands w a ha k hk
  simp only [Nat.add_sub_cancel]
  have tk : tokAt w (k + 1) = w.getD k 0 := by simp [tokAt]
  set p := (absState T cands (w.take k)).2.getD a none with hp
  set cd := cands.getD a [] with hcd
  unfold pickAt
  have hmask : h.mask = Mask.causal ∨ h.mask = Mask.strict := by
    cases hh : h.mask <;> simp_all
  rcases hmask with hmc | hms
  · simp only [hmc, true_and]
    by_cases hc : cd.getD (tokAt w (k + 1)) false = true
    · simp only [hc, if_true]
      refine ⟨by simp, fun t ht => ?_⟩
      have : tokAt w (k + 1) = t := by simpa using ht
      refine ⟨k + 1, ⟨?_, hc, ?_⟩, this⟩
      · simp [hmc, cand]
      · intro k' hk' _
        simp [hmc, cand] at hk'
        omega
    · simp only [hc, if_false]
      refine ⟨fun hn j hj => ?_, fun t ht => ?_⟩
      · simp [hmc, cand] at hj
        by_cases hjk : j = k + 1
        · subst hjk; simpa using hc
        · exact I1 hn j (by omega)
      · obtain ⟨j, hj, e1, e2, e3⟩ := I2 t ht
        refine ⟨j, ⟨?_, ?_, ?_⟩, e1⟩
        · simp [hmc, cand]; omega
        · rw [e1]; exact e2
        · intro k' hk' hcd
          simp [hmc, cand] at hk'
          by_cases hjk : k' = k + 1
          · subst hjk; exact absurd hcd hc
          · exact e3 k' (by omega) hcd
  · have hnc : ¬ (h.mask = Mask.causal) := by rw [hms]; simp
    simp only [hnc, false_and, if_false]
    refine ⟨fun hn j hj => ?_, fun t ht => ?_⟩
    · simp [hms, cand] at hj
      exact I1 hn j (by omega)
    · obtain ⟨j, hj, e1, e2, e3⟩ := I2 t ht
      refine ⟨j, ⟨?_, ?_, ?_⟩, e1⟩
      · simp [hms, cand]; omega
      · rw [e1]; exact e2
      · intro k' hk' hcd
        simp [hms, cand] at hk'
        exact e3 k' (by omega) hcd

end Lane4.R7K4

