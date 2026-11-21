/-
Lane 4, mechanism rows for rung 8 (PREREG_MECH.md), kit case 1: two task automata related by a
checked bisimulation have the same target on every valid input at every position.
Written by the lane; no doctor. New file; no rung 8 file is changed.
-/
import Lane4.R7Cert

namespace Lane4.Mech

open Lane4.Cert

/-- `R` is a bisimulation between `T1` and `T2` over tokens `1..T1.ntok`: it holds the initial
pair, and from every pair in it, on every token, the outputs agree and the successors are in `R`.
Decidable by evaluation. -/
def bisimOK (T1 T2 : Task) (R : List (ℕ × ℕ)) : Bool :=
  R.contains (T1.init, T2.init) &&
  R.all (fun p => (List.range T1.ntok).all (fun k =>
    (T1.out p.1 (k + 1) == T2.out p.2 (k + 1)) &&
    R.contains (T1.step p.1 (k + 1), T2.step p.2 (k + 1))))

theorem bisim_fold (T1 T2 : Task) (R : List (ℕ × ℕ))
    (hR : ∀ p ∈ R, ∀ t, 1 ≤ t → t ≤ T1.ntok →
      T1.out p.1 t = T2.out p.2 t ∧ (T1.step p.1 t, T2.step p.2 t) ∈ R) :
    ∀ (l : List ℕ) (a b : ℕ), (a, b) ∈ R → (∀ t ∈ l, 1 ≤ t ∧ t ≤ T1.ntok) →
      (l.foldl T1.step a, l.foldl T2.step b) ∈ R := by
  intro l
  induction l with
  | nil => intro a b h _; exact h
  | cons t l ih =>
    intro a b h hl
    have ht := hl t (by simp)
    exact ih _ _ ((hR (a, b) h t ht.1 ht.2).2) (fun s hs => hl s (by simp [hs]))

/-- Equal targets from a checked bisimulation. -/
theorem bisim_sound (T1 T2 : Task) (R : List (ℕ × ℕ)) (h : bisimOK T1 T2 R = true)
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ T1.ntok) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    T1.target w i = T2.target w i := by
  unfold bisimOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hinit, hall⟩ := h
  have hR : ∀ p ∈ R, ∀ t, 1 ≤ t → t ≤ T1.ntok →
      T1.out p.1 t = T2.out p.2 t ∧ (T1.step p.1 t, T2.step p.2 t) ∈ R := by
    intro p hp t ht1 ht2
    have a := (List.all_eq_true.mp hall) p hp
    have b := (List.all_eq_true.mp a) (t - 1) (List.mem_range.mpr (by omega))
    rw [Bool.and_eq_true] at b
    have e : t - 1 + 1 = t := by omega
    rw [e] at b
    exact ⟨by simpa using b.1, by simpa using b.2⟩
  have hin : (T1.init, T2.init) ∈ R := by simpa using hinit
  have hpre : ∀ t ∈ w.take (i - 1), 1 ≤ t ∧ t ≤ T1.ntok :=
    fun t ht => hw t (List.mem_of_mem_take ht)
  have hst := bisim_fold T1 T2 R hR (w.take (i - 1)) _ _ hin hpre
  have hlt : i - 1 < w.length := by omega
  have hmem : w.getD (i - 1) 0 ∈ w := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp
  have ht := hw _ hmem
  exact (hR _ hst _ ht.1 ht.2).1

end Lane4.Mech

#print axioms Lane4.Mech.bisim_sound
