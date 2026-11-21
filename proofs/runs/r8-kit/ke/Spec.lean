namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-- What a form says about the number it represents. -/
def AFRange : Prop :=
  ∀ (e : ℕ → ℝ) (v : ℝ) (a : AF), Sym e → InAF e v a →
    0 ≤ a.r ∧ |v| ≤ ((a.mag : ℚ) : ℝ) ∧
    (((a.c - a.dev : ℚ)) : ℝ) ≤ v ∧ v ≤ (((a.c + a.dev : ℚ)) : ℝ)

/-- A stored embedding row, as forms without symbols. -/
def EmbAF : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (row : List ℚ) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) → smallQ row = true →
  ∀ e : ℕ → ℝ,
    InAFs e (aswRow fl row d 0) (row.map (fun a => (⟨a, [], e0 δ⟩ : AF)))
    ∧ ∀ a ∈ row.map (fun a => (⟨a, [], e0 δ⟩ : AF)), a.mag ≤ 16

/-- A stored-weight dot product of a vector of forms lies in `dotAF`. -/
def DotAF : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (r : List ℚ) (x : List ℝ) (xa : List AF) (d : ℕ → ℝ), (∀ k, |d k| ≤ (δ : ℝ)) →
  r.length = x.length → r.length ≤ 32 → smallQ r = true →
  ∀ e : ℕ → ℝ, Sym e → InAFs e x xa → (∀ a ∈ xa, a.mag ≤ 16) →
    InAF e (ardot fl r x d 0 0) (dotAF δ r xa)

/-- A stored affine map lies in `affAF`, when every output passes the magnitude guard. -/
def AffAF : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl → ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (A : List (List ℚ)) (b : List ℚ) (x : List ℝ) (xa : List AF) (dW : ℕ → ℕ → ℝ) (db : ℕ → ℝ),
  (∀ i k, |dW i k| ≤ (δ : ℝ)) → (∀ i, |db i| ≤ (δ : ℝ)) →
  (∀ r ∈ A, r.length = x.length) → x.length ≤ 32 → A.length = b.length →
  smallM A = true → smallQ b = true →
  ∀ e : ℕ → ℝ, Sym e → InAFs e x xa → (∀ a ∈ xa, a.mag ≤ 16) →
  (affAF δ A b xa).all AF.small = true →
    InAFs e (araffine fl A b x dW db 0) (affAF δ A b xa)

/-- A rounded entrywise sum lies in `addAF`, when every output passes the magnitude guard. -/
def AddAF : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ (x y : List ℝ) (a b : List AF) (e : ℕ → ℝ), Sym e → InAFs e x a → InAFs e y b →
  (addAF a b).all AF.small = true →
    InAFs e (radd fl x y) (addAF a b)

/-- ReLU maps a form into `reluAF` of it, and small forms to small forms. -/
def ReluAF : Prop :=
  ∀ (x : List ℝ) (xa : List AF) (e : ℕ → ℝ), Sym e → InAFs e x xa →
  xa.all AF.small = true →
    InAFs e (x.map Lane4.relu) (xa.map reluAF) ∧ (xa.map reluAF).all AF.small = true

/-- Shifting the centre: if `v` is in `a` then a number within `r` of `v + c` is in `a.shift c r`. -/
def ShiftAF : Prop :=
  ∀ (e : ℕ → ℝ) (v v' : ℝ) (a : AF) (c r : ℚ), InAF e v a →
    |v' - (v + ((c : ℚ) : ℝ))| ≤ ((r : ℚ) : ℝ) → InAF e v' (a.shift c r)

end Lane4.Case
