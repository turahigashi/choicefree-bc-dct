import Mathlib.Tactic.Ring

/-! Technical auxiliary material for the public import closure. -/

namespace BishopCRat

/-- Technical lemma used in the public import closure. -/
structure Q where
  num : Int
  den : Int
  den_pos : 0 < den

namespace Q

/-- Technical lemma used in the public import closure. -/
def rel (a b : Q) : Prop := a.num * b.den = b.num * a.den

theorem rel_refl (a : Q) : rel a a := rfl

theorem rel_symm {a b : Q} (h : rel a b) : rel b a := h.symm

/-- Technical lemma used in the public import closure. -/
theorem rel_trans {a b c : Q} (hab : rel a b) (hbc : rel b c) : rel a c := by
  have H : a.num * c.den * b.den = c.num * a.den * b.den := by
    calc a.num * c.den * b.den
        = a.num * b.den * c.den := Int.mul_right_comm _ _ _
      _ = b.num * a.den * c.den := by rw [hab]
      _ = b.num * c.den * a.den := Int.mul_right_comm _ _ _
      _ = c.num * b.den * a.den := by rw [hbc]
      _ = c.num * a.den * b.den := Int.mul_right_comm _ _ _
  have hne : b.den ≠ 0 := by have := b.den_pos; omega
  exact Int.eq_of_mul_eq_mul_right hne H

/-- Technical lemma used in the public import closure. -/
def ofInt (n : Int) : Q := ⟨n, 1, by decide⟩

/-- Technical lemma used in the public import closure. -/
def zero : Q := ofInt 0
def one : Q := ofInt 1

/-- Technical lemma used in the public import closure. -/
def neg (a : Q) : Q := ⟨-a.num, a.den, a.den_pos⟩

/-- Technical lemma used in the public import closure. -/
def add (a b : Q) : Q :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

/-- Technical lemma used in the public import closure. -/
def mul (a b : Q) : Q :=
  ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem neg_congr {a a' : Q} (h : rel a a') : rel (neg a) (neg a') := by
  have h' : a.num * a'.den = a'.num * a.den := h
  show (-a.num) * a'.den = (-a'.num) * a.den
  rw [Int.neg_mul, Int.neg_mul, h']

/-- Technical lemma used in the public import closure. -/
theorem add_congr {a a' b b' : Q} (ha : rel a a') (hb : rel b b') :
    rel (add a b) (add a' b') := by
  have ha' : a.num * a'.den = a'.num * a.den := ha
  have hb' : b.num * b'.den = b'.num * b.den := hb
  show (a.num * b.den + b.num * a.den) * (a'.den * b'.den)
     = (a'.num * b'.den + b'.num * a'.den) * (a.den * b.den)
  have hL : (a.num * b.den + b.num * a.den) * (a'.den * b'.den)
      = (a.num * a'.den) * (b.den * b'.den) + (b.num * b'.den) * (a.den * a'.den) := by ring
  have hR : (a'.num * b'.den + b'.num * a'.den) * (a.den * b.den)
      = (a'.num * a.den) * (b.den * b'.den) + (b'.num * b.den) * (a.den * a'.den) := by ring
  rw [hL, hR, ha', hb']

/-- Technical lemma used in the public import closure. -/
theorem mul_congr {a a' b b' : Q} (ha : rel a a') (hb : rel b b') :
    rel (mul a b) (mul a' b') := by
  have ha' : a.num * a'.den = a'.num * a.den := ha
  have hb' : b.num * b'.den = b'.num * b.den := hb
  show (a.num * b.num) * (a'.den * b'.den) = (a'.num * b'.num) * (a.den * b.den)
  have hL : (a.num * b.num) * (a'.den * b'.den)
      = (a.num * a'.den) * (b.num * b'.den) := by ring
  have hR : (a'.num * b'.num) * (a.den * b.den)
      = (a'.num * a.den) * (b'.num * b.den) := by ring
  rw [hL, hR, ha', hb']

/-! Technical auxiliary material for the public import closure. -/

theorem add_comm (a b : Q) : rel (add a b) (add b a) := by
  unfold rel add ; ring
theorem add_assoc (a b c : Q) : rel (add (add a b) c) (add a (add b c)) := by
  unfold rel add ; ring
theorem zero_add (a : Q) : rel (add zero a) a := by
  unfold rel add zero ofInt ; ring
theorem add_zero (a : Q) : rel (add a zero) a := by
  unfold rel add zero ofInt ; ring
theorem neg_add_cancel (a : Q) : rel (add (neg a) a) zero := by
  unfold rel add neg zero ofInt ; ring
theorem mul_comm (a b : Q) : rel (mul a b) (mul b a) := by
  unfold rel mul ; ring
theorem mul_assoc (a b c : Q) : rel (mul (mul a b) c) (mul a (mul b c)) := by
  unfold rel mul ; ring
theorem one_mul (a : Q) : rel (mul one a) a := by
  unfold rel mul one ofInt ; ring
theorem mul_one (a : Q) : rel (mul a one) a := by
  unfold rel mul one ofInt ; ring
theorem left_distrib (a b c : Q) : rel (mul a (add b c)) (add (mul a b) (mul a c)) := by
  unfold rel add mul ; ring
theorem right_distrib (a b c : Q) : rel (mul (add a b) c) (add (mul a c) (mul b c)) := by
  unfold rel add mul ; ring
theorem zero_mul (a : Q) : rel (mul zero a) zero := by
  unfold rel mul zero ofInt ; ring
theorem mul_zero (a : Q) : rel (mul a zero) zero := by
  unfold rel mul zero ofInt ; ring

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def lt (a b : Q) : Prop := a.num * b.den < b.num * a.den

/-- Technical lemma used in the public import closure. -/
theorem lt_irrefl (a : Q) : ¬ lt a a := fun h => (Int.lt_irrefl (a.num * a.den)) h

/-- Technical lemma used in the public import closure. -/
theorem lt_add_left (c : Q) {a b : Q} (h : lt a b) : lt (add c a) (add c b) := by
  -- Technical note.
  -- Technical note.
  simp only [lt, add]
  have hpos : 0 < b.num * a.den - a.num * b.den := by simp only [lt] at h; omega
  have hprod : 0 < (c.den * c.den) * (b.num * a.den - a.num * b.den) :=
    Int.mul_pos (Int.mul_pos c.den_pos c.den_pos) hpos
  -- Technical note.
  rw [show (c.num * b.den + b.num * c.den) * (c.den * a.den)
      = (c.num * a.den + a.num * c.den) * (c.den * b.den)
        + (c.den * c.den) * (b.num * a.den - a.num * b.den) from by ring]
  omega

/-- Technical lemma used in the public import closure. -/
theorem lt_cotrans {a b : Q} (h : lt a b) (c : Q) : lt a c ∨ lt c b := by
  unfold lt at h ⊢
  rcases Int.lt_or_le (a.num * c.den) (c.num * a.den) with hlt | hge
  · exact Or.inl hlt
  · refine Or.inr ?_
    have hca : c.num * a.den ≤ a.num * c.den := hge
    have s1 : c.num * a.den * b.den ≤ a.num * c.den * b.den :=
      Int.mul_le_mul_of_nonneg_right hca (le_of_lt b.den_pos)
    have s2 : a.num * b.den * c.den < b.num * a.den * c.den :=
      Int.mul_lt_mul_of_pos_right h c.den_pos
    have chain : c.num * b.den * a.den < b.num * c.den * a.den := by
      have e1 : c.num * a.den * b.den = c.num * b.den * a.den := by ring
      have e2 : a.num * c.den * b.den = a.num * b.den * c.den := by ring
      have e3 : b.num * a.den * c.den = b.num * c.den * a.den := by ring
      omega
    exact Int.lt_of_mul_lt_mul_right chain (le_of_lt a.den_pos)

/-- Data-valued cotransitivity. This is the same cross-multiplication proof as
`lt_cotrans`, but it returns `PSum` directly, matching the current
`BishopB.COF.lt_cotrans_data` field without extracting data from a Prop. -/
def lt_cotrans_data {a b : Q} (h : lt a b) (c : Q) : PSum (lt a c) (lt c b) := by
  unfold lt at h ⊢
  by_cases hlt : a.num * c.den < c.num * a.den
  · exact PSum.inl hlt
  · refine PSum.inr ?_
    have hca : c.num * a.den ≤ a.num * c.den := by omega
    have s1 : c.num * a.den * b.den ≤ a.num * c.den * b.den :=
      Int.mul_le_mul_of_nonneg_right hca (le_of_lt b.den_pos)
    have s2 : a.num * b.den * c.den < b.num * a.den * c.den :=
      Int.mul_lt_mul_of_pos_right h c.den_pos
    have chain : c.num * b.den * a.den < b.num * c.den * a.den := by
      have e1 : c.num * a.den * b.den = c.num * b.den * a.den := by ring
      have e2 : a.num * c.den * b.den = a.num * b.den * c.den := by ring
      have e3 : b.num * a.den * c.den = b.num * c.den * a.den := by ring
      omega
    exact Int.lt_of_mul_lt_mul_right chain (le_of_lt a.den_pos)

/-- Technical lemma used in the public import closure. -/
theorem pos_of_mul_pos_right {x p : Int} (h : 0 < x * p) (hp : 0 ≤ p) : 0 < x :=
  Int.lt_of_mul_lt_mul_right (by rwa [Int.zero_mul]) hp

/-- Technical lemma used in the public import closure. -/
theorem lt_congr {a a' b b' : Q} (ha : rel a a') (hb : rel b b') : lt a b ↔ lt a' b' := by
  have ha' : a.num * a'.den = a'.num * a.den := ha
  have hb' : b.num * b'.den = b'.num * b.den := hb
  have key : (b.num*a.den - a.num*b.den) * (a'.den*b'.den)
           = (b'.num*a'.den - a'.num*b'.den) * (a.den*b.den) := by
    have hL : (b.num*a.den - a.num*b.den) * (a'.den*b'.den)
            = (b.num*b'.den)*(a.den*a'.den) - (a.num*a'.den)*(b.den*b'.den) := by ring
    have hR : (b'.num*a'.den - a'.num*b'.den) * (a.den*b.den)
            = (b'.num*b.den)*(a.den*a'.den) - (a'.num*a.den)*(b.den*b'.den) := by ring
    rw [hL, hR, ha', hb']
  have hp1 : 0 < a'.den * b'.den := Int.mul_pos a'.den_pos b'.den_pos
  have hp2 : 0 < a.den * b.den := Int.mul_pos a.den_pos b.den_pos
  simp only [lt]
  constructor
  · intro h
    have d1 : 0 < (b.num*a.den - a.num*b.den) := by omega
    have d2 : 0 < (b'.num*a'.den - a'.num*b'.den) * (a.den*b.den) := by
      rw [← key]; exact Int.mul_pos d1 hp1
    have d3 := pos_of_mul_pos_right d2 (le_of_lt hp2)
    omega
  · intro h
    have d1 : 0 < (b'.num*a'.den - a'.num*b'.den) := by omega
    have d2 : 0 < (b.num*a.den - a.num*b.den) * (a'.den*b'.den) := by
      rw [key]; exact Int.mul_pos d1 hp2
    have d3 := pos_of_mul_pos_right d2 (le_of_lt hp1)
    omega

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def abs (a : Q) : Q := if 0 ≤ a.num then a else neg a

/-- Technical lemma used in the public import closure. -/
theorem abs_congr {a a' : Q} (h : rel a a') : rel (abs a) (abs a') := by
  have h' : a.num * a'.den = a'.num * a.den := h
  unfold abs
  by_cases h1 : 0 ≤ a.num <;> by_cases h2 : 0 ≤ a'.num
  · simp only [h1, h2, if_true]; exact h
  · exfalso
    have hg : 0 ≤ a.num * a'.den := Int.mul_nonneg h1 (le_of_lt a'.den_pos)
    have hl : a'.num * a.den < 0 := Int.mul_neg_of_neg_of_pos (by omega) a.den_pos
    omega
  · exfalso
    have hg : 0 ≤ a'.num * a.den := Int.mul_nonneg h2 (le_of_lt a.den_pos)
    have hl : a.num * a'.den < 0 := Int.mul_neg_of_neg_of_pos (by omega) a'.den_pos
    omega
  · simp only [h1, h2, if_false]; exact neg_congr h

/-- ½ = ⟨1,2⟩。 -/
def half : Q := ⟨1, 2, by decide⟩

/-- Technical lemma used in the public import closure. -/
theorem half_add_half : rel (add half half) one := by unfold rel add half one ofInt; ring

-- Technical note.

end Q
end BishopCRat
