import Mathdemo.Internal.Rat.DecidableOrder

/-!
# CRat COFO seed lemmas

This file extends the live `CRat` scalar with the first concrete laws needed by
`BishopB.COFO`: transitivity of strict order, basic positive constants,
positivity of multiplication, and the first absolute-value facts.

It deliberately does not emit `instance : COFO CRat`; the remaining COFO fields
are still frontier work.  Keeping these facts as named lemmas gives the CReal
layer a stable, audited base without overstating the available structure.
-/

namespace BishopCRat
open Q
open BishopC

namespace Q

/-- Strict order transitivity for cross-multiplied rationals. -/
theorem lt_trans {a b c : Q} (hab : lt a b) (hbc : lt b c) : lt a c := by
  unfold lt at hab hbc ⊢
  have h1 : a.num * b.den * c.den < b.num * a.den * c.den :=
    Int.mul_lt_mul_of_pos_right hab c.den_pos
  have h2 : b.num * c.den * a.den < c.num * b.den * a.den :=
    Int.mul_lt_mul_of_pos_right hbc a.den_pos
  have h1' : a.num * c.den * b.den < b.num * c.den * a.den := by
    calc
      a.num * c.den * b.den = a.num * b.den * c.den := Int.mul_right_comm _ _ _
      _ < b.num * a.den * c.den := h1
      _ = b.num * c.den * a.den := Int.mul_right_comm _ _ _
  have h2' : b.num * c.den * a.den < c.num * a.den * b.den := by
    calc
      b.num * c.den * a.den < c.num * b.den * a.den := h2
      _ = c.num * a.den * b.den := Int.mul_right_comm _ _ _
  have chain : a.num * c.den * b.den < c.num * a.den * b.den :=
    Int.lt_trans h1' h2'
  exact Int.lt_of_mul_lt_mul_right chain (Int.le_of_lt b.den_pos)

theorem one_pos : lt zero one := by
  unfold lt zero one ofInt
  decide

theorem half_pos : lt zero half := by
  unfold lt zero half ofInt
  decide

theorem mul_pos {a b : Q} (ha : lt zero a) (hb : lt zero b) : lt zero (mul a b) := by
  have hna : 0 < a.num := by
    unfold lt zero ofInt at ha
    simpa using ha
  have hnb : 0 < b.num := by
    unfold lt zero ofInt at hb
    simpa using hb
  have hprod : 0 < a.num * b.num := Int.mul_pos hna hnb
  simpa [lt, zero, ofInt, mul] using hprod

theorem abs_zero : rel (abs zero) zero := by
  unfold abs
  have h : 0 ≤ zero.num := by
    unfold zero ofInt
    decide
  rw [if_pos h]
  exact rel_refl zero

theorem neg_neg (a : Q) : rel (neg (neg a)) a := by
  unfold rel neg
  ring

theorem abs_neg (a : Q) : rel (abs (neg a)) (abs a) := by
  unfold abs
  by_cases h : 0 ≤ a.num
  · by_cases hz : a.num = 0
    · have hn : 0 ≤ (neg a).num := by
        change 0 ≤ -a.num
        omega
      simp only [h, hn, if_true]
      unfold rel neg
      rw [hz]
      ring
    · have hn : ¬ 0 ≤ (neg a).num := by
        change ¬ 0 ≤ -a.num
        omega
      simp only [h, hn, if_true, if_false]
      exact neg_neg a
  · have hn : 0 ≤ (neg a).num := by
      change 0 ≤ -a.num
      omega
    simp only [h, hn, if_false, if_true]
    exact rel_refl (neg a)

theorem abs_of_nonneg {a : Q} (h : ¬ lt a zero) : rel (abs a) a := by
  have hn0 : ¬ a.num < 0 := by
    intro hneg
    apply h
    simpa [lt, zero, ofInt] using hneg
  have hn : 0 ≤ a.num := by
    omega
  unfold abs
  simp only [hn, if_true]
  exact rel_refl a

theorem neg_le_abs (a : Q) : ¬ lt (abs a) (neg a) := by
  unfold abs
  by_cases h : 0 ≤ a.num
  · simp only [h, if_true]
    intro hlt
    unfold lt neg at hlt
    have hnum : a.num < -a.num :=
      Int.lt_of_mul_lt_mul_right hlt (Int.le_of_lt a.den_pos)
    omega
  · simp only [h, if_false]
    exact lt_irrefl (neg a)

theorem le_abs_self (a : Q) : ¬ lt (abs a) a := by
  unfold abs
  by_cases h : 0 ≤ a.num
  · simp only [h, if_true]
    exact lt_irrefl a
  · simp only [h, if_false]
    intro hlt
    unfold lt neg at hlt
    have hnum : -a.num < a.num :=
      Int.lt_of_mul_lt_mul_right hlt (Int.le_of_lt a.den_pos)
    omega

theorem abs_le_of {a b : Q} (ha : ¬ lt b a) (hna : ¬ lt b (neg a)) :
    ¬ lt b (abs a) := by
  unfold abs
  by_cases h : 0 ≤ a.num
  · simp only [h, if_true]
    exact ha
  · simp only [h, if_false]
    exact hna

theorem lt_or_lt_of_abs_pos {a : Q} (h : lt zero (abs a)) : lt zero a ∨ lt a zero := by
  unfold abs at h
  by_cases hs : 0 ≤ a.num
  · simp only [hs, if_true] at h
    exact Or.inl h
  · simp only [hs, if_false] at h
    refine Or.inr ?_
    have hnum : 0 < -a.num := by
      simpa [lt, zero, ofInt, neg] using h
    have haneg : a.num < 0 := by omega
    simpa [lt, zero, ofInt] using haneg

theorem mul_nonneg {a b : Q} (ha : ¬ lt a zero) (hb : ¬ lt b zero) :
    ¬ lt (mul a b) zero := by
  have hna0 : ¬ a.num < 0 := by
    intro hneg
    apply ha
    simpa [lt, zero, ofInt] using hneg
  have hnb0 : ¬ b.num < 0 := by
    intro hneg
    apply hb
    simpa [lt, zero, ofInt] using hneg
  have hna : 0 ≤ a.num := by omega
  have hnb : 0 ≤ b.num := by omega
  intro hlt
  have hprod : 0 ≤ a.num * b.num := Int.mul_nonneg hna hnb
  have hnegprod : a.num * b.num < 0 := by
    simpa [lt, zero, ofInt, mul] using hlt
  omega

end Q

namespace CRat

theorem lt_trans {a b c : CRat} (hab : lt a b) (hbc : lt b c) : lt a c := by
  induction a using Quotient.inductionOn with | _ qa =>
  induction b using Quotient.inductionOn with | _ qb =>
  induction c using Quotient.inductionOn with | _ qc =>
  exact Q.lt_trans hab hbc

theorem one_pos : lt 0 1 := by
  change Q.lt Q.zero Q.one
  exact Q.one_pos

theorem half_pos : lt 0 half := by
  change Q.lt Q.zero Q.half
  exact Q.half_pos

theorem mul_pos {a b : CRat} (ha : lt 0 a) (hb : lt 0 b) : lt 0 (a * b) := by
  induction a using Quotient.inductionOn with | _ qa =>
  induction b using Quotient.inductionOn with | _ qb =>
  exact Q.mul_pos ha hb

theorem abs_zero : absF 0 = 0 := by
  exact Quotient.sound Q.abs_zero

theorem abs_neg (a : CRat) : absF (-a) = absF a := by
  induction a using Quotient.inductionOn with | _ qa =>
  exact Quotient.sound (Q.abs_neg qa)

theorem abs_of_nonneg {a : CRat} (h : ¬ lt a 0) : absF a = a := by
  induction a using Quotient.inductionOn with | _ qa =>
  exact Quotient.sound (Q.abs_of_nonneg h)

theorem neg_le_abs (a : CRat) : ¬ lt (absF a) (-a) := by
  induction a using Quotient.inductionOn with | _ qa =>
  exact Q.neg_le_abs qa

theorem le_abs_self (a : CRat) : ¬ lt (absF a) a := by
  induction a using Quotient.inductionOn with | _ qa =>
  exact Q.le_abs_self qa

theorem abs_le_of {a b : CRat} (ha : ¬ lt b a) (hna : ¬ lt b (-a)) :
    ¬ lt b (absF a) := by
  induction a using Quotient.inductionOn with | _ qa =>
  induction b using Quotient.inductionOn with | _ qb =>
  exact Q.abs_le_of ha hna

theorem lt_or_lt_of_abs_pos {a : CRat} (h : lt 0 (absF a)) : lt 0 a ∨ lt a 0 := by
  induction a using Quotient.inductionOn with | _ qa =>
  exact Q.lt_or_lt_of_abs_pos h

theorem mul_nonneg {a b : CRat} (ha : ¬ lt a 0) (hb : ¬ lt b 0) :
    ¬ lt (a * b) 0 := by
  induction a using Quotient.inductionOn with | _ qa =>
  induction b using Quotient.inductionOn with | _ qb =>
  exact Q.mul_nonneg ha hb

/-- Audited subset of the eventual `COFO CRat` instance. -/
structure COFOSeed where
  lt_trans : ∀ {a b c : CRat}, lt a b → lt b c → lt a c
  abs_zero : absF 0 = 0
  abs_neg : ∀ a : CRat, absF (-a) = absF a
  neg_le_abs : ∀ a : CRat, ¬ lt (absF a) (-a)
  le_abs_self : ∀ a : CRat, ¬ lt (absF a) a
  abs_le_of : ∀ {a b : CRat}, ¬ lt b a → ¬ lt b (-a) → ¬ lt b (absF a)
  abs_of_nonneg : ∀ {a : CRat}, ¬ lt a 0 → absF a = a
  lt_or_lt_of_abs_pos : ∀ {a : CRat}, lt 0 (absF a) → lt 0 a ∨ lt a 0
  one_pos : lt 0 1
  half_pos : lt 0 half
  mul_pos : ∀ {a b : CRat}, lt 0 a → lt 0 b → lt 0 (a * b)
  mul_nonneg : ∀ {a b : CRat}, ¬ lt a 0 → ¬ lt b 0 → ¬ lt (a * b) 0

def cofoSeed : COFOSeed where
  lt_trans := lt_trans
  abs_zero := abs_zero
  abs_neg := abs_neg
  neg_le_abs := neg_le_abs
  le_abs_self := le_abs_self
  abs_le_of := abs_le_of
  abs_of_nonneg := abs_of_nonneg
  lt_or_lt_of_abs_pos := lt_or_lt_of_abs_pos
  one_pos := one_pos
  half_pos := half_pos
  mul_pos := mul_pos
  mul_nonneg := mul_nonneg

end CRat
end BishopCRat

-- Axiom profile: these should remain within the quotient/propext boundary.
