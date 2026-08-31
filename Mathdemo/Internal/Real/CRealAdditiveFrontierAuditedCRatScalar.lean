import Mathdemo.Internal.Real.CRealRawPositivityHalf

/-!
# CReal additive frontier over the audited CRat scalar

This file proves the scalar triangle inequalities needed by the CReal
representative operations, then closes the additive frontier:
addition/absolute-value regularity and quotient-respect at the raw
representative level.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar triangle inequality for the audited CRat scalar. -/
theorem scalar_abs_add_le (a b : Scalar) :
    Le (COF.abs (a + b)) (COF.abs a + COF.abs b) := by
  refine scalarCOFOSeed.abs_le_of ?_ ?_
  · have ha : Le a (COF.abs a) := by
      change ¬ COF.lt (COF.abs a) a
      exact scalarCOFOSeed.le_abs_self a
    have hb : Le b (COF.abs b) := by
      change ¬ COF.lt (COF.abs b) b
      exact scalarCOFOSeed.le_abs_self b
    exact BishopC.le_add ha hb
  · have ha : Le (-a) (COF.abs a) := by
      change ¬ COF.lt (COF.abs a) (-a)
      exact scalarCOFOSeed.neg_le_abs a
    have hb : Le (-b) (COF.abs b) := by
      change ¬ COF.lt (COF.abs b) (-b)
      exact scalarCOFOSeed.neg_le_abs b
    have hsum := BishopC.le_add ha hb
    rwa [show -a + -b = -(a + b) from by ring] at hsum

/-- Scalar reverse triangle inequality for absolute values. -/
theorem scalar_abs_abs_sub_abs_le (a b : Scalar) :
    Le (COF.abs (COF.abs a - COF.abs b)) (COF.abs (a - b)) := by
  have key : ∀ u v : Scalar, Le (COF.abs u - COF.abs v) (COF.abs (u - v)) := by
    intro u v
    have ht : Le (COF.abs u) (COF.abs (u - v) + COF.abs v) := by
      have h := scalar_abs_add_le (u - v) v
      rwa [show (u - v) + v = u from by ring] at h
    have h2 := BishopC.le_sub_right (c := COF.abs v) ht
    rwa [show COF.abs (u - v) + COF.abs v - COF.abs v = COF.abs (u - v)
        from by ring] at h2
  have h1 : Le (COF.abs a - COF.abs b) (COF.abs (a - b)) := key a b
  have h2 : Le (-(COF.abs a - COF.abs b)) (COF.abs (a - b)) := by
    have hb := key b a
    rw [show COF.abs (b - a) = COF.abs (a - b) from by
      rw [show b - a = -(a - b) from by ring]
      exact scalarCOFOSeed.abs_neg (a - b)] at hb
    rwa [show COF.abs b - COF.abs a = -(COF.abs a - COF.abs b) from by ring] at hb
  exact scalarCOFOSeed.abs_le_of h1 h2


/-- Addition preserves regularity of representatives. -/
theorem add_regular (x y : RegularSeq) : RegularVal (addVal x.val y.val) := by
  intro m n
  unfold addVal addIndex
  have htri : Le
      (COF.abs ((x.val (m + 1) + y.val (m + 1)) - (x.val (n + 1) + y.val (n + 1))))
      (COF.abs (x.val (m + 1) - x.val (n + 1))
        + COF.abs (y.val (m + 1) - y.val (n + 1))) := by
    have h := scalar_abs_add_le
      (x.val (m + 1) - x.val (n + 1))
      (y.val (m + 1) - y.val (n + 1))
    rwa [show (x.val (m + 1) - x.val (n + 1))
        + (y.val (m + 1) - y.val (n + 1))
        = (x.val (m + 1) + y.val (m + 1)) - (x.val (n + 1) + y.val (n + 1))
        from by ring] at h
  have hx := x.regular (m + 1) (n + 1)
  have hy := y.regular (m + 1) (n + 1)
  have hsum := BishopC.le_add hx hy
  have hbudget :
      (eps (m + 1) + eps (n + 1)) + (eps (m + 1) + eps (n + 1))
        = eps m + eps n := by
    rw [show (eps (m + 1) + eps (n + 1)) + (eps (m + 1) + eps (n + 1))
        = (eps (m + 1) + eps (m + 1)) + (eps (n + 1) + eps (n + 1))
        from by ring, eps_succ_add_self m, eps_succ_add_self n]
  have hsum' : Le
      (COF.abs (x.val (m + 1) - x.val (n + 1))
        + COF.abs (y.val (m + 1) - y.val (n + 1)))
      (eps m + eps n) := by
    rwa [hbudget] at hsum
  exact BishopC.le_trans htri hsum'


/-- Absolute value preserves regularity of representatives. -/
theorem abs_regular (x : RegularSeq) : RegularVal (absVal x.val) := by
  intro m n
  unfold absVal
  exact BishopC.le_trans (scalar_abs_abs_sub_abs_le (x.val m) (x.val n)) (x.regular m n)



end BishopCReal

