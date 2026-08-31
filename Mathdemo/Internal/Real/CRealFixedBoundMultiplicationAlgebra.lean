import Mathdemo.Internal.Real.CRealRawSubtractionClosure

/-!
# CReal fixed-bound multiplication algebra

This file records the multiplication laws that do not require the hard
bound-construction/respect layer.  They are stated for a fixed natural bound
`K`, so they remain honest facts about the current `mulValWithBound` shape
without pretending to solve bounded multiplication globally.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Dyadic gauges are monotone under adding natural index slack. -/
theorem eps_add_le_eps (n d : Nat) : Le (eps (n + d)) (eps n) := by
  induction d with
  | zero =>
      rw [Nat.add_zero]
      exact BishopC.le_refl (eps n)
  | succ d ih =>
      rw [show n + Nat.succ d = (n + d) + 1 from by omega]
      exact BishopC.le_trans (eps_succ_le_eps (n + d)) ih

/-- Dyadic gauges are monotone with respect to the natural index order. -/
theorem eps_le_of_le {n m : Nat} (h : n ≤ m) : Le (eps m) (eps n) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  rw [hd]
  exact eps_add_le_eps n d

/-- The multiplication reindexing always looks at an index at least as large
as the requested output index. -/
theorem le_mulIndexFromBound (K n : Nat) : n ≤ mulIndexFromBound K n := by
  unfold mulIndexFromBound
  have hn : n ≤ n + 1 := Nat.le_succ n
  have hcoef : 0 < 2 * (K + 1) := Nat.mul_pos (by decide) (Nat.succ_pos K)
  have hmul : n + 1 ≤ (2 * (K + 1)) * (n + 1) :=
    Nat.le_mul_of_pos_left (n + 1) hcoef
  have hadd : (2 * (K + 1)) * (n + 1) ≤ (2 * (K + 1)) * (n + 1) + 1 :=
    Nat.le_succ _
  exact Nat.le_trans hn (Nat.le_trans hmul hadd)

/-- Fixed-bound left multiplication by zero is raw-equal to zero. -/
theorem mul_zero_left_raw_fixed (K : Nat) (x : RegularSeq) :
    relVal (mulValWithBound K zeroVal x.val) zeroVal := by
  intro n
  unfold mulValWithBound zeroVal constVal
  rw [show (0 * x.val (mulIndexFromBound K n)) - 0 = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Fixed-bound right multiplication by zero is raw-equal to zero. -/
theorem mul_zero_right_raw_fixed (K : Nat) (x : RegularSeq) :
    relVal (mulValWithBound K x.val zeroVal) zeroVal := by
  intro n
  unfold mulValWithBound zeroVal constVal
  rw [show (x.val (mulIndexFromBound K n) * 0) - 0 = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Fixed-bound left multiplication by one is raw-equal to the original
representative. -/
theorem mul_one_left_raw_fixed (K : Nat) (x : RegularSeq) :
    relVal (mulValWithBound K oneVal x.val) x.val := by
  intro n
  unfold mulValWithBound oneVal constVal
  rw [show (1 * x.val (mulIndexFromBound K n)) - x.val n
      = x.val (mulIndexFromBound K n) - x.val n from by ring]
  have hx := x.regular (mulIndexFromBound K n) n
  have hbudget : Le (eps (mulIndexFromBound K n) + eps n) (tol n) := by
    unfold tol
    exact BishopC.le_add (eps_le_of_le (le_mulIndexFromBound K n)) (BishopC.le_refl (eps n))
  exact BishopC.le_trans hx hbudget

/-- Fixed-bound right multiplication by one is raw-equal to the original
representative. -/
theorem mul_one_right_raw_fixed (K : Nat) (x : RegularSeq) :
    relVal (mulValWithBound K x.val oneVal) x.val := by
  intro n
  unfold mulValWithBound oneVal constVal
  rw [show (x.val (mulIndexFromBound K n) * 1) - x.val n
      = x.val (mulIndexFromBound K n) - x.val n from by ring]
  have hx := x.regular (mulIndexFromBound K n) n
  have hbudget : Le (eps (mulIndexFromBound K n) + eps n) (tol n) := by
    unfold tol
    exact BishopC.le_add (eps_le_of_le (le_mulIndexFromBound K n)) (BishopC.le_refl (eps n))
  exact BishopC.le_trans hx hbudget

/-- Fixed-bound multiplication is raw-commutative. -/
theorem mul_comm_raw_fixed (K : Nat) (x y : RegularSeq) :
    relVal
      (mulValWithBound K x.val y.val)
      (mulValWithBound K y.val x.val) := by
  intro n
  unfold mulValWithBound
  rw [show
      x.val (mulIndexFromBound K n) * y.val (mulIndexFromBound K n)
        - y.val (mulIndexFromBound K n) * x.val (mulIndexFromBound K n)
        = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n



end BishopCReal

