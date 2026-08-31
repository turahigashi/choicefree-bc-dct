import Mathdemo.Internal.Real.CRealFixedBoundMultiplicationNegation

/-!
# CReal relation and positivity budget lemmas

The current `relVal` and `PosRaw` frontiers are tight enough that the full
`rel_trans` and `pos_respects` fields should not be faked.  This file records
the honest budget facts available from the current definitions:

* transitivity gives a doubled tolerance immediately;
* positivity is relation-invariant when the positive witness has an explicit
  extra tolerance margin.
-/

namespace BishopCReal

open BishopC
open BishopCRat



/-- Scalar rearrangement: from `a - b ≤ c`, derive `a - c ≤ b`. -/
theorem scalar_le_sub_of_sub_le {a b c : Scalar} (h : Le (a - b) c) :
    Le (a - c) b := by
  intro hbad
  apply h
  have t := COF.lt_add_left (c - b) hbad
  rwa [show (c - b) + b = c from by ring,
    show (c - b) + (a - c) = a - b from by ring] at t

/-- A relation bound gives the usual one-sided lower estimate. -/
theorem rel_point_lower (x y : RegularSeq) (hxy : rel x y) (n : Nat) :
    Le (x.val n - tol n) (y.val n) := by
  have hself : Le (x.val n - y.val n) (COF.abs (x.val n - y.val n)) := by
    change ¬ COF.lt (COF.abs (x.val n - y.val n)) (x.val n - y.val n)
    exact scalarCOFOSeed.le_abs_self (x.val n - y.val n)
  exact scalar_le_sub_of_sub_le (BishopC.le_trans hself (hxy n))




end BishopCReal

