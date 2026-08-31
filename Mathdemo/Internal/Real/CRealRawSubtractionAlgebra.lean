import Mathdemo.Internal.Real.CRealFixedBoundMultiplicationAlgebra

/-!
# CReal raw subtraction algebra

The order layer uses `subVal`, while the additive algebra layer is expressed
through `addVal` and `negVal`.  This file closes the basic raw identities that
connect those two presentations.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Raw subtraction by zero is equal to the original representative. -/
theorem sub_zero_raw (x : RegularSeq) : relVal (subVal x.val zeroVal) x.val := by
  intro n
  unfold subVal addIndex zeroVal constVal
  rw [show x.val (n + 1) - 0 - x.val n = x.val (n + 1) - x.val n from by ring]
  exact BishopC.le_trans (x.regular (n + 1) n) (eps_succ_add_le_tol n)

/-- Raw zero minus a representative is equal to its negation. -/
theorem zero_sub_raw (x : RegularSeq) :
    relVal (subVal zeroVal x.val) (negVal x.val) := by
  intro n
  unfold subVal addIndex zeroVal constVal negVal
  rw [show (0 - x.val (n + 1)) - -x.val n
      = -(x.val (n + 1) - x.val n) from by ring]
  change Le (BishopCRat.CRat.absF (-(x.val (n + 1) - x.val n))) (tol n)
  rw [scalarCOFOSeed.abs_neg (x.val (n + 1) - x.val n)]
  exact BishopC.le_trans (x.regular (n + 1) n) (eps_succ_add_le_tol n)

/-- Raw self-subtraction is equal to zero. -/
theorem sub_self_raw (x : RegularSeq) : relVal (subVal x.val x.val) zeroVal := by
  intro n
  rw [sub_self_val x.val n]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- `subVal x y` agrees with `addVal x (-y)` at the raw representative level. -/
theorem sub_eq_add_neg_raw (x y : RegularSeq) :
    relVal (subVal x.val y.val) (addVal x.val (negVal y.val)) := by
  intro n
  unfold subVal addVal addIndex negVal
  rw [show
      (x.val (n + 1) - y.val (n + 1))
        - (x.val (n + 1) + -y.val (n + 1))
        = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Reversing a subtraction is raw-equal to negating it. -/
theorem sub_comm_neg_raw (x y : RegularSeq) :
    relVal (subVal x.val y.val) (negVal (subVal y.val x.val)) := by
  intro n
  unfold subVal addIndex negVal
  rw [show
      (x.val (n + 1) - y.val (n + 1))
        - -(y.val (n + 1) - x.val (n + 1))
        = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n



end BishopCReal

