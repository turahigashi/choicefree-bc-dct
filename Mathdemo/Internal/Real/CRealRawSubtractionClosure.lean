import Mathdemo.Internal.Real.CRealRawAdditiveAlgebraLaws

/-!
# CReal raw subtraction closure

The order frontiers are stated in terms of `subVal`, so this file records
regularity and quotient-respect for subtraction at the representative level.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Subtraction preserves regularity of representatives. -/
theorem sub_regular (x y : RegularSeq) : RegularVal (subVal x.val y.val) := by
  intro m n
  unfold subVal addIndex
  have htri : Le
      (COF.abs ((x.val (m + 1) - y.val (m + 1)) - (x.val (n + 1) - y.val (n + 1))))
      (COF.abs (x.val (m + 1) - x.val (n + 1))
        + COF.abs (y.val (m + 1) - y.val (n + 1))) := by
    have h := scalar_abs_add_le
      (x.val (m + 1) - x.val (n + 1))
      (-(y.val (m + 1) - y.val (n + 1)))
    rw [show (x.val (m + 1) - x.val (n + 1))
        + -(y.val (m + 1) - y.val (n + 1))
        = (x.val (m + 1) - y.val (m + 1)) - (x.val (n + 1) - y.val (n + 1))
        from by ring] at h
    rwa [show COF.abs (-(y.val (m + 1) - y.val (n + 1)))
        = COF.abs (y.val (m + 1) - y.val (n + 1)) from by
          exact scalarCOFOSeed.abs_neg (y.val (m + 1) - y.val (n + 1))] at h
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




end BishopCReal

