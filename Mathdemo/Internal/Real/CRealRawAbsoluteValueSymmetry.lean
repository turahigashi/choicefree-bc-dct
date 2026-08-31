import Mathdemo.Internal.Real.CRealConstantRawLawsAuditedCRat

/-!
# CReal raw absolute-value symmetry

This closes the representative-level `abs (-x) = abs x` fact needed by the
eventual CReal COFO layer.  No quotient or completeness claim is made here.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Raw CReal `abs (-x) = abs x` at the representative level. -/
theorem abs_neg_raw (x : RegularSeq) : relVal (absVal (negVal x.val)) (absVal x.val) := by
  intro n
  change Le
    (BishopCRat.CRat.absF
      (BishopCRat.CRat.absF (-x.val n) - BishopCRat.CRat.absF (x.val n)))
    (tol n)
  rw [scalarCOFOSeed.abs_neg (x.val n)]
  rw [show BishopCRat.CRat.absF (x.val n) - BishopCRat.CRat.absF (x.val n)
      = (0 : Scalar) from by ring, scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Audited raw absolute-value seed. -/
structure CRealAbsSeed : Type where
  abs_zero_raw : relVal (absVal zeroVal) zeroVal
  abs_neg_raw : ∀ x : RegularSeq, relVal (absVal (negVal x.val)) (absVal x.val)

def cRealAbsSeed : CRealAbsSeed where
  abs_zero_raw := abs_zero_raw
  abs_neg_raw := abs_neg_raw

end BishopCReal

