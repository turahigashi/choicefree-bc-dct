import Mathdemo.Internal.Real.CompletenessFrontierSplitConditionalQuotientBranch

/-!
# Local quotient-close extraction for the completeness frontier

`CompletenessFrontierSplitConditionalQuotientBranch` split representation-carrying completeness into two obligations.
This file refines the first one.  Instead of treating quotient-Cauchy to
representative-Cauchy conversion as a monolith, it isolates the local step:

```
|x - y| < 2^-k  on quotient elements
```

plus explicit representatives for `x` and `y` should give tail closeness at
gauge `k` for those representatives.  Given that local bridge, the full
sequence-level extraction from `IsCauchy` is a direct checked construction.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Local bridge needed to read the live quotient Cauchy predicate back as a
representative-level tail-close statement.  This is still an obligation: proving
it requires unpacking the quotient strict-order witness without silently
choosing representatives. -/
structure CRealQuotCloseToRepCloseData
    (cofo : BishopC.COFO CRealQuot) : Type 1 where
  close_of_quot_close :
    letI : BishopC.COFO CRealQuot := cofo
    ∀ {x y : CRealQuot},
      (hx : CRealQuotRepWitness x) →
      (hy : CRealQuotRepWitness y) →
      ∀ k : Nat,
        COF.lt (COF.abs (x - y)) (COF.halfPow (R := CRealQuot) k) →
          RepCloseAtGauge k hx.rep hy.rep

/-- Sequence-level quotient-Cauchy extraction follows immediately from the
local quotient-close bridge and the modulus carried by `IsCauchy`. -/
def cRealQuotCauchyToRepSequenceData_of_closeBridge
    (cofo : BishopC.COFO CRealQuot)
    (closeData : CRealQuotCloseToRepCloseData cofo) :
    CRealQuotCauchyToRepSequenceData cofo where
  rep_cauchy := by
    intro v vreps hv
    refine ⟨hv.cmod, ?_⟩
    intro k m n hm hn
    exact closeData.close_of_quot_close (vreps m) (vreps n) k
      (hv.ccond k m n hm hn)

/-- The completeness bridge after replacing the first sub-obligation by its
local quotient-close form. -/
def cRealQuotRepCarryingCompletenessData_of_closeBridgeAndDiagonal
    (cofo : BishopC.COFO CRealQuot)
    (closeData : CRealQuotCloseToRepCloseData cofo)
    (diagData : CRealRepDiagonalLimitData cofo) :
    CRealQuotRepCarryingCompletenessData cofo :=
  cRealQuotRepCarryingCompletenessData_of_repDiagonal cofo
    (cRealQuotCauchyToRepSequenceData_of_closeBridge cofo closeData)
    diagData

/-- Direct final assembly for the positive-inverse conditional branch after the
first completeness sub-obligation has been localized. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableOfCloseBridgeAndDiagonal
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (closeData : CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf))
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithPositiveInverseDecidableOfRepDiagonal
    A rep hdec ltDataOf
    (cRealQuotCauchyToRepSequenceData_of_closeBridge
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
      closeData)
    diagData

/-- Compact package for the frontier after quotient-Cauchy extraction has been
reduced to the local quotient-close bridge. -/
structure CRealQuotPositiveInverseCOFOCLocalClosePackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  closeData : CRealQuotCloseToRepCloseData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  diagData : CRealRepDiagonalLimitData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  repCauchyData : CRealQuotCauchyToRepSequenceData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  completeData : CRealQuotRepCarryingCompletenessData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotPositiveInverseCOFOCLocalClosePackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (closeData : CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf))
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    CRealQuotPositiveInverseCOFOCLocalClosePackage A where
  rep := rep
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  closeData := closeData
  diagData := diagData
  repCauchyData :=
    cRealQuotCauchyToRepSequenceData_of_closeBridge
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
      closeData
  completeData :=
    cRealQuotRepCarryingCompletenessData_of_closeBridgeAndDiagonal
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
      closeData diagData
  cofo := cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf
  cofoc := cRealQuotCOFOCWithPositiveInverseDecidableOfCloseBridgeAndDiagonal
    A rep hdec ltDataOf closeData diagData

/-- Exact frontier after this file. -/
structure CRealQuotAfterLocalCloseCompletenessFrontier : Type where
  local_quotient_close_to_rep_close : Prop
  representative_diagonal_limit : Prop
  remove_global_rep_witness : Prop
  remove_decidable_order_fork : Prop

def cRealQuotAfterLocalCloseCompletenessFrontier :
    CRealQuotAfterLocalCloseCompletenessFrontier where
  local_quotient_close_to_rep_close := True
  representative_diagonal_limit := True
  remove_global_rep_witness := True
  remove_decidable_order_fork := True

end BishopCReal

