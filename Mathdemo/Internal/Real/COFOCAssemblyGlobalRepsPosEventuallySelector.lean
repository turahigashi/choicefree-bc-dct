import Mathdemo.Internal.Real.PosEventuallyWitnessSelectorFrontier

/-!
# COFOC assembly from global reps and a PosEventually selector

`PosEventuallyWitnessSelectorFrontier` exposed the remaining positivity bridge as a selector for the
`k, N` witnesses inside `PosEventually`.  This file threads that selector
through the localized positive-order-data branch from `LocalizingOrderDataExtractionPositiveInverse` through
`COFOCAssemblyAfterPositiveOrderData`.

The result is an audit package, not a new construction of the selector or of
strict-order decidability: in the current decidable-order branch, global
representatives plus a `PosEventually` selector are enough to supply the
positive `ltQuotData` consumed by the positive inverse and hence the existing
`COFOC` assembly route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The positive-data branch of `COFO` supplied by a global representative
selector and the representative-level `PosEventually` selector. -/
@[reducible] def cRealQuotCOFOWithDecidableLTGlobalRepPosEventuallySelector
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
    A hdec
    (cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallySelector
      rep sel)

/-- The same global representative selector supplies the local
Cauchy-sequence representatives consumed by quotient completeness. -/
def cRealQuotCauchySequenceRepData_of_globalRep_and_posEventuallySelector
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotCauchySequenceRepData
      (cRealQuotCOFOWithDecidableLTGlobalRepPosEventuallySelector
        A hdec rep sel) :=
  cRealQuotCauchySequenceRepData_of_globalRep
    (cRealQuotCOFOWithDecidableLTGlobalRepPosEventuallySelector
      A hdec rep sel)
    rep

/-- The current decidable-order quotient route reaches `COFOC` from global
representatives and a `PosEventually` witness selector. -/
@[reducible] def cRealQuotCOFOCWithDecidableLTGlobalRepPosEventuallySelector
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithPositiveInverseDecidableLTPositiveDataOfCauchySequenceReps
    A hdec
    (cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallySelector
      rep sel)
    (cRealQuotCauchySequenceRepData_of_globalRep_and_posEventuallySelector
      A hdec rep sel)

/-- Compact package for the latest audited route to `COFOC`.  It records the
three remaining inputs without hiding them behind the older general
`ltQuot -> ltQuotData` obligation. -/
structure CRealQuotDecidableLTGlobalRepPosEventuallySelectorCOFOCPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  globalRep : ∀ x : CRealQuot, CRealQuotRepWitness x
  posEventuallySelector : CRealPosEventuallySelector
  positiveLtDataOf : CRealQuotPositiveLTDataOf
  cauchySequenceReps : CRealQuotCauchySequenceRepData
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A strict_order_decidable positiveLtDataOf)
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotDecidableLTGlobalRepPosEventuallySelectorCOFOCPackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotDecidableLTGlobalRepPosEventuallySelectorCOFOCPackage A where
  strict_order_decidable := hdec
  globalRep := rep
  posEventuallySelector := sel
  positiveLtDataOf :=
    cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallySelector
      rep sel
  cauchySequenceReps :=
    cRealQuotCauchySequenceRepData_of_globalRep
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec
        (cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallySelector
          rep sel))
      rep
  cofo :=
    cRealQuotCOFOWithDecidableLTGlobalRepPosEventuallySelector
      A hdec rep sel
  cofoc :=
    cRealQuotCOFOCWithDecidableLTGlobalRepPosEventuallySelector
      A hdec rep sel

/-- Frontier after threading the `PosEventually` selector through the current
positive-data `COFOC` assembly branch. -/
structure CRealQuotAfterGlobalRepPosEventuallySelectorCOFOCFrontier
    : Type where
  global_rep_plus_pos_eventually_selector_reaches_positive_lt_data : Prop
  current_decidable_branch_reaches_cofoc_from_global_rep_and_selector : Prop
  construct_or_remove_strict_order_decidability : Prop
  construct_global_representatives_or_replace_quotient_encoding : Prop
  construct_or_avoid_pos_eventually_selector : Prop

def cRealQuotAfterGlobalRepPosEventuallySelectorCOFOCFrontier :
    CRealQuotAfterGlobalRepPosEventuallySelectorCOFOCFrontier where
  global_rep_plus_pos_eventually_selector_reaches_positive_lt_data := True
  current_decidable_branch_reaches_cofoc_from_global_rep_and_selector := True
  construct_or_remove_strict_order_decidability := True
  construct_global_representatives_or_replace_quotient_encoding := True
  construct_or_avoid_pos_eventually_selector := True

end BishopCReal

set_option linter.style.longLine false

