import Mathdemo.Internal.CRat_iter102

/-!
# COFOC assembly from represented positive shifts

`CRat_iter102` showed that positive-order-data extraction plus represented
positive shifts recovers a global quotient representative selector.  This file
feeds that selector into the existing `CRat_iter99` COFOC assembly path for the
positive-data branch.

The result is not a new construction of shifts or positive `ltQuotData`; it is
the precise reduction of the localized positive-data `COFOC` branch to those
two remaining data-extraction problems.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Represented positive shifts plus positive-order-data extraction supply the
Cauchy-sequence representatives consumed by quotient completeness. -/
def cRealQuotCauchySequenceRepData_of_positiveLTData_and_positiveShift
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (shiftData : CRealQuotPositiveShiftData) :
    CRealQuotCauchySequenceRepData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf) :=
  cRealQuotCauchySequenceRepData_of_globalRep
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)
    (cRealQuotGlobalRep_of_positiveLTData_and_positiveShift
      posDataOf shiftData)

/-- The positive-data branch reaches a live `COFOC` once represented positive
shifts are supplied. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableLTPositiveDataOfPositiveShift
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (shiftData : CRealQuotPositiveShiftData) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithPositiveInverseDecidableLTPositiveDataOfCauchySequenceReps
    A hdec posDataOf
    (cRealQuotCauchySequenceRepData_of_positiveLTData_and_positiveShift
      A hdec posDataOf shiftData)

/-- Compact package for the represented-positive-shift route to `COFOC`. -/
structure CRealQuotDecidableLTPositiveDataPositiveShiftCOFOCPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  positiveLtDataOf : CRealQuotPositiveLTDataOf
  positiveShiftData : CRealQuotPositiveShiftData
  globalRep : ∀ x : CRealQuot, CRealQuotRepWitness x
  cauchySequenceReps : CRealQuotCauchySequenceRepData
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A strict_order_decidable positiveLtDataOf)
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotDecidableLTPositiveDataPositiveShiftCOFOCPackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (shiftData : CRealQuotPositiveShiftData) :
    CRealQuotDecidableLTPositiveDataPositiveShiftCOFOCPackage A where
  strict_order_decidable := hdec
  positiveLtDataOf := posDataOf
  positiveShiftData := shiftData
  globalRep :=
    cRealQuotGlobalRep_of_positiveLTData_and_positiveShift
      posDataOf shiftData
  cauchySequenceReps :=
    cRealQuotCauchySequenceRepData_of_positiveLTData_and_positiveShift
      A hdec posDataOf shiftData
  cofoc :=
    cRealQuotCOFOCWithPositiveInverseDecidableLTPositiveDataOfPositiveShift
      A hdec posDataOf shiftData

/-- Frontier after threading represented positive shifts into the `COFOC`
assembly. -/
structure CRealQuotAfterPositiveShiftCOFOCFrontier : Type where
  represented_positive_shift_route_reaches_cofoc : Prop
  construct_represented_positive_shift_data : Prop
  construct_positive_lt_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterPositiveShiftCOFOCFrontier :
    CRealQuotAfterPositiveShiftCOFOCFrontier where
  represented_positive_shift_route_reaches_cofoc := True
  construct_represented_positive_shift_data := True
  construct_positive_lt_data_extraction := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

set_option linter.style.longLine false

