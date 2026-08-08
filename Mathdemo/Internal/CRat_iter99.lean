import Mathdemo.Internal.CRat_iter98

/-!
# COFOC assembly after positive order-data localization

`CRat_iter98` propagated the positive-only order-data interface through
representation-carrying completeness.  This file transports the final
`CRat_iter95` bridge as well: once representatives are supplied for the terms
of the Cauchy sequence being completed, the positive-data decidable branch
assembles a live `BishopC.COFOC CRealQuot`.

The remaining representative frontier is unchanged and explicit.  This is not
opaque quotient completeness without representative supply; it is the precise
COFOC assembly under the Cauchy-sequence representative principle, now with the
positive inverse using only `ltQuot zeroQuot x` data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The positive-data decidable branch becomes a live `COFOC` once the
Cauchy-sequence representative principle is supplied. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableLTPositiveDataOfCauchySequenceReps
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (seqReps : CRealQuotCauchySequenceRepData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf)) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCConditionalOfCOFO
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)
    (cRealQuotCOFOCFieldData_of_repCarryingCompleteAndCauchySequenceReps
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf)
      seqReps
      (cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf))

/-- A package exposing the exact remaining representative principle for the
positive-data decidable-order `COFOC` branch. -/
structure CRealQuotDecidableLTPositiveDataCauchyRepCOFOCPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  positiveLtDataOf : CRealQuotPositiveLTDataOf
  cauchySequenceReps : CRealQuotCauchySequenceRepData
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A strict_order_decidable positiveLtDataOf)
  repCarryingCompleteData : CRealQuotRepCarryingCompletenessData
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A strict_order_decidable positiveLtDataOf)
  completeData : CRealQuotCOFOCFieldData
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A strict_order_decidable positiveLtDataOf)
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotDecidableLTPositiveDataCauchyRepCOFOCPackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (seqReps : CRealQuotCauchySequenceRepData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf)) :
    CRealQuotDecidableLTPositiveDataCauchyRepCOFOCPackage A where
  strict_order_decidable := hdec
  positiveLtDataOf := posDataOf
  cauchySequenceReps := seqReps
  repCarryingCompleteData :=
    cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf
  completeData :=
    cRealQuotCOFOCFieldData_of_repCarryingCompleteAndCauchySequenceReps
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf)
      seqReps
      (cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf)
  cofo := cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
    A hdec posDataOf
  cofoc :=
    cRealQuotCOFOCWithPositiveInverseDecidableLTPositiveDataOfCauchySequenceReps
      A hdec posDataOf seqReps

/-- The previous global-representative route still factors through the local
Cauchy-sequence representative interface for the positive-data branch. -/
def cRealQuotDecidableLTPositiveDataCauchyRepCOFOCPackageWithGlobalRep
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x) :
    CRealQuotDecidableLTPositiveDataCauchyRepCOFOCPackage A :=
  cRealQuotDecidableLTPositiveDataCauchyRepCOFOCPackageWith
    A hdec posDataOf
    (cRealQuotCauchySequenceRepData_of_globalRep
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf)
      rep)

/-- Frontier after the positive-data branch reaches the local-representative
`COFOC` assembly point. -/
structure CRealQuotAfterPositiveDataCauchyRepCOFOCFrontier : Type where
  cauchy_sequence_rep_principle : Prop
  construct_positive_lt_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterPositiveDataCauchyRepCOFOCFrontier :
    CRealQuotAfterPositiveDataCauchyRepCOFOCFrontier where
  cauchy_sequence_rep_principle := True
  construct_positive_lt_data_extraction := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

set_option linter.style.longLine false

