import Mathdemo.Internal.Real.RepresentativeCarryingCompletenessRepFreeDecidable

/-!
# COFOC assembly from Cauchy-sequence representative data

`RepresentativeCarryingCompletenessRepFreeDecidable` closed representation-carrying completeness for the
representative-free decidable-order `COFO` branch.  The remaining gap to the
opaque `COFOC.complete` field is exactly representative supply for an arbitrary
Cauchy quotient sequence.

This file isolates that weaker and more precise principle.  Instead of asking
for a global representative selector for every quotient element, it asks only
for representatives of the terms of the Cauchy sequence currently being
completed.  Given that data, the `RepresentativeCarryingCompletenessRepFreeDecidable` completeness theorem assembles a
live `BishopC.COFOC CRealQuot` record for the rep-free decidable branch.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative supply restricted to quotient-valued Cauchy sequences.

This is strictly more local than the previous global selector
`forall x, CRealQuotRepWitness x`: the provider only has to respond after a
specific sequence and its `IsCauchy` proof are known. -/
structure CRealQuotCauchySequenceRepData
    (cofo : BishopC.COFO CRealQuot) : Type 1 where
  reps :
    letI : BishopC.COFO CRealQuot := cofo
    ∀ {v : Nat → CRealQuot}, IsCauchy v →
      ∀ n : Nat, CRealQuotRepWitness (v n)

/-- A global representative selector is sufficient for the local Cauchy-sequence
representative principle.  This keeps the auxiliary construction available while naming the
smaller interface actually consumed by completeness. -/
def cRealQuotCauchySequenceRepData_of_globalRep
    (cofo : BishopC.COFO CRealQuot)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x) :
    CRealQuotCauchySequenceRepData cofo where
  reps := by
    intro v _hv n
    exact rep (v n)

/-- Bridge from representation-carrying completeness to the opaque quotient
`COFOC` field using only Cauchy-sequence representative data. -/
def cRealQuotCOFOCFieldData_of_repCarryingCompleteAndCauchySequenceReps
    (cofo : BishopC.COFO CRealQuot)
    (seqReps : CRealQuotCauchySequenceRepData cofo)
    (completeData : CRealQuotRepCarryingCompletenessData cofo) :
    CRealQuotCOFOCFieldData cofo where
  complete := by
    intro v hv
    exact completeData.complete_with_reps
      (seqReps.reps (v := v) hv) hv

/-- The rep-free decidable-order branch becomes a live `COFOC` once the
Cauchy-sequence representative principle is supplied. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableLTDataOfCauchySequenceReps
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (seqReps : CRealQuotCauchySequenceRepData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCConditionalOfCOFO
    (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)
    (cRealQuotCOFOCFieldData_of_repCarryingCompleteAndCauchySequenceReps
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)
      seqReps
      (cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTData
        A hdec ltDataOf))

/-- A package exposing the exact remaining representative principle for the
rep-free decidable-order `COFOC` branch. -/
structure CRealQuotDecidableLTCauchyRepCOFOCPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  cauchySequenceReps : CRealQuotCauchySequenceRepData
    (cRealQuotCOFOWithPositiveInverseDecidableLTData
      A strict_order_decidable ltDataOf)
  repCarryingCompleteData : CRealQuotRepCarryingCompletenessData
    (cRealQuotCOFOWithPositiveInverseDecidableLTData
      A strict_order_decidable ltDataOf)
  completeData : CRealQuotCOFOCFieldData
    (cRealQuotCOFOWithPositiveInverseDecidableLTData
      A strict_order_decidable ltDataOf)
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotDecidableLTCauchyRepCOFOCPackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (seqReps : CRealQuotCauchySequenceRepData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)) :
    CRealQuotDecidableLTCauchyRepCOFOCPackage A where
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  cauchySequenceReps := seqReps
  repCarryingCompleteData :=
    cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTData
      A hdec ltDataOf
  completeData :=
    cRealQuotCOFOCFieldData_of_repCarryingCompleteAndCauchySequenceReps
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)
      seqReps
      (cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTData
        A hdec ltDataOf)
  cofo := cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf
  cofoc :=
    cRealQuotCOFOCWithPositiveInverseDecidableLTDataOfCauchySequenceReps
      A hdec ltDataOf seqReps

/-- The previous global-representative route factors through the new local
Cauchy-sequence representative interface. -/
def cRealQuotDecidableLTCauchyRepCOFOCPackageWithGlobalRep
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x) :
    CRealQuotDecidableLTCauchyRepCOFOCPackage A :=
  cRealQuotDecidableLTCauchyRepCOFOCPackageWith
    A hdec ltDataOf
    (cRealQuotCauchySequenceRepData_of_globalRep
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)
      rep)

/-- Frontier after `COFOC` assembly has been reduced to the precise
Cauchy-sequence representative principle. -/
structure CRealQuotAfterCauchyRepCOFOCFrontier : Type where
  cauchy_sequence_rep_principle : Prop
  remove_ltDataOf_for_positive_inverse : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterCauchyRepCOFOCFrontier :
    CRealQuotAfterCauchyRepCOFOCFrontier where
  cauchy_sequence_rep_principle := True
  remove_ltDataOf_for_positive_inverse := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

