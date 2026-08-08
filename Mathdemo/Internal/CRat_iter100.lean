import Mathdemo.Internal.CRat_iter99

/-!
# Cauchy-sequence representatives audit for the positive-data branch

`CRat_iter99` assembled the localized positive-data decidable branch into a
`COFOC` once Cauchy-sequence representatives are supplied.  `CRat_iter96`
already proved the general audit: because constant quotient-valued sequences
are Cauchy in any `COFO`, representatives for all Cauchy sequences recover a
global representative selector.

This file specializes that audit to the positive-data branch, so the remaining
representative frontier is stated without ambiguity for the latest branch.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- In the positive-data decidable branch, Cauchy-sequence representative data
already implies a global representative selector. -/
def cRealQuotGlobalRepOfDecidableLTPositiveDataCauchySequenceReps
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (seqReps : CRealQuotCauchySequenceRepData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf)) :
    ∀ x : CRealQuot, CRealQuotRepWitness x :=
  cRealQuotGlobalRep_of_cauchySequenceRepData
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)
    seqReps

/-- The local Cauchy-sequence representative principle and the previous global
representative selector remain interderivable for the positive-data branch. -/
def cRealQuotPositiveDataCauchySequenceRepDataEquivGlobal
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotCauchySequenceRepDataEquivGlobal
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf) :=
  cRealQuotCauchySequenceRepDataEquivGlobal
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)

/-- Frontier after the localized branch's Cauchy-representative audit. -/
structure CRealQuotAfterPositiveDataCauchyRepAuditFrontier : Type where
  cauchy_sequence_reps_equivalent_to_global_rep : Prop
  construct_positive_lt_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterPositiveDataCauchyRepAuditFrontier :
    CRealQuotAfterPositiveDataCauchyRepAuditFrontier where
  cauchy_sequence_reps_equivalent_to_global_rep := True
  construct_positive_lt_data_extraction := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

set_option linter.style.longLine false

