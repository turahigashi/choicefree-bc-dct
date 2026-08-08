import Mathdemo.Internal.CRat_iter97

/-!
# Rep-carrying completeness after positive order-data localization

`CRat_iter97` localized the remaining `ltQuotData` extraction used by the
positive inverse to the shape `ltQuot zeroQuot x -> ltQuotData zeroQuot x`.
This file propagates that cleanup through the representation-carrying
completeness layer from `CRat_iter94`.

The result is still not the opaque `COFOC.complete` theorem.  As before, the
complete branch is honest only for quotient Cauchy sequences whose terms come
with representatives.  The improvement here is that this whole
representation-carrying bridge now uses only positive-branch order-data
extraction, not a general extractor for arbitrary strict inequalities.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Record-level local close extraction for the decidable-order `COFO` branch
with positive-only order-data extraction. -/
def cRealQuotCloseToRepCloseData_of_concreteAbsSubCloseDecidableLTPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (concreteData : CRealQuotConcreteAbsSubCloseToRepCloseData) :
    CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf) where
  close_of_quot_close := by
    intro x y hx hy k hclose
    letI : BishopC.COFO CRealQuot :=
      cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf
    have h_record :
        ltQuot
          (absQuot (x - y))
          (constQuot (eps k)) := by
      change
        ltQuot
          (absQuot (x - y))
          (@COF.halfPow CRealQuot
            (cRealQuotCOFConditionalWithDecidableLT A hdec) k) at hclose
      rwa [halfPowQuot_eq_const_eps_with_decidable A hdec k] at hclose
    have h_mk :
        ltQuot
          (absQuot (mkQuot hx.rep - mkQuot hy.rep))
          (constQuot (eps k)) := by
      rw [hx.eq_mk, hy.eq_mk] at h_record
      exact h_record
    have h_sub :
        mkQuot hx.rep - mkQuot hy.rep =
          subQuot (mkQuot hx.rep) (mkQuot hy.rep) := by
      change addQuot (mkQuot hx.rep) (negQuot (mkQuot hy.rep)) =
        subQuot (mkQuot hx.rep) (mkQuot hy.rep)
      exact (subQuot_eq_add_neg (mkQuot hx.rep) (mkQuot hy.rep)).symm
    rw [h_sub] at h_mk
    exact concreteData.close_of_abs_sub_const hx.rep hy.rep k h_mk

/-- Closed local quotient-close extraction for the positive-data branch. -/
def cRealQuotCloseToRepCloseDataWithPositiveInverseDecidableLTPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf) :=
  cRealQuotCloseToRepCloseData_of_concreteAbsSubCloseDecidableLTPositiveData
    A hdec posDataOf cRealQuotConcreteAbsSubCloseToRepCloseData

/-- Closed quotient-Cauchy to representative-Cauchy extraction for the
positive-data branch. -/
def cRealQuotCauchyToRepSequenceDataWithPositiveInverseDecidableLTPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotCauchyToRepSequenceData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf) :=
  cRealQuotCauchyToRepSequenceData_of_closeBridge
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)
    (cRealQuotCloseToRepCloseDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)

/-- Convert closed representative diagonal closeness into quotient convergence
for the positive-data branch. -/
def cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTPositiveData_of_repClose
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (closeDiag : CRealRepDiagonalLimitCloseData) :
    CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf) where
  limit := closeDiag.limit
  lmod := closeDiag.lmod
  tends := by
    intro w hc k n hn
    letI : BishopC.COFO CRealQuot :=
      cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf
    let limitRep : RegularSeq := closeDiag.limit w hc
    have hlt :
        ltQuot
          (absQuot (subQuot (mkQuot (w n)) (mkQuot limitRep)))
          (constQuot (eps k)) :=
      ltQuot_abs_sub_const_of_repClose_succ (w n) limitRep k
        (closeDiag.close_to_limit w hc k n hn)
    have hsub :
        mkQuot (w n) - mkQuot limitRep =
          subQuot (mkQuot (w n)) (mkQuot limitRep) := by
      change addQuot (mkQuot (w n)) (negQuot (mkQuot limitRep)) =
        subQuot (mkQuot (w n)) (mkQuot limitRep)
      exact (subQuot_eq_add_neg (mkQuot (w n)) (mkQuot limitRep)).symm
    change
      ltQuot
        (absQuot (mkQuot (w n) - mkQuot limitRep))
        (@COF.halfPow CRealQuot
          (cRealQuotCOFConditionalWithDecidableLT A hdec) k)
    rw [hsub, halfPowQuot_eq_const_eps_with_decidable A hdec k]
    exact hlt

/-- Closed diagonal-limit data for the positive-data branch. -/
def cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf) :=
  cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTPositiveData_of_repClose
    A hdec posDataOf cRealRepDiagonalLimitCloseData

/-- The fully closed representation-carrying completeness theorem for the
positive-data branch. -/
def cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotRepCarryingCompletenessData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
        A hdec posDataOf) :=
  cRealQuotRepCarryingCompletenessData_of_repDiagonal
    (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)
    (cRealQuotCauchyToRepSequenceDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)
    (cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)

/-- Compact package for the positive-data branch through
representation-carrying completeness. -/
structure CRealQuotDecidableLTPositiveDataRepCarryingCompletePackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  positiveLtDataOf : CRealQuotPositiveLTDataOf
  cofo : BishopC.COFO CRealQuot
  closeData : CRealQuotCloseToRepCloseData cofo
  repCauchyData : CRealQuotCauchyToRepSequenceData cofo
  diagData : CRealRepDiagonalLimitData cofo
  completeData : CRealQuotRepCarryingCompletenessData cofo

def cRealQuotDecidableLTPositiveDataRepCarryingCompletePackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotDecidableLTPositiveDataRepCarryingCompletePackage A where
  strict_order_decidable := hdec
  positiveLtDataOf := posDataOf
  cofo := cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
    A hdec posDataOf
  closeData :=
    cRealQuotCloseToRepCloseDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf
  repCauchyData :=
    cRealQuotCauchyToRepSequenceDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf
  diagData :=
    cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf
  completeData :=
    cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf

/-- The previous general-data completeness branch factors through the localized
positive-data interface. -/
def cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTData_asPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotRepCarryingCompletenessData
      (cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData A hdec
        (cRealQuotPositiveLTDataOf_of_ltDataOf ltDataOf)) :=
  cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTPositiveData
    A hdec (cRealQuotPositiveLTDataOf_of_ltDataOf ltDataOf)

/-- Frontier after representation-carrying completeness has been propagated to
the positive-data branch. -/
structure CRealQuotAfterPositiveDataRepCarryingCompletenessFrontier : Type where
  opaque_quotient_complete_without_cauchy_sequence_reps : Prop
  construct_positive_lt_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterPositiveDataRepCarryingCompletenessFrontier :
    CRealQuotAfterPositiveDataRepCarryingCompletenessFrontier where
  opaque_quotient_complete_without_cauchy_sequence_reps := True
  construct_positive_lt_data_extraction := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

set_option linter.style.longLine false

