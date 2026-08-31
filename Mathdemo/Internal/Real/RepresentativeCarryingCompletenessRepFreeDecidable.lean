import Mathdemo.Internal.Real.RepresentativeFreeDecidableOrderCOFOAssembly

/-!
# Representative-carrying completeness for the rep-free decidable COFO branch

`RepresentativeFreeDecidableOrderCOFOAssembly` assembled the non-completeness `COFO` layer for the
decidable-order branch without a global representative selector.  This file
pushes the same cleanup through the already-closed completeness sub-obligations.

The result is deliberately not an opaque `COFOC.complete` theorem: that target
quantifies over arbitrary quotient-valued sequences and supplies no
representatives.  What is closed here is the strongest currently honest
rep-free bridge: if a sequence comes with representatives term by term, then
the closed local-close and diagonal-limit machinery gives a limit, all over
the `RepresentativeFreeDecidableOrderCOFOAssembly` `COFO`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Record-level local close extraction for the representative-free
decidable-order `COFO` branch. -/
def cRealQuotCloseToRepCloseData_of_concreteAbsSubCloseDecidableLTData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (concreteData : CRealQuotConcreteAbsSubCloseToRepCloseData) :
    CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf) where
  close_of_quot_close := by
    intro x y hx hy k hclose
    letI : BishopC.COFO CRealQuot :=
      cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf
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

/-- Closed local quotient-close extraction for the representative-free
decidable-order `COFO` branch. -/
def cRealQuotCloseToRepCloseDataWithPositiveInverseDecidableLTData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf) :=
  cRealQuotCloseToRepCloseData_of_concreteAbsSubCloseDecidableLTData
    A hdec ltDataOf cRealQuotConcreteAbsSubCloseToRepCloseData

/-- Closed quotient-Cauchy to representative-Cauchy extraction for the
representative-free decidable-order `COFO` branch. -/
def cRealQuotCauchyToRepSequenceDataWithPositiveInverseDecidableLTData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCauchyToRepSequenceData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf) :=
  cRealQuotCauchyToRepSequenceData_of_closeBridge
    (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)
    (cRealQuotCloseToRepCloseDataWithPositiveInverseDecidableLTData
      A hdec ltDataOf)

/-- Convert closed representative diagonal closeness into quotient convergence
for the representative-free decidable-order `COFO` branch. -/
def cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTData_of_repClose
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (closeDiag : CRealRepDiagonalLimitCloseData) :
    CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf) where
  limit := closeDiag.limit
  lmod := closeDiag.lmod
  tends := by
    intro w hc k n hn
    letI : BishopC.COFO CRealQuot :=
      cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf
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

/-- Closed diagonal-limit data for the representative-free decidable-order
`COFO` branch. -/
def cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf) :=
  cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTData_of_repClose
    A hdec ltDataOf cRealRepDiagonalLimitCloseData

/-- The fully closed representation-carrying completeness theorem for the
representative-free decidable-order `COFO` branch. -/
def cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotRepCarryingCompletenessData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf) :=
  cRealQuotRepCarryingCompletenessData_of_repDiagonal
    (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)
    (cRealQuotCauchyToRepSequenceDataWithPositiveInverseDecidableLTData
      A hdec ltDataOf)
    (cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTData
      A hdec ltDataOf)

/-- Compact package for the rep-free decidable-order branch through
representation-carrying completeness. -/
structure CRealQuotDecidableLTRepCarryingCompletePackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  cofo : BishopC.COFO CRealQuot
  closeData : CRealQuotCloseToRepCloseData cofo
  repCauchyData : CRealQuotCauchyToRepSequenceData cofo
  diagData : CRealRepDiagonalLimitData cofo
  completeData : CRealQuotRepCarryingCompletenessData cofo

def cRealQuotDecidableLTRepCarryingCompletePackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotDecidableLTRepCarryingCompletePackage A where
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  cofo := cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf
  closeData :=
    cRealQuotCloseToRepCloseDataWithPositiveInverseDecidableLTData
      A hdec ltDataOf
  repCauchyData :=
    cRealQuotCauchyToRepSequenceDataWithPositiveInverseDecidableLTData
      A hdec ltDataOf
  diagData :=
    cRealRepDiagonalLimitDataWithPositiveInverseDecidableLTData
      A hdec ltDataOf
  completeData :=
    cRealQuotRepCarryingCompletenessDataWithPositiveInverseDecidableLTData
      A hdec ltDataOf

/-- Frontier after rep-free representation-carrying completeness is closed. -/
structure CRealQuotAfterRepFreeRepCarryingCompletenessFrontier : Type where
  opaque_quotient_complete_without_global_rep : Prop
  remove_ltDataOf_for_positive_inverse : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterRepFreeRepCarryingCompletenessFrontier :
    CRealQuotAfterRepFreeRepCarryingCompletenessFrontier where
  opaque_quotient_complete_without_global_rep := True
  remove_ltDataOf_for_positive_inverse := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

