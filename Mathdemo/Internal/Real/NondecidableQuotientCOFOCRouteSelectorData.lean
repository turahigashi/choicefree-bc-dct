import Mathdemo.Internal.Real.DataValuedQuotientCOFOrderLayer

/-!
# Nondecidable quotient COFOC route from selector data and inverse totalization

`DataValuedQuotientCOFOrderLayer` separated the data-valued order layer from the live Prop-valued
`COF` interface.  Together with the `PosEventuallyWitnessSelectorFrontier` `PosEventually` selector,
this gives the missing `ltQuot -> ltQuotData` bridge without asking for a
global strict-order decision procedure.

This file threads that bridge through the already-closed positive-inverse and
completeness machinery.  The remaining constructive inputs are now explicit:

* a global representative selector for quotient elements;
* a selector for the witnesses hidden in `PosEventually`;
* a totalization of the data-indexed positive inverse.

No `CRealQuotLTDecidable` hypothesis appears in the assembled `COFO`/`COFOC`
route below.  Decidability remains only as one optional way to build the
inverse totalization datum from `SplittingPositiveInverseDataTotalInverse`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Short name for the selector-supplied Prop-to-data strict-order bridge. -/
abbrev cRealQuotLTDataOfGlobalRepPosEventuallySelector
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotPropLTToDataLTObligation :=
  cRealQuotLTDataOf_of_globalRep_and_posEventuallySelector rep sel

/-- Short name for the positive-order specialization of the same bridge. -/
abbrev cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotPositiveLTDataOf :=
  cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallySelector rep sel

/-- The data-valued order package from `DataValuedQuotientCOFOrderLayer`, specialized to global
representatives plus a `PosEventually` selector. -/
def cRealQuotDataCOFToLiveCOFPackageWithGlobalRepPosEventuallySelector
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotDataCOFToLiveCOFPackage A :=
  cRealQuotDataCOFToLiveCOFPackageWith A rep
    (cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel)

/-- Live `COF` route from global representatives and a `PosEventually`
selector.  This uses the original representative/data-order `COF` record so it
can reuse the closed `COFO` field chain. -/
@[reducible] def cRealQuotCOFWithGlobalRepPosEventuallySelector
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    BishopC.COF CRealQuot :=
  cRealQuotCOFConditionalWith A rep
    (cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel)

/-- Positive-inverse field data for the nondecidable order route, using an
abstract totalization of the proof-indexed positive inverse. -/
def cRealQuotPositiveInverseFieldDataWithGlobalRepSelectorTotalized
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealQuotPositiveInverseFieldData
      (cRealQuotCOFWithGlobalRepPosEventuallySelector A rep sel) where
  inv := tot.inv
  mul_inv_cancel := by
    intro x hx
    change ltQuot zeroQuot x at hx
    let h : ltQuotData zeroQuot x :=
      cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector rep sel hx
    change mulQuotConcreteWith A x (tot.inv x) = oneQuot
    rw [tot.agrees_on_positive_data h]
    exact positiveQuot_mul_invWithData_eq_one A h
  inv_pos := by
    intro x hx
    change ltQuot zeroQuot x at hx
    let h : ltQuotData zeroQuot x :=
      cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector rep sel hx
    change ltQuot zeroQuot (tot.inv x)
    rw [tot.agrees_on_positive_data h]
    exact positiveQuotInvWithData_pos A h

/-- Live `COFO` with no strict-order decidability hypothesis.  The total
inverse is supplied separately by `tot`. -/
@[reducible] def cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOWithPositiveInverse A rep
    (cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel)
    (cRealQuotPositiveInverseFieldDataWithGlobalRepSelectorTotalized
      A rep sel tot)

/-- Local quotient-close extraction for the nondecidable totalized `COFO`
route.  This is the previous concrete-close bridge with the obsolete decidability
parameter removed. -/
def cRealQuotCloseToRepCloseDataWithGlobalRepSelectorTotalized
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
        A rep sel tot) where
  close_of_quot_close := by
    intro x y hx hy k hclose
    letI : BishopC.COFO CRealQuot :=
      cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
        A rep sel tot
    have h_record :
        ltQuot
          (absQuot (x - y))
          (constQuot (eps k)) := by
      change
        ltQuot
          (absQuot (x - y))
          (@COF.halfPow CRealQuot
            (cRealQuotCOFWithGlobalRepPosEventuallySelector A rep sel) k)
        at hclose
      rwa [halfPowQuot_eq_const_eps_with A rep
        (cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel) k]
        at hclose
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
    exact (cRealQuotConcreteAbsSubCloseToRepCloseData).close_of_abs_sub_const
      hx.rep hy.rep k h_mk

/-- Quotient-Cauchy to representative-Cauchy extraction for the nondecidable
totalized route. -/
def cRealQuotCauchyToRepSequenceDataWithGlobalRepSelectorTotalized
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealQuotCauchyToRepSequenceData
      (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
        A rep sel tot) :=
  cRealQuotCauchyToRepSequenceData_of_closeBridge
    (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
      A rep sel tot)
    (cRealQuotCloseToRepCloseDataWithGlobalRepSelectorTotalized
      A rep sel tot)

/-- Representative diagonal-limit data for the nondecidable totalized route. -/
def cRealRepDiagonalLimitDataWithGlobalRepSelectorTotalized_of_repClose
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A)
    (closeDiag : CRealRepDiagonalLimitCloseData) :
    CRealRepDiagonalLimitData
      (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
        A rep sel tot) where
  limit := closeDiag.limit
  lmod := closeDiag.lmod
  tends := by
    intro w hc k n hn
    letI : BishopC.COFO CRealQuot :=
      cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
        A rep sel tot
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
          (cRealQuotCOFWithGlobalRepPosEventuallySelector A rep sel) k)
    rw [hsub, halfPowQuot_eq_const_eps_with A rep
      (cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel) k]
    exact hlt

/-- The already-closed representative diagonal construction, retyped for the
nondecidable totalized route. -/
def cRealRepDiagonalLimitDataWithGlobalRepSelectorTotalized
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealRepDiagonalLimitData
      (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
        A rep sel tot) :=
  cRealRepDiagonalLimitDataWithGlobalRepSelectorTotalized_of_repClose
    A rep sel tot cRealRepDiagonalLimitCloseData

/-- Representation-carrying completeness for the nondecidable totalized
`COFO`. -/
def cRealQuotRepCarryingCompletenessDataWithGlobalRepSelectorTotalized
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealQuotRepCarryingCompletenessData
      (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
        A rep sel tot) :=
  cRealQuotRepCarryingCompletenessData_of_closeBridgeAndDiagonal
    (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
      A rep sel tot)
    (cRealQuotCloseToRepCloseDataWithGlobalRepSelectorTotalized
      A rep sel tot)
    (cRealRepDiagonalLimitDataWithGlobalRepSelectorTotalized
      A rep sel tot)

/-- Opaque quotient sequential-completeness field, using the supplied global
representative selector at the final bridge. -/
def cRealQuotCOFOCFieldDataWithGlobalRepSelectorTotalized
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealQuotCOFOCFieldData
      (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
        A rep sel tot) :=
  cRealQuotCOFOCFieldData_of_repCarryingComplete
    (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
      A rep sel tot)
    rep
    (cRealQuotRepCarryingCompletenessDataWithGlobalRepSelectorTotalized
      A rep sel tot)

/-- Live `COFOC` route with no strict-order decidability hypothesis. -/
@[reducible] def cRealQuotCOFOCWithGlobalRepPosEventuallySelectorTotalized
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCConditionalOfCOFO
    (cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
      A rep sel tot)
    (cRealQuotCOFOCFieldDataWithGlobalRepSelectorTotalized
      A rep sel tot)

/-- Decidable positivity remains available as one way to provide the new
inverse-totalization input; it is no longer part of the order or completeness
assembly itself. -/
@[reducible] def cRealQuotCOFOCWithGlobalRepPosEventuallySelectorDecidableTotalization
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithGlobalRepPosEventuallySelectorTotalized
    A rep sel
    (cRealQuotPositiveInverseTotalizationData_of_decidablePositiveData
      A hdec
      (cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector rep sel))

/-- Compact status package for the new nondecidable route. -/
structure CRealQuotGlobalRepSelectorTotalizedCOFOCPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  globalRep : ∀ x : CRealQuot, CRealQuotRepWitness x
  posEventuallySelector : CRealPosEventuallySelector
  totalization : CRealQuotPositiveInverseTotalizationData A
  ltDataOf : CRealQuotPropLTToDataLTObligation
  positiveLtDataOf : CRealQuotPositiveLTDataOf
  dataCOFPackage : CRealQuotDataCOFToLiveCOFPackage A
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotGlobalRepSelectorTotalizedCOFOCPackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealQuotGlobalRepSelectorTotalizedCOFOCPackage A where
  globalRep := rep
  posEventuallySelector := sel
  totalization := tot
  ltDataOf := cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel
  positiveLtDataOf :=
    cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector rep sel
  dataCOFPackage :=
    cRealQuotDataCOFToLiveCOFPackageWithGlobalRepPosEventuallySelector
      A rep sel
  cofo := cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
    A rep sel tot
  cofoc := cRealQuotCOFOCWithGlobalRepPosEventuallySelectorTotalized
    A rep sel tot

/-- Frontier after the strict-order-decidability branch has been removed from
the live `COFOC` assembly. -/
structure CRealQuotAfterGlobalRepSelectorTotalizedCOFOCFrontier : Type where
  live_cofoc_no_longer_requires_strict_order_decidability : Prop
  inverse_totalization_remains_explicit : Prop
  global_representative_selector_remains_explicit : Prop
  pos_eventually_selector_remains_explicit : Prop
  data_order_layer_available_without_decidable_order : Prop

def cRealQuotAfterGlobalRepSelectorTotalizedCOFOCFrontier :
    CRealQuotAfterGlobalRepSelectorTotalizedCOFOCFrontier where
  live_cofoc_no_longer_requires_strict_order_decidability := True
  inverse_totalization_remains_explicit := True
  global_representative_selector_remains_explicit := True
  pos_eventually_selector_remains_explicit := True
  data_order_layer_available_without_decidable_order := True

end BishopCReal

set_option linter.style.longLine false

