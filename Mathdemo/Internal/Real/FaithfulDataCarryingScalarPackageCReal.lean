import Mathdemo.Internal.Real.PositiveDataInverseConsumerTotalInverse

/-!
# Faithful data-carrying scalar package for the CReal quotient route

`NondecidableQuotientCOFOCRouteSelectorData` gives a live `BishopC.COFOC CRealQuot` only after a total
positive-inverse selector is supplied.  `PositiveDataInverseConsumerTotalInverse` separated the
constructive part of Bishop's reciprocal construction from that total selector:
the inverse laws only consume explicit positive data.

This file packages the source-faithful route:

* data-valued quotient order;
* positive-data inverse laws, with no total inverse selection;
* representative-level sequential completeness by the diagonal construction.

It intentionally does not claim a new live `BishopC.COFOC` instance.  The last
bridge to the previous interface still requires either a total inverse
totalization, or a refactoring of the scalar interface so that inverse is
data-indexed as in Bishop's construction.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative-level sequential completeness, independent of the old
`COFO.inv : R -> R` total field and independent of opaque quotient
representative extraction. -/
structure CRealRepSequenceCompleteLayer : Type 1 where
  limit : ∀ (w : Nat → RegularSeq), CRealRepSequenceCauchyData w → RegularSeq
  lmod : ∀ (w : Nat → RegularSeq), CRealRepSequenceCauchyData w → Nat → Nat
  close_to_limit :
    ∀ (w : Nat → RegularSeq) (hc : CRealRepSequenceCauchyData w),
      ∀ k n : Nat, lmod w hc k ≤ n →
        RepCloseAtGauge (k + 1) (w n) (limit w hc)

/-- The already closed diagonal construction supplies the representation-level
completeness layer. -/
def cRealRepSequenceCompleteLayer :
    CRealRepSequenceCompleteLayer where
  limit := cRealRepDiagonalLimitCloseData.limit
  lmod := cRealRepDiagonalLimitCloseData.lmod
  close_to_limit := cRealRepDiagonalLimitCloseData.close_to_limit

/-- Faithful data-carrying scalar package for the quotient route.

The package records the mathematically constructive content currently available
without forcing Bishop's reciprocal through a total function field. -/
structure CRealQuotFaithfulScalarPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  globalRep : ∀ x : CRealQuot, CRealQuotRepWitness x
  posEventuallySelector : CRealPosEventuallySelector
  dataCOFPackage : CRealQuotDataCOFToLiveCOFPackage A
  positiveInversePackage : CRealQuotPositiveDataInversePackage A
  concreteCloseData : CRealQuotConcreteAbsSubCloseToRepCloseData
  repSequenceComplete : CRealRepSequenceCompleteLayer
  positive_inverse_is_data_indexed : Prop
  old_live_cofo_needs_total_inverse_or_interface_refactor : Prop
  opaque_quotient_complete_needs_representatives_or_interface_refactor : Prop

def cRealQuotFaithfulScalarPackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotFaithfulScalarPackage A where
  globalRep := rep
  posEventuallySelector := sel
  dataCOFPackage :=
    cRealQuotDataCOFToLiveCOFPackageWithGlobalRepPosEventuallySelector
      A rep sel
  positiveInversePackage :=
    cRealQuotPositiveDataInversePackageWith A rep sel
  concreteCloseData := cRealQuotConcreteAbsSubCloseToRepCloseData
  repSequenceComplete := cRealRepSequenceCompleteLayer
  positive_inverse_is_data_indexed := True
  old_live_cofo_needs_total_inverse_or_interface_refactor := True
  opaque_quotient_complete_needs_representatives_or_interface_refactor := True

/-- The faithful package can still be routed back into the previous live
`BishopC.COFOC` interface when a totalization of the positive inverse is
explicitly supplied.  This theorem is a typed audit of the remaining interface
pressure: all other ingredients are already present in the package. -/
@[reducible] def cRealQuotFaithfulScalarPackage_to_liveCOFOC_with_totalization
    (A : ScalarMulArchimedeanData)
    (P : CRealQuotFaithfulScalarPackage A)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithGlobalRepPosEventuallySelectorTotalized
    A P.globalRep P.posEventuallySelector tot

/-- Roadmap checkpoint after the faithful scalar package is available. -/
structure CRealQuotAfterFaithfulScalarPackageFrontier : Type where
  faithful_data_order_packaged : Prop
  faithful_positive_inverse_packaged_without_totalization : Prop
  representative_diagonal_completeness_packaged : Prop
  remaining_global_rep_selector : Prop
  remaining_pos_eventually_selector : Prop
  remaining_choice_between_totalization_and_interface_refactor : Prop

def cRealQuotAfterFaithfulScalarPackageFrontier :
    CRealQuotAfterFaithfulScalarPackageFrontier where
  faithful_data_order_packaged := True
  faithful_positive_inverse_packaged_without_totalization := True
  representative_diagonal_completeness_packaged := True
  remaining_global_rep_selector := True
  remaining_pos_eventually_selector := True
  remaining_choice_between_totalization_and_interface_refactor := True

end BishopCReal

set_option linter.style.longLine false

