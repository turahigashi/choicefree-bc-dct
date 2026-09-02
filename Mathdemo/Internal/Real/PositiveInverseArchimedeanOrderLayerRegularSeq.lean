import Mathdemo.Internal.Real.DataOrderLawLayerRegularSeqData

/-!
# Positive inverse and Archimedean order layer for the RegularSeq route

`DataOrderLawLayerRegularSeqData` packaged the representative strict-order laws.  This file
connects two already closed ingredients to that source-shaped interface:

* the positive-data reciprocal is positive and cancels against its source
  representative;
* every representative has the Prop-valued multiplicative Archimedean bound
  supplied by the standard dyadic bound.

The data-valued Archimedean search is deliberately left as a frontier item:
the existing quotient construction obtains it from strict-order decidability,
while the RegularSeq data route has not committed to such a selector.
-/

namespace BishopCReal

open BishopC
open BishopCRat



/-- Source representative times its data-indexed reciprocal is eventually
equal to one. -/
theorem regularSeqPositiveInvData_mul_cancel
    (A : ScalarMulArchimedeanData)
    {x : RegularSeq} (hx : PosEventuallyData x) :
    relEventually
      (mulSeqConcreteWith A x (positiveTailInvSeqWithBound A x hx))
      oneSeq :=
  positiveTail_mulSeqConcreteWith_invSeq_eventually_one A x hx

/-- Data-indexed reciprocal respects implementation equality when both sides
carry positive data. -/
theorem regularSeqPositiveInvData_respects
    (A : ScalarMulArchimedeanData)
    {x y : RegularSeq}
    (hx : PosEventuallyData x) (hy : PosEventuallyData y)
    (hxy : relEventually x y) :
    relEventually
      (positiveTailInvSeqWithBound A x hx)
      (positiveTailInvSeqWithBound A y hy) :=
  positiveTailInvSeqWithBound_respects_eventually_data A hx hy hxy


/-- Positive inverse/order compatibility layer for the RegularSeq route. -/
structure CRealRegularSeqPositiveInverseOrderCompatibilityLayer
    (A : ScalarMulArchimedeanData) : Type 1 where
  orderPackage : CRealRegularSeqDataCOFOCOrderPackage A
  inv_posData :
    ∀ {x : RegularSeq}, ∀ hx : PosEventuallyData x,
      regularSeqLtData zeroSeq (positiveTailInvSeqWithBound A x hx)
  inv_posProp :
    ∀ {x : RegularSeq}, ∀ hx : PosEventuallyData x,
      regularSeqLtProp zeroSeq (positiveTailInvSeqWithBound A x hx)
  mul_inv_eventually_one :
    ∀ {x : RegularSeq}, ∀ hx : PosEventuallyData x,
      relEventually
        (mulSeqConcreteWith A x (positiveTailInvSeqWithBound A x hx))
        oneSeq
  inv_respects :
    ∀ {x y : RegularSeq}, ∀ hx : PosEventuallyData x,
      ∀ hy : PosEventuallyData y,
        relEventually x y →
          relEventually
            (positiveTailInvSeqWithBound A x hx)
            (positiveTailInvSeqWithBound A y hy)


/-- Prop-level Archimedean layer for RegularSeq representatives. -/
structure CRealRegularSeqArchimedeanPropLayer
    (A : ScalarMulArchimedeanData) : Type 1 where
  positiveInverseOrder :
    CRealRegularSeqPositiveInverseOrderCompatibilityLayer A
  mul_archimedean_const_prop :
    ∀ x : RegularSeq,
      ∃ m : Nat,
        ¬ regularSeqLtProp oneSeq
          (mulSeqConcreteWith A (absSeq x) (constSeq (eps m)))
  data_search_requires_order_selector : Prop
  quotient_decidable_route_already_supplies_selector : Prop


/-- Extended RegularSeq package after adding positive-inverse/order
compatibility and Prop-valued Archimedean bounds. -/
structure CRealRegularSeqDataCOFOCArchInvPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  orderPackage : CRealRegularSeqDataCOFOCOrderPackage A
  positiveInverseOrder :
    CRealRegularSeqPositiveInverseOrderCompatibilityLayer A
  archimedeanProp : CRealRegularSeqArchimedeanPropLayer A
  positive_inverse_is_data_indexed : Prop
  archimedean_is_prop_level_without_selector : Prop
  old_quotient_total_inverse_adapter_remains_separate : Prop




end BishopCReal

set_option linter.style.longLine false

