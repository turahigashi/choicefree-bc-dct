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

/-- The data-indexed reciprocal of a positive representative is positive in
the same representative strict order used by the RegularSeq package. -/
def regularSeqPositiveInvData_posData
    (A : ScalarMulArchimedeanData)
    {x : RegularSeq} (hx : PosEventuallyData x) :
    regularSeqLtData zeroSeq (positiveTailInvSeqWithBound A x hx) :=
  positiveTailInvSeqWithBound_sub_zero_posData A x hx

/-- Prop-valued version of reciprocal positivity for the RegularSeq order. -/
theorem regularSeqPositiveInvData_posProp
    (A : ScalarMulArchimedeanData)
    {x : RegularSeq} (hx : PosEventuallyData x) :
    regularSeqLtProp zeroSeq (positiveTailInvSeqWithBound A x hx) :=
  (regularSeqPositiveInvData_posData A hx).toProp

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

/-- Prop-valued multiplicative Archimedean bound directly on representatives.

This is the RegularSeq form of the standard-bound argument already used by the
quotient layer. -/
theorem regularSeqMulArchimedean_const_exists
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    ∃ m : Nat,
      ¬ regularSeqLtProp oneSeq
        (mulSeqConcreteWith A (absSeq x) (constSeq (eps m))) := by
  refine ⟨standardBoundWith A x, ?_⟩
  change ¬ PosEventually
    (subSeq
      (mulSeqConcreteWith A (absSeq x)
        (constSeq (eps (standardBoundWith A x))))
      oneSeq)
  exact not_posEventually_abs_mul_standard_sub_one_with A x

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

def cRealRegularSeqPositiveInverseOrderCompatibilityLayer
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqPositiveInverseOrderCompatibilityLayer A where
  orderPackage := cRealRegularSeqDataCOFOCOrderPackage A
  inv_posData := fun hx => regularSeqPositiveInvData_posData A hx
  inv_posProp := fun hx => regularSeqPositiveInvData_posProp A hx
  mul_inv_eventually_one := fun hx =>
    regularSeqPositiveInvData_mul_cancel A hx
  inv_respects := fun hx hy hxy =>
    regularSeqPositiveInvData_respects A hx hy hxy

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

def cRealRegularSeqArchimedeanPropLayer
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqArchimedeanPropLayer A where
  positiveInverseOrder :=
    cRealRegularSeqPositiveInverseOrderCompatibilityLayer A
  mul_archimedean_const_prop :=
    regularSeqMulArchimedean_const_exists A
  data_search_requires_order_selector := True
  quotient_decidable_route_already_supplies_selector := True

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

def cRealRegularSeqDataCOFOCArchInvPackage
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqDataCOFOCArchInvPackage A where
  orderPackage := cRealRegularSeqDataCOFOCOrderPackage A
  positiveInverseOrder :=
    cRealRegularSeqPositiveInverseOrderCompatibilityLayer A
  archimedeanProp := cRealRegularSeqArchimedeanPropLayer A
  positive_inverse_is_data_indexed := True
  archimedean_is_prop_level_without_selector := True
  old_quotient_total_inverse_adapter_remains_separate := True

/-- Roadmap checkpoint after the RegularSeq positive-inverse/Archimedean
layer. -/
structure CRealAfterRegularSeqArchInvLayerFrontier : Type where
  positive_inverse_order_compat_available : Prop
  prop_archimedean_available : Prop
  data_archimedean_search_remains_frontier : Prop
  old_quotient_total_inverse_adapter_remains_separate : Prop
  next_step_selector_or_adapter_boundary : Prop

def cRealAfterRegularSeqArchInvLayerFrontier :
    CRealAfterRegularSeqArchInvLayerFrontier where
  positive_inverse_order_compat_available := True
  prop_archimedean_available := True
  data_archimedean_search_remains_frontier := True
  old_quotient_total_inverse_adapter_remains_separate := True
  next_step_selector_or_adapter_boundary := True

end BishopCReal

set_option linter.style.longLine false

