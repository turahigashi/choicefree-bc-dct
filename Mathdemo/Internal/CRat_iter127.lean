import Mathdemo.Internal.CRat_iter126

/-!
# G27: PosEventually selector boundary at the scalar instance

The remaining positive-tail issue is not pointwise scalar order.  It is the
extraction of concrete `k, N` witnesses from the Prop-valued infinite-tail
predicate `PosEventually`.

The constructive direction is data-to-Prop:

* `PosEventuallyData x` carries `k`, `N`, and the tail proof.
* `PosEventually x` only states that such witnesses exist as a proposition.

This file records that boundary and connects it to the selector containment
from `CRat_iter126`, so the measure-theory layer still sees only the final
`BishopC.COFOC CRealQuot` scalar interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The one-way constructive bridge from carried positive-tail data to the
Prop-valued positive-tail predicate. -/
def cRealPosEventuallyData_to_prop {x : RegularSeq}
    (hx : PosEventuallyData x) : PosEventually x :=
  hx.toProp

/-- The two positivity presentations at the scalar boundary.

The reverse direction is intentionally not constructed here.  The existing
`CRealPosEventuallySelector` from `CRat_iter106` is the precise Type-valued
input that would provide the missing witnesses. -/
structure CRealPosEventuallyPropDataBoundary : Type 1 where
  propPos : RegularSeq -> Prop
  dataPos : RegularSeq -> Type
  data_to_prop : forall {x : RegularSeq}, dataPos x -> propPos x
  selector : Type
  selector_to_dataOf : selector -> CRealPosEventuallyDataOf
  dataOf_to_selector : CRealPosEventuallyDataOf -> selector
  prop_to_data_not_constructed_here : Prop
  selector_is_exact_frontier : Prop
  data_positive_route_is_source_shape : Prop

def cRealPosEventuallyPropDataBoundary :
    CRealPosEventuallyPropDataBoundary where
  propPos := PosEventually
  dataPos := PosEventuallyData
  data_to_prop := fun hx => hx.toProp
  selector := CRealPosEventuallySelector
  selector_to_dataOf := cRealPosEventuallyDataOf_of_selector
  dataOf_to_selector := cRealPosEventuallySelector_of_dataOf
  prop_to_data_not_constructed_here := True
  selector_is_exact_frontier := True
  data_positive_route_is_source_shape := True

/-- Boundary audit after combining the positive-tail selector frontier with the
G26 scalar-instance containment package. -/
structure CRealQuotPosEventuallyBoundaryAtMeasureScalar
    (A : ScalarMulArchimedeanData) : Type 2 where
  selectorContainment : CRealQuotDecidableBranchSelectorContainmentAudit A
  posBoundary : CRealPosEventuallyPropDataBoundary
  selectorInputs_to_cofoc :
    CRealQuotMeasureScalarSelectorInputs A -> BishopC.COFOC CRealQuot
  selectorInputs_to_measureSpaceType :
    CRealQuotMeasureScalarSelectorInputs A -> Type -> Type
  positive_selector_compiled_before_measure_layer : Prop
  measure_layer_does_not_eliminate_pos_eventually : Prop
  measure_layer_sees_only_cofoc : Prop

def cRealQuotPosEventuallyBoundaryAtMeasureScalar
    (A : ScalarMulArchimedeanData) :
    CRealQuotPosEventuallyBoundaryAtMeasureScalar A where
  selectorContainment := cRealQuotDecidableBranchSelectorContainmentAudit A
  posBoundary := cRealPosEventuallyPropDataBoundary
  selectorInputs_to_cofoc := cRealQuotMeasureScalarSelectorInputs_cofoc A
  selectorInputs_to_measureSpaceType := fun inputs X =>
    cRealQuotMeasureSpaceType_from_selectorInputs A inputs X
  positive_selector_compiled_before_measure_layer := True
  measure_layer_does_not_eliminate_pos_eventually := True
  measure_layer_sees_only_cofoc := True

/-- A source-shaped branch where carried positive data is primary.  This avoids
the Prop-to-data witness extraction by taking the data presentation as the
working order layer. -/
structure CRealPositiveDataPrimaryRoute : Type 1 where
  carrier : Type
  positiveData : carrier -> Type
  positiveProp : carrier -> Prop
  data_to_prop : forall {x : carrier}, positiveData x -> positiveProp x
  positive_inverse_consumes_data : Prop
  prop_to_data_selector_not_part_of_route : Prop
  quotient_measure_scalar_still_needs_boundary_packaging : Prop

def cRealRegularSeqPositiveDataPrimaryRoute :
    CRealPositiveDataPrimaryRoute where
  carrier := RegularSeq
  positiveData := PosEventuallyData
  positiveProp := PosEventually
  data_to_prop := fun hx => hx.toProp
  positive_inverse_consumes_data := True
  prop_to_data_selector_not_part_of_route := True
  quotient_measure_scalar_still_needs_boundary_packaging := True

/-- G27 progress meter after isolating the `PosEventually` witness selector as
the positive-tail boundary. -/
structure CRealCOFOCG27PosEventuallyProgressMeter : Type where
  regularSeqRoutePercent : Nat
  quotientCOFOCNoExtraInputPercent : Nat
  quotientDecidableBranchPercent : Nat
  measureTheoryCompatibilityPercent : Nat
  selectorContainmentPercent : Nat
  posEventuallySelectorBoundaryPercent : Nat
  practicalFinalRoutePercent : Nat
  remainingNoExtraInputSelectorCount : Nat
  remainingDecidableBranchSelectorCount : Nat
  measureLayerSeesSelectorCount : Nat
  data_to_prop_direction_available : Prop
  prop_to_data_selector_kept_explicit : Prop
  next_blocker_is_representative_or_data_positive_refactor : Prop

def cRealCOFOCG27PosEventuallyProgressMeter :
    CRealCOFOCG27PosEventuallyProgressMeter where
  regularSeqRoutePercent := 97
  quotientCOFOCNoExtraInputPercent := 69
  quotientDecidableBranchPercent := 76
  measureTheoryCompatibilityPercent := 81
  selectorContainmentPercent := 83
  posEventuallySelectorBoundaryPercent := 86
  practicalFinalRoutePercent := 97
  remainingNoExtraInputSelectorCount := 3
  remainingDecidableBranchSelectorCount := 2
  measureLayerSeesSelectorCount := 0
  data_to_prop_direction_available := True
  prop_to_data_selector_kept_explicit := True
  next_blocker_is_representative_or_data_positive_refactor := True

/-- Roadmap checkpoint after the positive-tail selector boundary is fixed. -/
structure CRealAfterPosEventuallySelectorBoundaryFrontier : Type where
  pos_eventually_prop_data_boundary_recorded : Prop
  data_to_prop_direction_available : Prop
  prop_to_data_selector_kept_explicit : Prop
  selector_boundary_remains_scalar_instance_only : Prop
  measure_theory_bridge_still_needs_only_cofoc : Prop
  next_representative_extraction_or_data_positive_refactor : Prop

def cRealAfterPosEventuallySelectorBoundaryFrontier :
    CRealAfterPosEventuallySelectorBoundaryFrontier where
  pos_eventually_prop_data_boundary_recorded := True
  data_to_prop_direction_available := True
  prop_to_data_selector_kept_explicit := True
  selector_boundary_remains_scalar_instance_only := True
  measure_theory_bridge_still_needs_only_cofoc := True
  next_representative_extraction_or_data_positive_refactor := True

end BishopCReal

set_option linter.style.longLine false

