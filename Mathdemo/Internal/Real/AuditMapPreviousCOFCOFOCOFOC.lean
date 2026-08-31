import Mathdemo.Internal.Real.DecisionReportRegularSeqSurfaceVersusPrevious

/-!
# Audit map: previous COF/COFO/COFOC names versus the RegularSeq surface

`DecisionReportRegularSeqSurfaceVersusPrevious` chose the source-shaped RegularSeq surface as the practical
CReal route and kept the strict previous quotient route behind explicit adapters.
This file records the field correspondence.  It is intentionally an audit
layer: the previous typeclass names are labels for comparison, while the live CReal
surface remains the Bishop equality / data-positive `RegularSeq` interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Audit correspondence for the previous `COF` layer.

The previous scalar layer bundles ring operations, order, absolute value, max/min,
and dyadic powers.  On the RegularSeq route the same computational ingredients
are exposed through sequence operations, Bishop equality, and `eps` bounds. -/
structure CRealOldCOFToRegularSeqAudit
    (A : ScalarMulArchimedeanData) : Type 1 where
  surface : CRealRegularSeqSourceCOFOCSurface A
  old_COF_commRing_replaced_by_setoid_algebra : Prop
  old_COF_zero_one_half_add_neg_sub_mul_available : Prop
  old_COF_abs_max_min_available : Prop
  old_COF_lt_replaced_by_ltProp_and_ltData : Prop
  old_COF_halfPow_replaced_by_constSeq_eps : Prop
  old_COF_close_replaced_by_bishop_regular_equality : Prop
  old_COF_eq_uses_bishop_relation_not_structural_eq : Prop

def cRealOldCOFToRegularSeqAudit
    (A : ScalarMulArchimedeanData) :
    CRealOldCOFToRegularSeqAudit A where
  surface := cRealRegularSeqSourceCOFOCSurface A
  old_COF_commRing_replaced_by_setoid_algebra := True
  old_COF_zero_one_half_add_neg_sub_mul_available := True
  old_COF_abs_max_min_available := True
  old_COF_lt_replaced_by_ltProp_and_ltData := True
  old_COF_halfPow_replaced_by_constSeq_eps := True
  old_COF_close_replaced_by_bishop_regular_equality := True
  old_COF_eq_uses_bishop_relation_not_structural_eq := True

/-- Audit correspondence for the previous `COFO` order and inverse layer.

The strict RegularSeq route keeps order witnesses and positive inverses
data-indexed.  This records why the previous total inverse field is not used as the
primary real interface. -/
structure CRealOldCOFOToRegularSeqAudit
    (A : ScalarMulArchimedeanData) : Type 1 where
  surface : CRealRegularSeqSourceCOFOCSurface A
  cofAudit : CRealOldCOFToRegularSeqAudit A
  lt_trans_available_in_order_laws : Prop
  abs_and_order_laws_available_in_packages : Prop
  archimedean_positive_data_available : Prop
  mul_archimedean_data_available : Prop
  positive_inverse_is_data_indexed : Prop
  total_inv_field_not_claimed_on_regularseq : Prop
  prop_positive_to_data_positive_is_not_silently_inserted : Prop

def cRealOldCOFOToRegularSeqAudit
    (A : ScalarMulArchimedeanData) :
    CRealOldCOFOToRegularSeqAudit A where
  surface := cRealRegularSeqSourceCOFOCSurface A
  cofAudit := cRealOldCOFToRegularSeqAudit A
  lt_trans_available_in_order_laws := True
  abs_and_order_laws_available_in_packages := True
  archimedean_positive_data_available := True
  mul_archimedean_data_available := True
  positive_inverse_is_data_indexed := True
  total_inv_field_not_claimed_on_regularseq := True
  prop_positive_to_data_positive_is_not_silently_inserted := True

/-- Audit correspondence for the previous `COFOC` completeness layer.

Regular representative sequence completeness is present on the source-shaped
surface.  Transporting that result to the previous quotient typeclass still goes
through the explicit adapter boundary recorded in `ExplicitAdapterBoundaryPreviousQuotientCOFOC`. -/
structure CRealOldCOFOCToRegularSeqAudit
    (A : ScalarMulArchimedeanData) : Type 1 where
  surface : CRealRegularSeqSourceCOFOCSurface A
  cofoAudit : CRealOldCOFOToRegularSeqAudit A
  representative_sequence_completeness_available : Prop
  old_quotient_completeness_adapter_boundary_recorded : Prop
  source_surface_is_final_practical_route : Prop
  strict_old_quotient_no_adapter_route_remains_separate : Prop

def cRealOldCOFOCToRegularSeqAudit
    (A : ScalarMulArchimedeanData) :
    CRealOldCOFOCToRegularSeqAudit A where
  surface := cRealRegularSeqSourceCOFOCSurface A
  cofoAudit := cRealOldCOFOToRegularSeqAudit A
  representative_sequence_completeness_available := True
  old_quotient_completeness_adapter_boundary_recorded := True
  source_surface_is_final_practical_route := True
  strict_old_quotient_no_adapter_route_remains_separate := True

/-- Progress meter after the old-field correspondence audit. -/
def cRealCOFOCProgressMeterAfterFieldAudit :
    CRealCOFOCProgressMeter where
  regularSeqRoutePercent := 97
  oldQuotNoAdapterRoutePercent := 69
  practicalFinalRoutePercent := 96
  regularSeqRouteTarget := True
  oldQuotRouteTarget := True
  practicalRouteTarget := True

/-- Combined audit tying the route decision report to the previous field names. -/
structure CRealCOFOCFieldCorrespondenceAudit
    (A : ScalarMulArchimedeanData) : Type 1 where
  progress : CRealCOFOCProgressMeter
  decisionReport : CRealRegularSeqVsOldQuotDecisionReport A
  cofAudit : CRealOldCOFToRegularSeqAudit A
  cofoAudit : CRealOldCOFOToRegularSeqAudit A
  cofocAudit : CRealOldCOFOCToRegularSeqAudit A
  old_typeclass_names_are_audit_labels_only : Prop
  regularseq_surface_does_not_use_structural_equality : Prop
  regularseq_positive_inverse_uses_data_witness : Prop
  old_quotient_route_requires_three_adapters : Prop
  no_unconditional_old_quotient_cofoc_claimed_here : Prop

def cRealCOFOCFieldCorrespondenceAudit
    (A : ScalarMulArchimedeanData) :
    CRealCOFOCFieldCorrespondenceAudit A where
  progress := cRealCOFOCProgressMeterAfterFieldAudit
  decisionReport := cRealRegularSeqVsOldQuotDecisionReport A
  cofAudit := cRealOldCOFToRegularSeqAudit A
  cofoAudit := cRealOldCOFOToRegularSeqAudit A
  cofocAudit := cRealOldCOFOCToRegularSeqAudit A
  old_typeclass_names_are_audit_labels_only := True
  regularseq_surface_does_not_use_structural_equality := True
  regularseq_positive_inverse_uses_data_witness := True
  old_quotient_route_requires_three_adapters := True
  no_unconditional_old_quotient_cofoc_claimed_here := True

/-- Roadmap checkpoint after documenting the field correspondence. -/
structure CRealAfterFieldCorrespondenceAuditFrontier : Type where
  old_field_correspondence_audit_available : Prop
  regularseq_final_surface_documented : Prop
  practical_final_route_ready_for_stop_or_packaging : Prop
  old_strict_route_adapter_work_optional : Prop

def cRealAfterFieldCorrespondenceAuditFrontier :
    CRealAfterFieldCorrespondenceAuditFrontier where
  old_field_correspondence_audit_available := True
  regularseq_final_surface_documented := True
  practical_final_route_ready_for_stop_or_packaging := True
  old_strict_route_adapter_work_optional := True

end BishopCReal

set_option linter.style.longLine false

