import Mathdemo.Internal.Real.FinalSourceShapedRegularSeqCOFOCSurface

/-!
# Decision report: RegularSeq surface versus previous quotient adapter

`FinalSourceShapedRegularSeqCOFOCSurface` exposed the source-shaped RegularSeq surface.  This file adds a
single decision report comparing it with the previous quotient adapter route from
`ExplicitAdapterBoundaryPreviousQuotientCOFOC`, together with a compact progress meter for the two routes.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Coarse project progress meter for the CReal/COFOC formalization fork.

The values are intentionally project-management markers, not mathematical
content.  They keep the route split visible in Lean:

* the RegularSeq route tracks the source-shaped data surface;
* the previous quotient route tracks the strict no-extra-adapter `COFOC` target;
* the practical route tracks the RegularSeq surface as the accepted final
  CReal presentation. -/
structure CRealCOFOCProgressMeter : Type where
  regularSeqRoutePercent : Nat
  oldQuotNoAdapterRoutePercent : Nat
  practicalFinalRoutePercent : Nat
  regularSeqRouteTarget : Prop
  oldQuotRouteTarget : Prop
  practicalRouteTarget : Prop

def cRealCOFOCProgressMeterAfterRegularSeqSurface :
    CRealCOFOCProgressMeter where
  regularSeqRoutePercent := 96
  oldQuotNoAdapterRoutePercent := 69
  practicalFinalRoutePercent := 95
  regularSeqRouteTarget := True
  oldQuotRouteTarget := True
  practicalRouteTarget := True

/-- Route comparison after the RegularSeq source surface is available. -/
structure CRealRegularSeqVsOldQuotDecisionReport
    (A : ScalarMulArchimedeanData) : Type 1 where
  progress : CRealCOFOCProgressMeter
  regularSeqSurface : CRealRegularSeqSourceCOFOCSurface A
  oldAdapterBoundary : CRealOldQuotCOFOCAdapterBoundary A
  oldCOFOCFromAdapters :
    CRealOldQuotRepresentativeSelector →
      CRealOldQuotPositiveDataSelector →
        CRealOldQuotTotalInverseAdapter A →
          BishopC.COFOC CRealQuot
  regularSeq_primary_carrier_is_data_surface : Prop
  regularSeq_uses_bishop_equality_and_eventual_setoid : Prop
  regularSeq_inverse_is_positive_data_indexed : Prop
  old_quotient_requires_representative_selector : Prop
  old_quotient_requires_prop_to_data_selector : Prop
  old_quotient_requires_total_inverse_adapter : Prop
  no_unconditional_old_quotient_cofoc_claimed : Prop
  final_practical_route_is_regularseq_surface : Prop

def cRealRegularSeqVsOldQuotDecisionReport
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqVsOldQuotDecisionReport A where
  progress := cRealCOFOCProgressMeterAfterRegularSeqSurface
  regularSeqSurface := cRealRegularSeqSourceCOFOCSurface A
  oldAdapterBoundary := cRealOldQuotCOFOCAdapterBoundary A
  oldCOFOCFromAdapters := fun rep sel tot =>
    cRealOldQuotCOFOC_from_explicit_adapters A rep sel tot
  regularSeq_primary_carrier_is_data_surface := True
  regularSeq_uses_bishop_equality_and_eventual_setoid := True
  regularSeq_inverse_is_positive_data_indexed := True
  old_quotient_requires_representative_selector := True
  old_quotient_requires_prop_to_data_selector := True
  old_quotient_requires_total_inverse_adapter := True
  no_unconditional_old_quotient_cofoc_claimed := True
  final_practical_route_is_regularseq_surface := True

/-- Final checkpoint for this roadmap slice. -/
structure CRealAfterRouteDecisionReportFrontier : Type where
  regularseq_surface_available : Prop
  old_adapter_route_audited : Prop
  route_decision_report_available : Prop
  progress_meter_available : Prop
  next_optional_work_old_adapter_or_documentation : Prop

def cRealAfterRouteDecisionReportFrontier :
    CRealAfterRouteDecisionReportFrontier where
  regularseq_surface_available := True
  old_adapter_route_audited := True
  route_decision_report_available := True
  progress_meter_available := True
  next_optional_work_old_adapter_or_documentation := True

end BishopCReal

set_option linter.style.longLine false

