import Mathdemo.Internal.CRat_iter119

/-!
# Explicit adapter boundary for the previous quotient COFOC route

The RegularSeq route now carries the source-shaped data directly.  This file
records the remaining previous `BishopC.COFOC CRealQuot` route as an adapter
boundary rather than a hidden target:

* quotient representative extraction;
* conversion from Prop-valued quotient order to data-valued order;
* totalization of the positive-data inverse into the previous total inverse field.

No new construction is claimed here.  The previous live `COFOC` record is recovered
only when those adapters are supplied explicitly.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative selector required by the previous opaque quotient route. -/
abbrev CRealOldQuotRepresentativeSelector : Type :=
  CRealQuotGlobalRepProblem

/-- Positive-tail data selector required to convert quotient Prop order back
to data. -/
abbrev CRealOldQuotPositiveDataSelector : Type :=
  CRealPosEventuallySelector

/-- Prop-valued quotient strict order to data-valued strict order. -/
abbrev CRealOldQuotPropLTToDataBoundary : Type :=
  CRealQuotPropLTToDataLTObligation

/-- Total inverse adapter required by the previous `COFO.inv` field. -/
abbrev CRealOldQuotTotalInverseAdapter
    (A : ScalarMulArchimedeanData) : Type :=
  CRealQuotPositiveInverseTotalizationData A

/-- The global representative selector plus positive-tail selector produce the
Prop-to-data strict-order bridge used by the older quotient route. -/
def cRealOldQuotPropLTToData_from_rep_posSelector
    (rep : CRealOldQuotRepresentativeSelector)
    (sel : CRealOldQuotPositiveDataSelector) :
    CRealOldQuotPropLTToDataBoundary :=
  cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel

/-- Same boundary specialized to positive quotient inputs. -/
def cRealOldQuotPositiveLTData_from_rep_posSelector
    (rep : CRealOldQuotRepresentativeSelector)
    (sel : CRealOldQuotPositiveDataSelector) :
    CRealQuotPositiveLTDataOf :=
  cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector rep sel

/-- Old live quotient `COFOC` recovered only after all adapters are supplied. -/
@[reducible] def cRealOldQuotCOFOC_from_explicit_adapters
    (A : ScalarMulArchimedeanData)
    (rep : CRealOldQuotRepresentativeSelector)
    (sel : CRealOldQuotPositiveDataSelector)
    (tot : CRealOldQuotTotalInverseAdapter A) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithGlobalRepPosEventuallySelectorTotalized A rep sel tot

/-- Boundary report comparing the source-faithful RegularSeq package with the
previous quotient adapter route. -/
structure CRealOldQuotCOFOCAdapterBoundary
    (A : ScalarMulArchimedeanData) : Type 1 where
  regularSeqDataPackage : CRealRegularSeqDataCOFOCArchDataPackage A
  representativeSelector : Type
  positiveDataSelector : Type
  propLTToDataBoundary : Type
  totalInverseAdapter : Type
  propLTToDataFrom :
    representativeSelector → positiveDataSelector → propLTToDataBoundary
  oldCOFOCFromAdapters :
    representativeSelector → positiveDataSelector → totalInverseAdapter →
      BishopC.COFOC CRealQuot
  quotient_route_is_adapter_not_source_carrier : Prop
  regularseq_route_carries_positive_data_directly : Prop
  no_unconditional_old_quotient_cofoc_claimed : Prop

def cRealOldQuotCOFOCAdapterBoundary
    (A : ScalarMulArchimedeanData) :
    CRealOldQuotCOFOCAdapterBoundary A where
  regularSeqDataPackage := cRealRegularSeqDataCOFOCArchDataPackage A
  representativeSelector := CRealOldQuotRepresentativeSelector
  positiveDataSelector := CRealOldQuotPositiveDataSelector
  propLTToDataBoundary := CRealOldQuotPropLTToDataBoundary
  totalInverseAdapter := CRealOldQuotTotalInverseAdapter A
  propLTToDataFrom := fun rep sel =>
    cRealOldQuotPropLTToData_from_rep_posSelector rep sel
  oldCOFOCFromAdapters := fun rep sel tot =>
    cRealOldQuotCOFOC_from_explicit_adapters A rep sel tot
  quotient_route_is_adapter_not_source_carrier := True
  regularseq_route_carries_positive_data_directly := True
  no_unconditional_old_quotient_cofoc_claimed := True

/-- Roadmap checkpoint after isolating the previous quotient adapter boundary. -/
structure CRealAfterOldQuotAdapterBoundaryFrontier : Type where
  regularseq_arch_data_package_available : Prop
  old_quotient_adapter_boundary_explicit : Prop
  representative_selector_boundary_explicit : Prop
  prop_to_data_selector_boundary_explicit : Prop
  total_inverse_adapter_boundary_explicit : Prop
  next_regularseq_final_surface_or_adapter_choice : Prop

def cRealAfterOldQuotAdapterBoundaryFrontier :
    CRealAfterOldQuotAdapterBoundaryFrontier where
  regularseq_arch_data_package_available := True
  old_quotient_adapter_boundary_explicit := True
  representative_selector_boundary_explicit := True
  prop_to_data_selector_boundary_explicit := True
  total_inverse_adapter_boundary_explicit := True
  next_regularseq_final_surface_or_adapter_choice := True

end BishopCReal

set_option linter.style.longLine false

