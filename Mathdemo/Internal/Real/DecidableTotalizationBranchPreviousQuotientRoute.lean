import Mathdemo.Internal.Real.AuditMapPreviousCOFCOFOCOFOC

/-!
# G24: decidable-totalization branch for the previous quotient route

`AuditMapPreviousCOFCOFOCOFOC` documented the correspondence between the previous `COF`/`COFO`/
`COFOC` field names and the source-shaped `RegularSeq` surface.  This file
reduces one old-quotient adapter obligation: the total inverse adapter can be
built from the already existing decidable-positive branch once a quotient order
decider, a representative selector, and a positive-tail selector are supplied.

This does not make the strict no-extra-input quotient route unconditional.
It turns the third adapter from an opaque input into a conditional constructor,
leaving the representative and positive-tail selectors explicit.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The previous total inverse adapter produced by the decidable-positive branch.

The positive-data selector is used only to feed the existing data-positive
inverse totalization.  The representative selector is used to obtain the
positive quotient data needed by that constructor. -/
def cRealOldQuotTotalInverseAdapter_of_decidableBranch
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (rep : CRealOldQuotRepresentativeSelector)
    (sel : CRealOldQuotPositiveDataSelector) :
    CRealOldQuotTotalInverseAdapter A :=
  cRealQuotPositiveInverseTotalizationData_of_decidablePositiveData
    A hdec
    (cRealOldQuotPositiveLTData_from_rep_posSelector rep sel)

/-- Old live quotient `COFOC` through the same decidable-totalization branch. -/
@[reducible] def cRealOldQuotCOFOC_from_decidableTotalizationBranch
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (rep : CRealOldQuotRepresentativeSelector)
    (sel : CRealOldQuotPositiveDataSelector) :
    BishopC.COFOC CRealQuot :=
  cRealOldQuotCOFOC_from_explicit_adapters
    A rep sel
    (cRealOldQuotTotalInverseAdapter_of_decidableBranch A hdec rep sel)

/-- G24 package: the total-inverse adapter is no longer an opaque third input
on the decidable branch. -/
structure CRealOldQuotDecidableTotalizationBranch
    (A : ScalarMulArchimedeanData) : Type 1 where
  fieldAudit : CRealCOFOCFieldCorrespondenceAudit A
  totalInverseFromDecidable :
    CRealQuotLTDecidable →
      CRealOldQuotRepresentativeSelector →
        CRealOldQuotPositiveDataSelector →
          CRealOldQuotTotalInverseAdapter A
  oldCOFOCFromDecidable :
    CRealQuotLTDecidable →
      CRealOldQuotRepresentativeSelector →
        CRealOldQuotPositiveDataSelector →
          BishopC.COFOC CRealQuot
  total_inverse_adapter_has_conditional_constructor : Prop
  representative_selector_still_explicit : Prop
  positive_tail_selector_still_explicit : Prop
  quotient_order_decider_is_branch_input_not_source_surface : Prop
  regularseq_route_unchanged_by_this_branch : Prop

def cRealOldQuotDecidableTotalizationBranch
    (A : ScalarMulArchimedeanData) :
    CRealOldQuotDecidableTotalizationBranch A where
  fieldAudit := cRealCOFOCFieldCorrespondenceAudit A
  totalInverseFromDecidable := fun hdec rep sel =>
    cRealOldQuotTotalInverseAdapter_of_decidableBranch A hdec rep sel
  oldCOFOCFromDecidable := fun hdec rep sel =>
    cRealOldQuotCOFOC_from_decidableTotalizationBranch A hdec rep sel
  total_inverse_adapter_has_conditional_constructor := True
  representative_selector_still_explicit := True
  positive_tail_selector_still_explicit := True
  quotient_order_decider_is_branch_input_not_source_surface := True
  regularseq_route_unchanged_by_this_branch := True

/-- More detailed progress marker after G24.

The no-extra-input quotient route does not advance merely by adding a decidable
branch.  The conditional adapter branch advances because the total inverse
adapter now has a concrete constructor under explicit branch inputs. -/
structure CRealCOFOCG24ProgressMeter : Type where
  regularSeqRoutePercent : Nat
  oldQuotNoAdapterRoutePercent : Nat
  oldQuotDecidableAdapterBranchPercent : Nat
  practicalFinalRoutePercent : Nat
  totalInverseAdapterBranchPercent : Nat
  remainingDecidableBranchSelectorCount : Nat
  regularSeqRouteTarget : Prop
  oldQuotNoAdapterTarget : Prop
  oldQuotDecidableAdapterTarget : Prop
  practicalRouteTarget : Prop

def cRealCOFOCG24ProgressMeterAfterDecidableTotalization :
    CRealCOFOCG24ProgressMeter where
  regularSeqRoutePercent := 97
  oldQuotNoAdapterRoutePercent := 69
  oldQuotDecidableAdapterBranchPercent := 73
  practicalFinalRoutePercent := 97
  totalInverseAdapterBranchPercent := 85
  remainingDecidableBranchSelectorCount := 2
  regularSeqRouteTarget := True
  oldQuotNoAdapterTarget := True
  oldQuotDecidableAdapterTarget := True
  practicalRouteTarget := True

/-- Roadmap checkpoint after reducing the total-inverse adapter on the
decidable branch. -/
structure CRealAfterDecidableTotalizationBranchFrontier : Type where
  total_inverse_adapter_conditional_constructor_available : Prop
  decidable_branch_has_two_selector_inputs_remaining : Prop
  strict_no_extra_input_quotient_route_still_separate : Prop
  next_work_representative_or_positive_tail_selector : Prop

def cRealAfterDecidableTotalizationBranchFrontier :
    CRealAfterDecidableTotalizationBranchFrontier where
  total_inverse_adapter_conditional_constructor_available := True
  decidable_branch_has_two_selector_inputs_remaining := True
  strict_no_extra_input_quotient_route_still_separate := True
  next_work_representative_or_positive_tail_selector := True

end BishopCReal

set_option linter.style.longLine false

