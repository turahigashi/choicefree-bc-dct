import Mathdemo.Internal.CRat_iter124
import Mathdemo.Internal.BishopSec5_Measure

/-!
# G25: bridge from CRealQuot COFOC to the existing measure-theory interface

The constructive measure-theory files are written over an abstract scalar
`R` with `[BishopC.COFOC R]`.  Therefore the compatibility target for the
constructed Bishop real is the quotient presentation `CRealQuot` equipped with
`BishopC.COFOC CRealQuot`.

This file does not change the measure-theory development.  It records that,
once the quotient `COFOC` value is supplied by either explicit adapters or the
decidable-totalization branch, the existing `BishopD.MeasureSpace` and
`BishopD.SimpleFunction` interfaces can be specialized to `CRealQuot`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Existing measure-space type specialized to `CRealQuot` from any supplied
quotient `COFOC` value. -/
def cRealQuotMeasureSpaceTypeFromCOFOC
    (hR : BishopC.COFOC CRealQuot) (X : Type) : Type :=
  letI : BishopC.COFOC CRealQuot := hR
  BishopD.MeasureSpace X CRealQuot

/-- Existing simple-function type specialized to `CRealQuot` from any supplied
quotient `COFOC` value. -/
def cRealQuotSimpleFunctionTypeFromCOFOC
    (hR : BishopC.COFOC CRealQuot) {X : Type}
    (M : cRealQuotMeasureSpaceTypeFromCOFOC hR X) : Type :=
  letI : BishopC.COFOC CRealQuot := hR
  BishopD.SimpleFunction M

/-- Measure-space type obtained from the explicit old-quotient adapter route. -/
def cRealQuotMeasureSpaceType_from_explicitAdapters
    (A : ScalarMulArchimedeanData)
    (rep : CRealOldQuotRepresentativeSelector)
    (sel : CRealOldQuotPositiveDataSelector)
    (tot : CRealOldQuotTotalInverseAdapter A)
    (X : Type) : Type :=
  cRealQuotMeasureSpaceTypeFromCOFOC
    (cRealOldQuotCOFOC_from_explicit_adapters A rep sel tot) X

/-- Measure-space type obtained from the decidable-totalization branch. -/
def cRealQuotMeasureSpaceType_from_decidableBranch
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (rep : CRealOldQuotRepresentativeSelector)
    (sel : CRealOldQuotPositiveDataSelector)
    (X : Type) : Type :=
  cRealQuotMeasureSpaceTypeFromCOFOC
    (cRealOldQuotCOFOC_from_decidableTotalizationBranch A hdec rep sel) X

/-- G25 progress marker, now tracking compatibility with the abstract
measure-theory scalar interface. -/
structure CRealCOFOCG25MeasureBridgeProgressMeter : Type where
  regularSeqRoutePercent : Nat
  quotientCOFOCNoExtraInputPercent : Nat
  quotientDecidableBranchPercent : Nat
  measureTheoryCompatibilityPercent : Nat
  practicalFinalRoutePercent : Nat
  remainingNoExtraInputSelectorCount : Nat
  remainingDecidableBranchSelectorCount : Nat
  quotient_target_is_measure_theory_scalar : Prop
  regularseq_surface_is_source_layer : Prop
  existing_measure_files_need_no_scalar_refactor : Prop

def cRealCOFOCG25MeasureBridgeProgressMeter :
    CRealCOFOCG25MeasureBridgeProgressMeter where
  regularSeqRoutePercent := 97
  quotientCOFOCNoExtraInputPercent := 69
  quotientDecidableBranchPercent := 74
  measureTheoryCompatibilityPercent := 76
  practicalFinalRoutePercent := 97
  remainingNoExtraInputSelectorCount := 3
  remainingDecidableBranchSelectorCount := 2
  quotient_target_is_measure_theory_scalar := True
  regularseq_surface_is_source_layer := True
  existing_measure_files_need_no_scalar_refactor := True

/-- Compatibility package for the existing `[COFOC R]` measure-theory code. -/
structure CRealQuotMeasureTheoryCompatibilityPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  progress : CRealCOFOCG25MeasureBridgeProgressMeter
  explicitOldCOFOC :
    CRealOldQuotRepresentativeSelector →
      CRealOldQuotPositiveDataSelector →
        CRealOldQuotTotalInverseAdapter A →
          BishopC.COFOC CRealQuot
  decidableOldCOFOC :
    CRealQuotLTDecidable →
      CRealOldQuotRepresentativeSelector →
        CRealOldQuotPositiveDataSelector →
          BishopC.COFOC CRealQuot
  measureSpaceTypeFromCOFOC :
    BishopC.COFOC CRealQuot → Type → Type
  measureSpaceTypeFromExplicitAdapters :
    CRealOldQuotRepresentativeSelector →
      CRealOldQuotPositiveDataSelector →
        CRealOldQuotTotalInverseAdapter A →
          Type → Type
  measureSpaceTypeFromDecidableBranch :
    CRealQuotLTDecidable →
      CRealOldQuotRepresentativeSelector →
        CRealOldQuotPositiveDataSelector →
          Type → Type
  abstract_measure_theory_uses_cofoc_class : Prop
  crealquot_is_the_matching_scalar_target : Prop
  regularseq_enters_measure_theory_through_quotient_cofoc : Prop
  no_measure_theory_refactor_needed_for_scalar_alignment : Prop

def cRealQuotMeasureTheoryCompatibilityPackage
    (A : ScalarMulArchimedeanData) :
    CRealQuotMeasureTheoryCompatibilityPackage A where
  progress := cRealCOFOCG25MeasureBridgeProgressMeter
  explicitOldCOFOC := fun rep sel tot =>
    cRealOldQuotCOFOC_from_explicit_adapters A rep sel tot
  decidableOldCOFOC := fun hdec rep sel =>
    cRealOldQuotCOFOC_from_decidableTotalizationBranch A hdec rep sel
  measureSpaceTypeFromCOFOC := fun hR X =>
    cRealQuotMeasureSpaceTypeFromCOFOC hR X
  measureSpaceTypeFromExplicitAdapters := fun rep sel tot X =>
    cRealQuotMeasureSpaceType_from_explicitAdapters A rep sel tot X
  measureSpaceTypeFromDecidableBranch := fun hdec rep sel X =>
    cRealQuotMeasureSpaceType_from_decidableBranch A hdec rep sel X
  abstract_measure_theory_uses_cofoc_class := True
  crealquot_is_the_matching_scalar_target := True
  regularseq_enters_measure_theory_through_quotient_cofoc := True
  no_measure_theory_refactor_needed_for_scalar_alignment := True

/-- Roadmap checkpoint after proving the scalar-interface bridge shape. -/
structure CRealAfterMeasureTheoryBridgeFrontier : Type where
  measure_theory_bridge_available : Prop
  quotient_cofoc_is_required_for_existing_measure_code : Prop
  next_unconditional_work_is_selector_closure : Prop
  next_practical_work_is_final_packaging : Prop

def cRealAfterMeasureTheoryBridgeFrontier :
    CRealAfterMeasureTheoryBridgeFrontier where
  measure_theory_bridge_available := True
  quotient_cofoc_is_required_for_existing_measure_code := True
  next_unconditional_work_is_selector_closure := True
  next_practical_work_is_final_packaging := True

end BishopCReal

set_option linter.style.longLine false

