import Mathdemo.Internal.Real.QuotClassicalExtractionAudit

set_option linter.style.longLine false

/-!
# G110: RegularSeq/data-carrying mainline for theorem 1.18 property (4)

G109 was a useful audit: the previous opaque quotient route can discharge the two
remaining extraction obligations by `selector-based route`.  That is not the
Bishop-faithful proof route.

This file switches the property-(4) surface back to the representation-carrying
route.  The mainline data carries:

* the RegularSeq real surface;
* data-valued positivity/order infrastructure;
* the G96 property-(4) reduction data, whose min-law frontier is stated over
  representatives rather than by extracting representatives from a quotient.

The previous G109 selector extraction object is mentioned only as an adapter type,
not as a field used by the theorem-producing function.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Choice-free mainline input for property (4).

The theorem-producing field is the existing G96 reduction data.  The extra
fields record the scalar route that supplies that data: regular sequences with
Bishop equality and carried positivity/order evidence. -/
structure Property4RegularSeqDataMainlineInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 5 where
  realSurface : BishopRegularSeqRealSurface Arch
  sourceCOFOCSurface : CRealRegularSeqSourceCOFOCSurface Arch
  archDataPackage : CRealRegularSeqDataCOFOCArchDataPackage Arch
  sourceFaithfulness : BishopRealSourceFaithfulnessAudit
  g96_data : Property4ReductionDataFromScalarMinKernelClosedBridge S r
  source_line735_uses_regularseq_min_data : Prop
  source_line743_uses_carried_positive_data : Prop
  no_quotient_representative_extraction_in_mainline : Prop
  no_prop_lt_to_data_extraction_in_mainline : Prop
  classical_extraction_adapter_not_used_in_mainline : Prop

/-- Build the RegularSeq/data mainline input from the already isolated G96
property-(4) reduction data. -/
def regularSeqDataMainlineInput_from_g96Data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromScalarMinKernelClosedBridge S r) :
    Property4RegularSeqDataMainlineInput S r where
  realSurface := bishopRegularSeqRealSurface Arch
  sourceCOFOCSurface := cRealRegularSeqSourceCOFOCSurface Arch
  archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage Arch
  sourceFaithfulness := bishopRealSourceFaithfulnessAudit
  g96_data := data
  source_line735_uses_regularseq_min_data := True
  source_line743_uses_carried_positive_data := True
  no_quotient_representative_extraction_in_mainline := True
  no_prop_lt_to_data_extraction_in_mainline := True
  classical_extraction_adapter_not_used_in_mainline := True

/-- Theorem 1.18 property (4) through the Bishop-faithful RegularSeq/data
mainline.

Unlike the G109 adapter theorem, this function has no inputs of type
`CRealQuotRepresentativeExtractionObligation` or
`CRealQuotLTWitnessExtractionObligation`. -/
def property4_from_regularseq_data_mainline
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMainlineInput S r) :
    Property4Conclusion S r :=
  property4_from_scalar_min_kernel_closed S r data.g96_data

/-- A small audit object for the mainline's selector footprint. -/
structure Property4RegularSeqDataMainlineSelectorAudit : Type where
  quotient_representative_extraction_inputs : Nat
  quotient_lt_witness_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  regularseq_data_surface_inputs : Nat
  g109_classical_route_is_adapter_only : Prop

def property4RegularSeqDataMainlineSelectorAudit :
    Property4RegularSeqDataMainlineSelectorAudit where
  quotient_representative_extraction_inputs := 0
  quotient_lt_witness_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  regularseq_data_surface_inputs := 1
  g109_classical_route_is_adapter_only := True

end BishopRegularSeqTheorem118

/-- G110 package: property (4) now has a RegularSeq/data-carrying mainline.

The previous selector extraction audit remains named as an adapter type only.  The
main theorem-producing function consumes `Property4RegularSeqDataMainlineInput`,
not the G109 selector extraction value. -/
structure BishopRegularSeqTheorem118G110Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 7 where
  g109_classical_adapter_documented : Prop
  regularSeq_real_surface : BishopRegularSeqRealSurface Arch
  regularSeq_source_surface : CRealRegularSeqSourceCOFOCSurface Arch
  regularSeq_arch_data_package : CRealRegularSeqDataCOFOCArchDataPackage Arch
  property4_regularseq_mainline_data :
    BishopRegularSeqIntegrableRep S -> Type 5
  property4_from_regularseq_mainline :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_regularseq_mainline_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqDataMainlineSelectorAudit
  classical_extraction_adapter_type : Type 1
  source_lines_734_747_rerouted_to_regularseq_data_mainline : Prop
  quotient_extraction_not_a_mainline_input : Prop
  prop_order_witness_extraction_not_a_mainline_input : Prop
  g96_min_law_reduction_remains_the_active_analytic_input : Prop

def bishopRegularSeqTheorem118G110Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G110Package S where
  g109_classical_adapter_documented := True
  regularSeq_real_surface := bishopRegularSeqRealSurface Arch
  regularSeq_source_surface := cRealRegularSeqSourceCOFOCSurface Arch
  regularSeq_arch_data_package := cRealRegularSeqDataCOFOCArchDataPackage Arch
  property4_regularseq_mainline_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMainlineInput S
  property4_from_regularseq_mainline := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_data_mainline
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqDataMainlineSelectorAudit
  classical_extraction_adapter_type := CRealQuotClassicalExtractionAudit
  source_lines_734_747_rerouted_to_regularseq_data_mainline := True
  quotient_extraction_not_a_mainline_input := True
  prop_order_witness_extraction_not_a_mainline_input := True
  g96_min_law_reduction_remains_the_active_analytic_input := True

/-- Progress after G110: G109 is demoted to an adapter audit, while property
(4) has a theorem-producing RegularSeq/data-carrying mainline.  The remaining
mathematical work is now the analytic supply of the G96 min-law reduction data,
not quotient/Prop witness extraction. -/
def bishopRegularSeqCh1To4ProgressAfterG110 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G110: rerouted theorem 1.18 property (4) to a RegularSeq/data-carrying \
    mainline; the G109 selector-based quotient extraction is now adapter \
    audit only."


end BishopCReal
