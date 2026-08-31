import Mathdemo.Internal.Real.PosEventuallySelectorExactlyPropDataPositivity

set_option linter.style.longLine false

/-!
# G107: no-inverse min laws from representative extraction plus lt-data

G106 restated the second selector as representative-level
`PosEventually -> PosEventuallyData` extraction.  The lower G101 min-law
theorems, however, need only the quotient-facing pair:

* representatives for quotient elements;
* conversion from Prop-valued `ltQuot` to data-valued `ltQuotData`.

This file connects property (4)'s no-inverse min-law bridge directly to that
general extraction pair.  The `PosEventually` route from G106 is retained as
one way to produce the `ltQuotData` extractor, not as a separate mathematical
ingredient of the min-law proof itself.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Generate the G97 quotient-transport laws from the exact quotient
extraction pair used by the G101 no-inverse min-law theorems. -/
def minSeqQuotientTransportCoreLaws_from_repLTDataNoInverse
    (Arch : ScalarMulArchimedeanData)
    (g96_laws : Property4ScalarMinKernelClosedCoreLaws Arch)
    (rep : CRealQuotRepresentativeExtractionObligation)
    (ltDataOf : CRealQuotPropLTToDataLTObligation) :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch where
  g96_core_laws := g96_laws
  quotient_min_monotone_left := by
    intro x y c hxy
    exact
      quotient_min_monotone_left_regularSeqLe_without_inverse_totalization
        Arch rep ltDataOf x y c hxy
  quotient_min_add_nonnegative_right_bound := by
    intro x d c hd
    exact
      quotient_min_add_nonnegative_right_bound_regularSeqLe_without_inverse_totalization
        Arch rep ltDataOf x d c hd
  source_minSeqWith_to_quotient_min_closed := True
  source_line735_min_frontier_now_quotient_order := True
  source_line743_shifted_min_frontier_now_quotient_order := True

/-- No-inverse min-law data stated at the quotient extraction boundary. -/
structure Property4NoInverseMinLawRepLTDataExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g96_bridge :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S
  representative_extraction :
    CRealQuotRepresentativeExtractionObligation
  prop_lt_to_data_lt :
    CRealQuotPropLTToDataLTObligation
  source_line735_and_line743_generated_from_rep_plus_lt_data : Prop
  source_positive_inverse_totalization_removed_from_rep_lt_data_route : Prop

/-- Generate the G102 no-inverse bridge directly from quotient representative
extraction plus Prop-to-data strict-order extraction. -/
def noInverseMinSeqQuotientTransportBridge_from_repLTDataExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawRepLTDataExactData S) :
    Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge S where
  no_inverse_minseq_transport_laws :=
    minSeqQuotientTransportCoreLaws_from_repLTDataNoInverse
      Arch
      data.g96_bridge.scalar_min_kernel_closed_core_laws
      data.representative_extraction
      data.prop_lt_to_data_lt
  g96_bridge := data.g96_bridge
  source_line735_min_transport_no_inverse_totalization :=
    data.source_line735_and_line743_generated_from_rep_plus_lt_data
  source_line743_shifted_min_transport_no_inverse_totalization :=
    data.source_line735_and_line743_generated_from_rep_plus_lt_data
  remaining_global_rep_selector_frontier := True
  remaining_pos_eventually_selector_frontier := False

/-- The G106 `PosEventuallyDataOf` interface supplies the general `ltQuotData`
extractor and hence the G107 rep+lt-data interface. -/
def repLTDataExactData_from_posDataOfExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawPosDataOfExactData S) :
    Property4NoInverseMinLawRepLTDataExactData S where
  g96_bridge := data.g96_bridge
  representative_extraction := data.global_rep_selector
  prop_lt_to_data_lt :=
    cRealQuotLTDataOf_of_globalRep_and_posEventuallyDataOf
      data.global_rep_selector
      data.pos_eventually_data_of
  source_line735_and_line743_generated_from_rep_plus_lt_data :=
    data.source_line735_and_line743_generated_from_global_rep_plus_pos_data
  source_positive_inverse_totalization_removed_from_rep_lt_data_route :=
    data.source_positive_inverse_totalization_removed_from_pos_data_route

/-- Property-(4) reduction data at the quotient extraction boundary. -/
structure Property4ReductionDataFromRepLTDataExactNoInverseMinLawBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g96_data :
    Property4ReductionDataFromScalarMinKernelClosedBridge S r
  representative_extraction :
    CRealQuotRepresentativeExtractionObligation
  prop_lt_to_data_lt :
    CRealQuotPropLTToDataLTObligation
  source_property4_min_laws_generated_from_rep_plus_lt_data : Prop
  source_no_positive_inverse_totalization_input_for_min_laws : Prop

/-- Convert the rep+lt-data reduction interface into the G102 no-inverse
reduction layer. -/
def noInverseTotalizationData_from_repLTDataExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromRepLTDataExactNoInverseMinLawBridge S r) :
    Property4ReductionDataFromNoInverseTotalizationBridge S r where
  g96_data := data.g96_data
  no_inverse_bridge :=
    noInverseMinSeqQuotientTransportBridge_from_repLTDataExact
      S
      { g96_bridge := data.g96_data.scalar_min_kernel_bridge
        representative_extraction := data.representative_extraction
        prop_lt_to_data_lt := data.prop_lt_to_data_lt
        source_line735_and_line743_generated_from_rep_plus_lt_data :=
          data.source_property4_min_laws_generated_from_rep_plus_lt_data
        source_positive_inverse_totalization_removed_from_rep_lt_data_route :=
          data.source_no_positive_inverse_totalization_input_for_min_laws }
  source_property4_reduction_uses_no_inverse_totalization_for_min_laws :=
    data.source_no_positive_inverse_totalization_input_for_min_laws

/-- Property (4) from the exact quotient extraction pair used by the no-inverse
min-law proof. -/
def property4_from_repLTData_exact_no_inverse_min_laws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromRepLTDataExactNoInverseMinLawBridge S r) :
    Property4Conclusion S r :=
  property4_from_no_inverse_totalization_min_laws
    S r
    (noInverseTotalizationData_from_repLTDataExact S r data)

/-- The G106 Prop-to-data positivity interface is one way to supply the G107
rep+lt-data reduction interface. -/
def repLTDataExactReductionData_from_posDataOfExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromPosDataOfExactNoInverseMinLawBridge S r) :
    Property4ReductionDataFromRepLTDataExactNoInverseMinLawBridge S r where
  g96_data := data.g96_data
  representative_extraction := data.global_rep_selector
  prop_lt_to_data_lt :=
    cRealQuotLTDataOf_of_globalRep_and_posEventuallyDataOf
      data.global_rep_selector
      data.pos_eventually_data_of
  source_property4_min_laws_generated_from_rep_plus_lt_data :=
    data.source_property4_min_laws_generated_from_global_rep_plus_pos_data
  source_no_positive_inverse_totalization_input_for_min_laws :=
    data.source_no_positive_inverse_totalization_input_for_min_laws

end BishopRegularSeqTheorem118

/-- G107 package. -/
structure BishopRegularSeqTheorem118G107Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g106_package_available : Prop
  rep_lt_data_exact_data : Type 4
  minseq_laws_from_rep_lt_data :
    BishopRegularSeqTheorem118.Property4ScalarMinKernelClosedCoreLaws Arch ->
      CRealQuotRepresentativeExtractionObligation ->
        CRealQuotPropLTToDataLTObligation ->
          BishopRegularSeqTheorem118.Property4MinSeqQuotientTransportClosedCoreLaws
            Arch
  no_inverse_bridge_from_rep_lt_data :
    rep_lt_data_exact_data ->
      BishopRegularSeqTheorem118.Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge
        S
  property4_rep_lt_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_rep_lt_data_no_inverse :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_rep_lt_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_min_laws_need_rep_plus_lt_data_not_inverse : Prop
  pos_eventually_route_is_supplier_of_lt_data : Prop

def bishopRegularSeqTheorem118G107Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G107Package S where
  g106_package_available := True
  rep_lt_data_exact_data :=
    BishopRegularSeqTheorem118.Property4NoInverseMinLawRepLTDataExactData S
  minseq_laws_from_rep_lt_data := fun laws rep ltDataOf =>
    BishopRegularSeqTheorem118.minSeqQuotientTransportCoreLaws_from_repLTDataNoInverse
      Arch laws rep ltDataOf
  no_inverse_bridge_from_rep_lt_data :=
    BishopRegularSeqTheorem118.noInverseMinSeqQuotientTransportBridge_from_repLTDataExact
      S
  property4_rep_lt_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromRepLTDataExactNoInverseMinLawBridge
      S
  property4_from_rep_lt_data_no_inverse := fun r data =>
    BishopRegularSeqTheorem118.property4_from_repLTData_exact_no_inverse_min_laws
      S r data
  source_min_laws_need_rep_plus_lt_data_not_inverse := True
  pos_eventually_route_is_supplier_of_lt_data := True

/-- Progress after G107: the no-inverse min-law route is connected directly to
quotient representative extraction plus Prop-to-data strict-order extraction. -/
def bishopRegularSeqCh1To4ProgressAfterG107 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G107: routed the no-inverse min-law bridge directly through quotient \
    representative extraction plus ltQuot-to-ltQuotData extraction; \
    PosEventually data is now only a supplier of the lt-data extractor."


end BishopCReal
