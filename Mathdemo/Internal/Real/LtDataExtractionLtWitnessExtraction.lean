import Mathdemo.Internal.Real.NoInverseMinLawsRepresentativeExtraction

set_option linter.style.longLine false

/-!
# G108: lt-data extraction is the lt-witness extraction frontier

G107 routed the no-inverse min-law bridge through
`CRealQuotPropLTToDataLTObligation`.  Since `ltQuotData` is an abbreviation for
`CRealQuotLTDataWitness`, this obligation is exactly the witness-extraction
frontier isolated in `CRealQuotientCotransitivityDataBridge`.

This file lifts that definitional identification to the property-(4)
interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- `ltQuot -> ltQuotData` is the same obligation as extracting the explicit
`CRealQuotLTDataWitness`. -/
def propLTToData_from_ltWitnessExtraction
    (ltWitness : CRealQuotLTWitnessExtractionObligation) :
    CRealQuotPropLTToDataLTObligation :=
  ltWitness

/-- Conversely, the Prop-to-data strict-order bridge supplies explicit
strict-order witnesses. -/
def ltWitnessExtraction_from_propLTToData
    (ltDataOf : CRealQuotPropLTToDataLTObligation) :
    CRealQuotLTWitnessExtractionObligation :=
  ltDataOf

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- No-inverse min-law data stated with the explicit lt-witness extraction
obligation. -/
structure Property4NoInverseMinLawRepLTWitnessExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g96_bridge :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S
  representative_extraction :
    CRealQuotRepresentativeExtractionObligation
  lt_witness_extraction :
    CRealQuotLTWitnessExtractionObligation
  source_line735_and_line743_generated_from_rep_plus_lt_witness : Prop
  source_positive_inverse_totalization_removed_from_rep_lt_witness_route : Prop

/-- Convert the explicit lt-witness interface into the G107 rep+lt-data
interface. -/
def repLTDataExactData_from_repLTWitnessExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawRepLTWitnessExactData S) :
    Property4NoInverseMinLawRepLTDataExactData S where
  g96_bridge := data.g96_bridge
  representative_extraction := data.representative_extraction
  prop_lt_to_data_lt :=
    propLTToData_from_ltWitnessExtraction
      data.lt_witness_extraction
  source_line735_and_line743_generated_from_rep_plus_lt_data :=
    data.source_line735_and_line743_generated_from_rep_plus_lt_witness
  source_positive_inverse_totalization_removed_from_rep_lt_data_route :=
    data.source_positive_inverse_totalization_removed_from_rep_lt_witness_route

/-- Convert the G107 rep+lt-data interface back to explicit lt-witness
extraction. -/
def repLTWitnessExactData_from_repLTDataExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawRepLTDataExactData S) :
    Property4NoInverseMinLawRepLTWitnessExactData S where
  g96_bridge := data.g96_bridge
  representative_extraction := data.representative_extraction
  lt_witness_extraction :=
    ltWitnessExtraction_from_propLTToData
      data.prop_lt_to_data_lt
  source_line735_and_line743_generated_from_rep_plus_lt_witness :=
    data.source_line735_and_line743_generated_from_rep_plus_lt_data
  source_positive_inverse_totalization_removed_from_rep_lt_witness_route :=
    data.source_positive_inverse_totalization_removed_from_rep_lt_data_route

/-- Property-(4) reduction data using explicit lt-witness extraction. -/
structure Property4ReductionDataFromRepLTWitnessExactNoInverseMinLawBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g96_data :
    Property4ReductionDataFromScalarMinKernelClosedBridge S r
  representative_extraction :
    CRealQuotRepresentativeExtractionObligation
  lt_witness_extraction :
    CRealQuotLTWitnessExtractionObligation
  source_property4_min_laws_generated_from_rep_plus_lt_witness : Prop
  source_no_positive_inverse_totalization_input_for_min_laws : Prop

/-- Convert explicit lt-witness reduction data into the G107 rep+lt-data
reduction interface. -/
def repLTDataExactReductionData_from_repLTWitnessExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromRepLTWitnessExactNoInverseMinLawBridge S r) :
    Property4ReductionDataFromRepLTDataExactNoInverseMinLawBridge S r where
  g96_data := data.g96_data
  representative_extraction := data.representative_extraction
  prop_lt_to_data_lt :=
    propLTToData_from_ltWitnessExtraction
      data.lt_witness_extraction
  source_property4_min_laws_generated_from_rep_plus_lt_data :=
    data.source_property4_min_laws_generated_from_rep_plus_lt_witness
  source_no_positive_inverse_totalization_input_for_min_laws :=
    data.source_no_positive_inverse_totalization_input_for_min_laws

/-- Property (4) from representative extraction plus explicit strict-order
witness extraction. -/
def property4_from_repLTWitness_exact_no_inverse_min_laws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromRepLTWitnessExactNoInverseMinLawBridge S r) :
    Property4Conclusion S r :=
  property4_from_repLTData_exact_no_inverse_min_laws
    S r
    (repLTDataExactReductionData_from_repLTWitnessExact S r data)

/-- The G107 rep+lt-data interface and the explicit lt-witness interface are
interderivable by definitional unfolding of `ltQuotData`. -/
structure Property4RepLTDataEquivRepLTWitness
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  to_lt_data :
    Property4NoInverseMinLawRepLTWitnessExactData S ->
      Property4NoInverseMinLawRepLTDataExactData S
  to_lt_witness :
    Property4NoInverseMinLawRepLTDataExactData S ->
      Property4NoInverseMinLawRepLTWitnessExactData S
  source_lt_data_is_lt_witness_record : Prop

def repLTDataEquivRepLTWitness
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Property4RepLTDataEquivRepLTWitness S where
  to_lt_data := repLTDataExactData_from_repLTWitnessExactData S
  to_lt_witness := repLTWitnessExactData_from_repLTDataExactData S
  source_lt_data_is_lt_witness_record := True

end BishopRegularSeqTheorem118

/-- G108 package. -/
structure BishopRegularSeqTheorem118G108Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g107_package_available : Prop
  lt_data_from_lt_witness :
    CRealQuotLTWitnessExtractionObligation ->
      CRealQuotPropLTToDataLTObligation
  lt_witness_from_lt_data :
    CRealQuotPropLTToDataLTObligation ->
      CRealQuotLTWitnessExtractionObligation
  rep_lt_witness_data : Type 4
  rep_lt_data_equiv_rep_lt_witness : Type 4
  property4_rep_lt_witness_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_rep_lt_witness_no_inverse :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_rep_lt_witness_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_order_frontier_is_lt_witness_extraction : Prop

def bishopRegularSeqTheorem118G108Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G108Package S where
  g107_package_available := True
  lt_data_from_lt_witness := propLTToData_from_ltWitnessExtraction
  lt_witness_from_lt_data := ltWitnessExtraction_from_propLTToData
  rep_lt_witness_data :=
    BishopRegularSeqTheorem118.Property4NoInverseMinLawRepLTWitnessExactData
      S
  rep_lt_data_equiv_rep_lt_witness :=
    BishopRegularSeqTheorem118.Property4RepLTDataEquivRepLTWitness S
  property4_rep_lt_witness_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromRepLTWitnessExactNoInverseMinLawBridge
      S
  property4_from_rep_lt_witness_no_inverse := fun r data =>
    BishopRegularSeqTheorem118.property4_from_repLTWitness_exact_no_inverse_min_laws
      S r data
  source_order_frontier_is_lt_witness_extraction := True

/-- Progress after G108: the order half of the min-law frontier is the explicit
lt-witness extraction obligation. -/
def bishopRegularSeqCh1To4ProgressAfterG108 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G108: identified ltQuot-to-ltQuotData extraction with explicit \
    CRealQuotLTDataWitness extraction at the property-(4) min-law interface."


end BishopCReal
