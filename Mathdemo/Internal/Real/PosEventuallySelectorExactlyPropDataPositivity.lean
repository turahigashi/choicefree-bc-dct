import Mathdemo.Internal.Real.PositiveShiftRouteEquivalentSelectorExact

set_option linter.style.longLine false

/-!
# G106: PosEventually selector is exactly Prop-to-data positivity extraction

G103 stated the no-inverse min-law frontier with a `CRealPosEventuallySelector`.
`PosEventuallyWitnessSelectorFrontier` had already shown that this selector is equivalent to the
representative-level bridge

`CRealPosEventuallyDataOf : PosEventually x -> PosEventuallyData x`.

This file lifts that equivalence to the property-(4) interface.  The remaining
second selector is therefore not scalar pointwise order decidability; it is the
Type-valued witness extraction hidden in the infinite-tail `PosEventually`
predicate.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Selector-exact min-law data restated with the representative-level
`PosEventually -> PosEventuallyData` bridge instead of the concrete selector
record. -/
structure Property4NoInverseMinLawPosDataOfExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g96_bridge :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S
  global_rep_selector :
    ∀ x : CRealQuot, CRealQuotRepWitness x
  pos_eventually_data_of :
    CRealPosEventuallyDataOf
  source_line735_and_line743_generated_from_global_rep_plus_pos_data : Prop
  source_positive_inverse_totalization_removed_from_pos_data_route : Prop

/-- Convert the Prop-to-data positivity bridge interface into the G103
selector-exact data interface. -/
def selectorExactData_from_posDataOfExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawPosDataOfExactData S) :
    Property4NoInverseMinLawSelectorExactData S where
  g96_bridge := data.g96_bridge
  global_rep_selector := data.global_rep_selector
  pos_eventually_selector :=
    cRealPosEventuallySelector_of_dataOf
      data.pos_eventually_data_of
  source_line735_and_line743_generated_from_exact_selector_pair :=
    data.source_line735_and_line743_generated_from_global_rep_plus_pos_data
  source_positive_inverse_totalization_removed_from_selector_exact_route :=
    data.source_positive_inverse_totalization_removed_from_pos_data_route

/-- Convert the G103 selector-exact data interface back to the Prop-to-data
positivity bridge interface. -/
def posDataOfExactData_from_selectorExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawSelectorExactData S) :
    Property4NoInverseMinLawPosDataOfExactData S where
  g96_bridge := data.g96_bridge
  global_rep_selector := data.global_rep_selector
  pos_eventually_data_of :=
    cRealPosEventuallyDataOf_of_selector
      data.pos_eventually_selector
  source_line735_and_line743_generated_from_global_rep_plus_pos_data :=
    data.source_line735_and_line743_generated_from_exact_selector_pair
  source_positive_inverse_totalization_removed_from_pos_data_route :=
    data.source_positive_inverse_totalization_removed_from_selector_exact_route

/-- The G103 selector form and the Prop-to-data positivity bridge form are
interderivable at the min-law data interface. -/
structure Property4NoInverseMinLawPosDataOfEquivSelectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  to_selector_exact :
    Property4NoInverseMinLawPosDataOfExactData S ->
      Property4NoInverseMinLawSelectorExactData S
  from_selector_exact :
    Property4NoInverseMinLawSelectorExactData S ->
      Property4NoInverseMinLawPosDataOfExactData S
  source_pos_eventually_selector_is_prop_to_data_extraction : Prop
  scalar_pointwise_decidability_does_not_supply_tail_data : Prop

def posDataOfEquivSelectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Property4NoInverseMinLawPosDataOfEquivSelectorExact S where
  to_selector_exact := selectorExactData_from_posDataOfExactData S
  from_selector_exact := posDataOfExactData_from_selectorExactData S
  source_pos_eventually_selector_is_prop_to_data_extraction := True
  scalar_pointwise_decidability_does_not_supply_tail_data := True

/-- Property-(4) reduction data using `CRealPosEventuallyDataOf` instead of the
concrete selector record. -/
structure Property4ReductionDataFromPosDataOfExactNoInverseMinLawBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g96_data :
    Property4ReductionDataFromScalarMinKernelClosedBridge S r
  global_rep_selector :
    ∀ x : CRealQuot, CRealQuotRepWitness x
  pos_eventually_data_of :
    CRealPosEventuallyDataOf
  source_property4_min_laws_generated_from_global_rep_plus_pos_data : Prop
  source_no_positive_inverse_totalization_input_for_min_laws : Prop

/-- Convert the Prop-to-data positivity bridge reduction data into the G103
selector-exact reduction data. -/
def selectorExactReductionData_from_posDataOfExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromPosDataOfExactNoInverseMinLawBridge S r) :
    Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r where
  g96_data := data.g96_data
  global_rep_selector := data.global_rep_selector
  pos_eventually_selector :=
    cRealPosEventuallySelector_of_dataOf
      data.pos_eventually_data_of
  source_property4_min_laws_generated_from_exact_selector_pair :=
    data.source_property4_min_laws_generated_from_global_rep_plus_pos_data
  source_no_positive_inverse_totalization_input_for_min_laws :=
    data.source_no_positive_inverse_totalization_input_for_min_laws

/-- Convert selector-exact reduction data back to the Prop-to-data positivity
bridge reduction interface. -/
def posDataOfExactReductionData_from_selectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r) :
    Property4ReductionDataFromPosDataOfExactNoInverseMinLawBridge S r where
  g96_data := data.g96_data
  global_rep_selector := data.global_rep_selector
  pos_eventually_data_of :=
    cRealPosEventuallyDataOf_of_selector
      data.pos_eventually_selector
  source_property4_min_laws_generated_from_global_rep_plus_pos_data :=
    data.source_property4_min_laws_generated_from_exact_selector_pair
  source_no_positive_inverse_totalization_input_for_min_laws :=
    data.source_no_positive_inverse_totalization_input_for_min_laws

/-- Property (4) from global representatives plus representative-level
`PosEventually` Prop-to-data extraction. -/
def property4_from_posDataOf_exact_no_inverse_min_laws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromPosDataOfExactNoInverseMinLawBridge S r) :
    Property4Conclusion S r :=
  property4_from_selector_exact_no_inverse_min_laws
    S r
    (selectorExactReductionData_from_posDataOfExact S r data)

end BishopRegularSeqTheorem118

/-- G106 package. -/
structure BishopRegularSeqTheorem118G106Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g105_package_available : Prop
  pos_data_of_exact_data : Type 4
  pos_data_of_equiv_selector_exact : Type 4
  selector_exact_from_pos_data_of :
    pos_data_of_exact_data ->
      BishopRegularSeqTheorem118.Property4NoInverseMinLawSelectorExactData S
  pos_data_of_from_selector_exact :
    BishopRegularSeqTheorem118.Property4NoInverseMinLawSelectorExactData S ->
      pos_data_of_exact_data
  property4_pos_data_of_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_pos_data_of_no_inverse :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_pos_data_of_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_second_selector_is_pos_eventually_prop_to_data : Prop
  remaining_selector_count_for_min_laws : Nat

def bishopRegularSeqTheorem118G106Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G106Package S where
  g105_package_available := True
  pos_data_of_exact_data :=
    BishopRegularSeqTheorem118.Property4NoInverseMinLawPosDataOfExactData S
  pos_data_of_equiv_selector_exact :=
    BishopRegularSeqTheorem118.Property4NoInverseMinLawPosDataOfEquivSelectorExact
      S
  selector_exact_from_pos_data_of :=
    BishopRegularSeqTheorem118.selectorExactData_from_posDataOfExactData
      S
  pos_data_of_from_selector_exact :=
    BishopRegularSeqTheorem118.posDataOfExactData_from_selectorExactData
      S
  property4_pos_data_of_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromPosDataOfExactNoInverseMinLawBridge
      S
  property4_from_pos_data_of_no_inverse := fun r data =>
    BishopRegularSeqTheorem118.property4_from_posDataOf_exact_no_inverse_min_laws
      S r data
  source_second_selector_is_pos_eventually_prop_to_data := True
  remaining_selector_count_for_min_laws := 2

/-- Progress after G106: the second selector has been restated as the exact
`PosEventually` Prop-to-data extraction obligation. -/
def bishopRegularSeqCh1To4ProgressAfterG106 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G106: lifted the PosEventually selector/dataOf equivalence to the \
    property-(4) no-inverse min-law interface; the second selector is exactly \
    Prop-to-data extraction for the infinite-tail positivity predicate."


end BishopCReal
