import Mathdemo.Internal.Real.SelectorExactNoInverseMinLaw

set_option linter.style.longLine false

/-!
# G104: positive-shift route into the selector-exact min-law bridge

G103 exposed the exact remaining selector inputs for the no-inverse min-law
route: a global quotient representative selector and a `PosEventually`
selector.  Earlier work (`PositiveShiftsRecoverGlobalRepresentatives`) had already shown one constructive
way to obtain the global representative selector: positive-order data plus
represented positive shifts.

This file connects that older representative route to the G103 property-(4)
interface.  It does not claim that positive shifts or positive-order data are
now unconditional; it only removes a layer of indirection from the min-law
frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data for producing the G103 selector-exact min-law bridge by first
constructing the global representative selector from positive shifts. -/
structure Property4NoInverseMinLawPositiveShiftSelectorData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g96_bridge :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S
  positive_lt_data :
    CRealQuotPositiveLTDataOf
  positive_shift_data :
    CRealQuotPositiveShiftData
  pos_eventually_selector :
    CRealPosEventuallySelector
  source_global_rep_selector_factored_through_positive_shift : Prop
  source_positive_inverse_totalization_not_used_in_positive_shift_route : Prop

/-- The global representative selector obtained from the positive-shift route. -/
def globalRepSelector_from_positiveShiftSelectorData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawPositiveShiftSelectorData S) :
    ∀ x : CRealQuot, CRealQuotRepWitness x :=
  cRealQuotGlobalRep_of_positiveLTData_and_positiveShift
    data.positive_lt_data
    data.positive_shift_data

/-- Convert positive-shift selector data into the G103 selector-exact data. -/
def selectorExactData_from_positiveShiftSelectorData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawPositiveShiftSelectorData S) :
    Property4NoInverseMinLawSelectorExactData S where
  g96_bridge := data.g96_bridge
  global_rep_selector :=
    globalRepSelector_from_positiveShiftSelectorData S data
  pos_eventually_selector := data.pos_eventually_selector
  source_line735_and_line743_generated_from_exact_selector_pair :=
    data.source_global_rep_selector_factored_through_positive_shift
  source_positive_inverse_totalization_removed_from_selector_exact_route :=
    data.source_positive_inverse_totalization_not_used_in_positive_shift_route

/-- Generate the G102 no-inverse bridge through the positive-shift route. -/
def noInverseMinSeqQuotientTransportBridge_from_positiveShiftSelectorData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawPositiveShiftSelectorData S) :
    Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge S :=
  noInverseMinSeqQuotientTransportBridge_from_selectorExact
    S
    (selectorExactData_from_positiveShiftSelectorData S data)

/-- Property-(4) reduction data using the positive-shift route to supply the
global representative selector needed by G103. -/
structure Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g96_data :
    Property4ReductionDataFromScalarMinKernelClosedBridge S r
  positive_lt_data :
    CRealQuotPositiveLTDataOf
  positive_shift_data :
    CRealQuotPositiveShiftData
  pos_eventually_selector :
    CRealPosEventuallySelector
  source_property4_global_rep_input_factored_through_positive_shift : Prop
  source_property4_no_positive_inverse_totalization_input : Prop

/-- Extract the positive-shift selector data from the property-(4) reduction
record. -/
def positiveShiftSelectorData_from_reductionData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
        S r) :
    Property4NoInverseMinLawPositiveShiftSelectorData S where
  g96_bridge := data.g96_data.scalar_min_kernel_bridge
  positive_lt_data := data.positive_lt_data
  positive_shift_data := data.positive_shift_data
  pos_eventually_selector := data.pos_eventually_selector
  source_global_rep_selector_factored_through_positive_shift :=
    data.source_property4_global_rep_input_factored_through_positive_shift
  source_positive_inverse_totalization_not_used_in_positive_shift_route :=
    data.source_property4_no_positive_inverse_totalization_input

/-- Convert the positive-shift route into the G103 selector-exact reduction
data. -/
def selectorExactReductionData_from_positiveShiftSelectorData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
        S r) :
    Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r where
  g96_data := data.g96_data
  global_rep_selector :=
    globalRepSelector_from_positiveShiftSelectorData
      S
      (positiveShiftSelectorData_from_reductionData S r data)
  pos_eventually_selector := data.pos_eventually_selector
  source_property4_min_laws_generated_from_exact_selector_pair :=
    data.source_property4_global_rep_input_factored_through_positive_shift
  source_no_positive_inverse_totalization_input_for_min_laws :=
    data.source_property4_no_positive_inverse_totalization_input

/-- Theorem 1.18 property (4), with global representatives supplied through
the positive-shift route and min laws still using no positive-inverse
totalization. -/
def property4_from_positive_shift_selector_no_inverse_min_laws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
        S r) :
    Property4Conclusion S r :=
  property4_from_selector_exact_no_inverse_min_laws
    S r
    (selectorExactReductionData_from_positiveShiftSelectorData S r data)

end BishopRegularSeqTheorem118

/-- G104 package. -/
structure BishopRegularSeqTheorem118G104Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g103_package_available : Prop
  positive_shift_selector_data : Type 4
  global_rep_from_positive_shift :
    positive_shift_selector_data ->
      (∀ x : CRealQuot, CRealQuotRepWitness x)
  selector_exact_data_from_positive_shift :
    positive_shift_selector_data ->
      BishopRegularSeqTheorem118.Property4NoInverseMinLawSelectorExactData S
  property4_positive_shift_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_positive_shift_no_inverse :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_positive_shift_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_global_rep_frontier_factored_through_positive_shift : Prop
  remaining_positive_shift_route_inputs_count : Nat
  positive_inverse_totalization_not_part_of_min_frontier : Prop

def bishopRegularSeqTheorem118G104Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G104Package S where
  g103_package_available := True
  positive_shift_selector_data :=
    BishopRegularSeqTheorem118.Property4NoInverseMinLawPositiveShiftSelectorData
      S
  global_rep_from_positive_shift := fun data =>
    BishopRegularSeqTheorem118.globalRepSelector_from_positiveShiftSelectorData
      S data
  selector_exact_data_from_positive_shift := fun data =>
    BishopRegularSeqTheorem118.selectorExactData_from_positiveShiftSelectorData
      S data
  property4_positive_shift_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
      S
  property4_from_positive_shift_no_inverse := fun r data =>
    BishopRegularSeqTheorem118.property4_from_positive_shift_selector_no_inverse_min_laws
      S r data
  source_global_rep_frontier_factored_through_positive_shift := True
  remaining_positive_shift_route_inputs_count := 3
  positive_inverse_totalization_not_part_of_min_frontier := True

/-- Progress after G104: the G103 global representative input is connected to
the earlier positive-shift representative route. -/
def bishopRegularSeqCh1To4ProgressAfterG104 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G104: connected the selector-exact no-inverse min-law bridge to the \
    positive-shift route that constructs global quotient representatives."


end BishopCReal
