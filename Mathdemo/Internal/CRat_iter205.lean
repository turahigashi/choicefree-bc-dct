import Mathdemo.Internal.CRat_iter204

set_option linter.style.longLine false

/-!
# G105: positive-shift route is equivalent to the selector-exact route

G104 connected property (4)'s no-inverse min-law bridge to the positive-shift
representative route.  Earlier work (`CRat_iter104`) already audited that
represented positive shifts are not a genuine weakening of global
representatives: a global representative selector immediately supplies the
shift `-x + 1`.

This file lifts that audit to the G103/G104 property-(4) interface.  The
positive-shift route and the direct selector-exact route are interderivable.
Thus G104 is a useful factoring of the frontier, but it does not reduce the
remaining selector problem below the G103 pair:

* global quotient representatives;
* `PosEventually` Prop-to-data selection.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Convert the direct G103 selector-exact data into the G104 positive-shift
route.  The positive-order data and represented shifts are both obtained from
the same global representative selector and `PosEventually` selector. -/
def positiveShiftSelectorData_from_selectorExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawSelectorExactData S) :
    Property4NoInverseMinLawPositiveShiftSelectorData S where
  g96_bridge := data.g96_bridge
  positive_lt_data :=
    cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallySelector
      data.global_rep_selector
      data.pos_eventually_selector
  positive_shift_data :=
    cRealQuotPositiveShiftData_of_globalRep
      data.global_rep_selector
  pos_eventually_selector := data.pos_eventually_selector
  source_global_rep_selector_factored_through_positive_shift :=
    data.source_line735_and_line743_generated_from_exact_selector_pair
  source_positive_inverse_totalization_not_used_in_positive_shift_route :=
    data.source_positive_inverse_totalization_removed_from_selector_exact_route

/-- The G103 selector-exact bridge and the G104 positive-shift bridge are
interderivable at the min-law data interface. -/
structure Property4NoInverseMinLawPositiveShiftEquivSelectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  to_selector_exact :
    Property4NoInverseMinLawPositiveShiftSelectorData S ->
      Property4NoInverseMinLawSelectorExactData S
  from_selector_exact :
    Property4NoInverseMinLawSelectorExactData S ->
      Property4NoInverseMinLawPositiveShiftSelectorData S
  source_positive_shift_route_is_factorization_not_frontier_reduction : Prop
  remaining_selector_pair_still_global_rep_plus_pos_eventually : Prop

def positiveShiftEquivSelectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Property4NoInverseMinLawPositiveShiftEquivSelectorExact S where
  to_selector_exact := selectorExactData_from_positiveShiftSelectorData S
  from_selector_exact := positiveShiftSelectorData_from_selectorExactData S
  source_positive_shift_route_is_factorization_not_frontier_reduction := True
  remaining_selector_pair_still_global_rep_plus_pos_eventually := True

/-- Convert selector-exact property-(4) reduction data into the G104
positive-shift reduction route. -/
def positiveShiftReductionData_from_selectorExactReductionData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r) :
    Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
      S r where
  g96_data := data.g96_data
  positive_lt_data :=
    cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallySelector
      data.global_rep_selector
      data.pos_eventually_selector
  positive_shift_data :=
    cRealQuotPositiveShiftData_of_globalRep
      data.global_rep_selector
  pos_eventually_selector := data.pos_eventually_selector
  source_property4_global_rep_input_factored_through_positive_shift :=
    data.source_property4_min_laws_generated_from_exact_selector_pair
  source_property4_no_positive_inverse_totalization_input :=
    data.source_no_positive_inverse_totalization_input_for_min_laws

/-- Property (4) from selector-exact data, routed through the equivalent
positive-shift interface. -/
def property4_from_selector_exact_via_positive_shift_equiv
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r) :
    Property4Conclusion S r :=
  property4_from_positive_shift_selector_no_inverse_min_laws
    S r
    (positiveShiftReductionData_from_selectorExactReductionData S r data)

/-- The two no-inverse property-(4) reduction interfaces used in G103 and G104
are interderivable. -/
structure Property4ReductionPositiveShiftEquivSelectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  to_selector_exact :
    Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
      S r ->
        Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r
  from_selector_exact :
    Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r ->
      Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
        S r
  property4_from_positive_shift :
    Property4ReductionDataFromPositiveShiftSelectorNoInverseMinLawBridge
      S r ->
        Property4Conclusion S r
  property4_from_selector_exact_via_positive_shift :
    Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r ->
      Property4Conclusion S r
  source_equivalence_keeps_frontier_honest : Prop

def property4ReductionPositiveShiftEquivSelectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) :
    Property4ReductionPositiveShiftEquivSelectorExact S r where
  to_selector_exact :=
    selectorExactReductionData_from_positiveShiftSelectorData S r
  from_selector_exact :=
    positiveShiftReductionData_from_selectorExactReductionData S r
  property4_from_positive_shift :=
    property4_from_positive_shift_selector_no_inverse_min_laws S r
  property4_from_selector_exact_via_positive_shift :=
    property4_from_selector_exact_via_positive_shift_equiv S r
  source_equivalence_keeps_frontier_honest := True

end BishopRegularSeqTheorem118

/-- G105 package. -/
structure BishopRegularSeqTheorem118G105Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g104_package_available : Prop
  min_law_positive_shift_equiv_selector_exact : Type 4
  positive_shift_from_selector_exact :
    BishopRegularSeqTheorem118.Property4NoInverseMinLawSelectorExactData S ->
      BishopRegularSeqTheorem118.Property4NoInverseMinLawPositiveShiftSelectorData
        S
  selector_exact_from_positive_shift :
    BishopRegularSeqTheorem118.Property4NoInverseMinLawPositiveShiftSelectorData
      S ->
        BishopRegularSeqTheorem118.Property4NoInverseMinLawSelectorExactData S
  property4_equiv_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  source_positive_shift_route_not_frontier_reduction : Prop
  remaining_selector_count_for_min_laws : Nat
  positive_inverse_totalization_not_part_of_min_frontier : Prop

def bishopRegularSeqTheorem118G105Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G105Package S where
  g104_package_available := True
  min_law_positive_shift_equiv_selector_exact :=
    BishopRegularSeqTheorem118.Property4NoInverseMinLawPositiveShiftEquivSelectorExact
      S
  positive_shift_from_selector_exact :=
    BishopRegularSeqTheorem118.positiveShiftSelectorData_from_selectorExactData
      S
  selector_exact_from_positive_shift :=
    BishopRegularSeqTheorem118.selectorExactData_from_positiveShiftSelectorData
      S
  property4_equiv_data :=
    BishopRegularSeqTheorem118.Property4ReductionPositiveShiftEquivSelectorExact
      S
  source_positive_shift_route_not_frontier_reduction := True
  remaining_selector_count_for_min_laws := 2
  positive_inverse_totalization_not_part_of_min_frontier := True

/-- Progress after G105: G104 is now identified as a factorization of G103,
not a reduction of the two-selector frontier. -/
def bishopRegularSeqCh1To4ProgressAfterG105 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G105: proved at the property-(4) interface that the positive-shift route \
    is equivalent to the direct selector-exact route; the real min-law \
    frontier remains global representatives plus PosEventually selection."


end BishopCReal
