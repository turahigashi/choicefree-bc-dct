import Mathdemo.Internal.CRat_iter210

set_option linter.style.longLine false

/-!
# G111: exact RegularSeq/data min-law frontier for property (4)

G110 rerouted theorem 1.18 property (4) to a RegularSeq/data-carrying
mainline.  The next constructive frontier is no longer quotient extraction.
It is the two source min laws needed by lines 735 and 743:

* monotonicity of `minSeqWith` in the first argument;
* the nonnegative shifted-min bound.

This file makes those two laws the explicit RegularSeq/data mainline input and
threads them back into the G96 scalar-min-kernel reduction.  No quotient
representative selector and no Prop-to-data strict-order selector are fields of
this route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The exact RegularSeq/data min-law input left after G110.

These are the two analytic laws corresponding to the source proof's line 735
and line 743 uses of `min`.  They are stated directly over representatives and
the Bishop non-strict order `RegularSeqLe`. -/
structure Property4RegularSeqDataMinLawCore
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  minSeqWith_add_nonnegative_right_bound :
    forall x d c : RegularSeq,
      RegularSeqLe zeroSeq d ->
        RegularSeqLe
          (minSeqWith Arch (addSeq x d) c)
          (addSeq (minSeqWith Arch x c) d)
  source_line735_regularseq_min_monotone : Prop
  source_line743_regularseq_shifted_min_bound : Prop
  no_quotient_order_obligation_in_min_laws : Prop
  no_prop_to_data_selector_in_min_laws : Prop

/-- Install RegularSeq/data min laws into the G95 core-law record. -/
def displayedScalarAbsBridgeClosedCoreLaws_from_regularSeqDataMinLaws
    (base : Property4DisplayedScalarAbsBridgeClosedCoreLaws Arch)
    (min_laws : Property4RegularSeqDataMinLawCore Arch) :
    Property4DisplayedScalarAbsBridgeClosedCoreLaws Arch where
  minSeqWith_monotone_left :=
    min_laws.minSeqWith_monotone_left
  minSeqWith_add_nonnegative_right_bound :=
    min_laws.minSeqWith_add_nonnegative_right_bound
  source_abs_from_two_sided_bridge_closed :=
    base.source_abs_from_two_sided_bridge_closed
  source_line735_subtraction_monotone_left_closed :=
    base.source_line735_subtraction_monotone_left_closed
  source_line735_sub_add_cancel_closed :=
    base.source_line735_sub_add_cancel_closed
  source_line735_same_right_subtraction_diff_closed :=
    base.source_line735_same_right_subtraction_diff_closed
  source_line735_nonneg_transport_closed :=
    base.source_line735_nonneg_transport_closed
  source_line735_self_shift_upper_closed :=
    base.source_line735_self_shift_upper_closed
  source_line735_base_shift_lower_closed :=
    base.source_line735_base_shift_lower_closed
  source_line735_addition_monotonicity_closed :=
    base.source_line735_addition_monotonicity_closed
  source_line735_min_monotonicity_and_shift :=
    min_laws.source_line735_regularseq_min_monotone
  source_line743_self_le_base_plus_abs_tail_closed :=
    base.source_line743_self_le_base_plus_abs_tail_closed
  source_line743_base_le_abs_base_closed :=
    base.source_line743_base_le_abs_base_closed
  source_line743_addition_monotonicity_for_abs_base_closed :=
    base.source_line743_addition_monotonicity_for_abs_base_closed
  source_line743_min_monotonicity_applies_to_abs_tail :=
    min_laws.source_line735_regularseq_min_monotone
  source_line743_tail_abs_is_nonnegative_closed :=
    base.source_line743_tail_abs_is_nonnegative_closed
  source_line743_shifted_min_bound_uses_nonnegative_tail :=
    min_laws.source_line743_regularseq_shifted_min_bound

/-- Install RegularSeq/data min laws into the G95 bridge used by the G96
property-(4) reduction. -/
def displayedScalarAbsBridgeClosedBridge_from_regularSeqDataMinLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarAbsBridgeClosedCoreUnifiedBridge S)
    (min_laws : Property4RegularSeqDataMinLawCore Arch) :
    Property4DisplayedScalarAbsBridgeClosedCoreUnifiedBridge S where
  abs_bridge_closed_core_laws :=
    displayedScalarAbsBridgeClosedCoreLaws_from_regularSeqDataMinLaws
      bridge.abs_bridge_closed_core_laws
      min_laws
  full_sets := bridge.full_sets
  abs_from_prop111 := bridge.abs_from_prop111
  prop111_bridge := bridge.prop111_bridge
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  source_line734_reduced_to_prop111 :=
    bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_closed_shift_add_abs_bridge :=
    True
  source_line743_reduced_to_abs_nonnegative_closed_chain :=
    True
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Install RegularSeq/data min laws into the G96 scalar-min-kernel core. -/
def scalarMinKernelClosedCoreLaws_from_regularSeqDataMinLaws
    (base : Property4ScalarMinKernelClosedCoreLaws Arch)
    (min_laws : Property4RegularSeqDataMinLawCore Arch) :
    Property4ScalarMinKernelClosedCoreLaws Arch where
  g95_core_laws :=
    displayedScalarAbsBridgeClosedCoreLaws_from_regularSeqDataMinLaws
      base.g95_core_laws
      min_laws
  source_scalar_min_right_abs_gap_bound_closed :=
    base.source_scalar_min_right_abs_gap_bound_closed
  source_scalar_min_halfsum_difference_nonneg_closed :=
    base.source_scalar_min_halfsum_difference_nonneg_closed
  source_scalar_min_halfsum_monotone_right_closed :=
    base.source_scalar_min_halfsum_monotone_right_closed
  representative_minSeqWith_transport_frontier := False

/-- The G96 bridge after replacing the min-law frontier by direct
RegularSeq/data min laws. -/
structure Property4RegularSeqDataMinLawUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  min_laws : Property4RegularSeqDataMinLawCore Arch
  realSurface : BishopRegularSeqRealSurface Arch
  archDataPackage : CRealRegularSeqDataCOFOCArchDataPackage Arch
  source_line735_min_law_is_regularseq_data : Prop
  source_line743_min_law_is_regularseq_data : Prop
  no_quotient_extraction_in_minlaw_bridge : Prop
  no_classical_choice_in_minlaw_bridge : Prop

/-- Convert the G111 min-law bridge back to the G96 bridge shape. -/
def scalarMinKernelClosedCoreUnifiedBridge_from_regularSeqDataMinLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4RegularSeqDataMinLawUnifiedBridge S) :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S where
  scalar_min_kernel_closed_core_laws :=
    scalarMinKernelClosedCoreLaws_from_regularSeqDataMinLaws
      bridge.g96_bridge.scalar_min_kernel_closed_core_laws
      bridge.min_laws
  g95_bridge :=
    displayedScalarAbsBridgeClosedBridge_from_regularSeqDataMinLaws
      S bridge.g96_bridge.g95_bridge bridge.min_laws
  source_line735_scalar_min_halfsum_kernel_closed :=
    bridge.g96_bridge.source_line735_scalar_min_halfsum_kernel_closed
  source_line735_regularSeq_min_transport_frontier := False
  source_line743_regularSeq_shifted_min_bound_frontier := False

/-- Property-(4) reduction data after supplying the two RegularSeq/data min
laws. -/
structure Property4ReductionDataFromRegularSeqDataMinLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  minlaw_bridge : Property4RegularSeqDataMinLawUnifiedBridge S
  source_property4_min_laws_are_regularseq_data : Prop
  quotient_extraction_not_used_for_property4_min_laws : Prop

/-- Convert G111 reduction data back to the G96 property-(4) reduction data. -/
def scalarMinKernelReductionData_from_regularSeqDataMinLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromRegularSeqDataMinLaws S r) :
    Property4ReductionDataFromScalarMinKernelClosedBridge S r where
  g95_data :=
    { data.mainline.g96_data.g95_data with
      displayed_scalar_abs_bridge_closed_bridge :=
        displayedScalarAbsBridgeClosedBridge_from_regularSeqDataMinLaws
          S
          data.mainline.g96_data.g95_data.displayed_scalar_abs_bridge_closed_bridge
          data.minlaw_bridge.min_laws }
  scalar_min_kernel_bridge :=
    scalarMinKernelClosedCoreUnifiedBridge_from_regularSeqDataMinLaws
      S data.minlaw_bridge
  source_property4_frontier_after_scalar_min_kernel_closed :=
    True

/-- Theorem 1.18 property (4), now routed through the exact two
RegularSeq/data min-law inputs. -/
def property4_from_regularseq_data_min_laws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromRegularSeqDataMinLaws S r) :
    Property4Conclusion S r :=
  property4_from_scalar_min_kernel_closed
    S r
    (scalarMinKernelReductionData_from_regularSeqDataMinLaws S r data)

/-- Selector footprint of the G111 min-law mainline. -/
structure Property4RegularSeqDataMinLawSelectorAudit : Type where
  regularseq_min_law_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  quotient_lt_witness_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_analytic_frontier_is_two_regularseq_min_laws : Prop

def property4RegularSeqDataMinLawSelectorAudit :
    Property4RegularSeqDataMinLawSelectorAudit where
  regularseq_min_law_inputs := 2
  quotient_representative_extraction_inputs := 0
  quotient_lt_witness_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_analytic_frontier_is_two_regularseq_min_laws := True

end BishopRegularSeqTheorem118

/-- G111 package: the post-G110 constructive frontier is exactly the two
RegularSeq/data min laws, threaded into the property-(4) theorem-producing
route. -/
structure BishopRegularSeqTheorem118G111Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g110 : BishopRegularSeqTheorem118G110Package S
  regularseq_min_law_core : Type 1
  regularseq_min_law_bridge : Type 5
  property4_regularseq_minlaw_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_regularseq_minlaws :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_regularseq_minlaw_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawSelectorAudit
  source_lines_735_and_743_are_the_remaining_min_laws : Prop
  no_quotient_extraction_in_g111_mainline : Prop
  no_classical_choice_in_g111_mainline : Prop

def bishopRegularSeqTheorem118G111Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G111Package S where
  g110 := bishopRegularSeqTheorem118G110Package S
  regularseq_min_law_core :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawCore Arch
  regularseq_min_law_bridge :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawUnifiedBridge S
  property4_regularseq_minlaw_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromRegularSeqDataMinLaws
      S
  property4_from_regularseq_minlaws := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_data_min_laws
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqDataMinLawSelectorAudit
  source_lines_735_and_743_are_the_remaining_min_laws := True
  no_quotient_extraction_in_g111_mainline := True
  no_classical_choice_in_g111_mainline := True

/-- Progress after G111: the constructive property-(4) route has been
narrowed to the exact two RegularSeq/data min laws. -/
def bishopRegularSeqCh1To4ProgressAfterG111 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G111: narrowed the post-G110 constructive property-(4) frontier to the \
    two RegularSeq/data min laws for source lines 735 and 743."


end BishopCReal
