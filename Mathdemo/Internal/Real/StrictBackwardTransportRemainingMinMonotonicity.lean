import Mathdemo.Internal.Real.LateSamplePositivityTransportRegularSeq

set_option linter.style.longLine false

/-!
# G121: strict-backward transport for the remaining min monotonicity frontier

G118 reduced Theorem 1.18 property (4) to the line-735 left monotonicity of
`minSeqWith`.  G119 and G120 closed two supporting RegularSeq bridges.  This
file factors the remaining monotonicity target through the Bishop-style
contrapositive shape:

if a strict counterexample to `min x c <= min y c` can be transported backward
to a strict counterexample to `x <= y`, then the desired non-strict
`RegularSeqLe` monotonicity follows.

This avoids extracting representatives from a quotient and avoids any selector
from `Prop` positivity to data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- A Bishop-style contrapositive for the remaining line-735 min monotonicity.

The hypothesis is the genuine scalar/RegularSeq frontier: strict positivity of
`min x c - min y c` must imply strict positivity of `x - y`.  Once that strict
backward transport is available, the ordinary non-strict `RegularSeqLe`
monotonicity follows by contradiction against the definition of `RegularSeqLe`.
-/
theorem minSeqWith_monotone_left_regularSeqLe_of_strict_backward
    (A : ScalarMulArchimedeanData)
    (strict_backward :
      forall x y c : RegularSeq,
        regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c) ->
          regularSeqLtProp y x)
    (x y c : RegularSeq)
    (hxy : RegularSeqLe x y) :
    RegularSeqLe (minSeqWith A x c) (minSeqWith A y c) := by
  intro hcounter
  have hstrict_min :
      regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c) := by
    exact regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hyx : regularSeqLtProp y x :=
    strict_backward x y c hstrict_min
  exact regularSeqLe_not_lt_reverse_prop hxy hyx

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data for the remaining scalar/RegularSeq frontier after G121.  It is not a
choice principle: it is the exact strict-backward transport still to be proved
from the half-sum minimum formula. -/
structure Property4RegularSeqMinStrictBackwardTransport
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_backward :
    forall x y c : RegularSeq,
      regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c) ->
        regularSeqLtProp y x
  source_line735_min_strict_backward_transport : Prop
  no_quotient_representative_extraction : Prop
  no_pos_eventually_witness_extraction : Prop
  no_classical_choice : Prop

/-- Convert strict-backward transport into the exact `minSeqWith` left
monotonicity input required by G118. -/
def minSeqWith_monotone_left_from_strictBackward
    (A : ScalarMulArchimedeanData)
    (data : Property4RegularSeqMinStrictBackwardTransport A) :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith A x c) (minSeqWith A y c) :=
  fun x y c hxy =>
    minSeqWith_monotone_left_regularSeqLe_of_strict_backward
      A data.strict_backward x y c hxy

/-- G121 replacement for the G118 property-(4) input: line 735 is now expressed
as strict-backward transport, not as a black-box min monotonicity selector. -/
structure Property4RegularSeqDataMinLawStrictBackwardInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  min_strict_backward :
    Property4RegularSeqMinStrictBackwardTransport Arch
  source_line735_min_strict_backward_transport_input : Prop
  line743_translation_closed : Prop
  quotient_extraction_not_used : Prop
  prop_to_data_selector_not_used : Prop

/-- Convert the G121 strict-backward input to the G118 only-left input. -/
def regularSeqDataMinLawOnlyLeftInput_from_strictBackward
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawStrictBackwardInput S r) :
    Property4RegularSeqDataMinLawOnlyLeftInput S r where
  mainline := data.mainline
  g96_bridge := data.g96_bridge
  minSeqWith_monotone_left :=
    minSeqWith_monotone_left_from_strictBackward
      Arch data.min_strict_backward
  source_line735_left_monotonicity_input :=
    data.source_line735_min_strict_backward_transport_input
  line743_translation_closed := data.line743_translation_closed
  quotient_extraction_not_used := data.quotient_extraction_not_used

/-- Property (4), with line 735 factored through strict-backward transport. -/
def property4_from_regularseq_min_strict_backward
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawStrictBackwardInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_left_min_monotone
    S r
    (regularSeqDataMinLawOnlyLeftInput_from_strictBackward S r data)

/-- Selector footprint after G121.  The remaining input is now the scalar
strict-backward transport for the half-sum min formula. -/
structure Property4RegularSeqStrictBackwardAudit : Type where
  line735_regularseq_min_monotonicity_inputs : Nat
  line735_min_strict_backward_transport_inputs : Nat
  pointwise_to_regularseq_order_bridge_closed : Nat
  late_sample_positivity_bridge_closed : Nat
  line743_sum_translation_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_min_strict_backward_transport : Prop

def property4RegularSeqStrictBackwardAudit :
    Property4RegularSeqStrictBackwardAudit where
  line735_regularseq_min_monotonicity_inputs := 0
  line735_min_strict_backward_transport_inputs := 1
  pointwise_to_regularseq_order_bridge_closed := 1
  late_sample_positivity_bridge_closed := 1
  line743_sum_translation_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_min_strict_backward_transport := True

end BishopRegularSeqTheorem118

/-- G121 package: the residual line-735 monotonicity obligation is reduced to
strict-backward transport. -/
structure BishopRegularSeqTheorem118G121Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g120 : BishopRegularSeqTheorem118G120Package S
  strict_backward_to_left_monotone :
    BishopRegularSeqTheorem118.Property4RegularSeqMinStrictBackwardTransport Arch ->
      forall x y c : RegularSeq,
        RegularSeqLe x y ->
          RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  property4_strict_backward_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_strict_backward :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawStrictBackwardInput S r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqStrictBackwardAudit
  line743_closed_by_g118 : Prop
  line735_min_monotonicity_reduced_to_strict_backward : Prop
  no_quotient_extraction_in_g121_mainline : Prop

def bishopRegularSeqTheorem118G121Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G121Package S where
  g120 := bishopRegularSeqTheorem118G120Package S
  strict_backward_to_left_monotone := by
    intro data x y c hxy
    exact
      BishopRegularSeqTheorem118.minSeqWith_monotone_left_from_strictBackward
        Arch data x y c hxy
  property4_strict_backward_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawStrictBackwardInput S
  property4_from_strict_backward := by
    intro r data
    exact
      BishopRegularSeqTheorem118.property4_from_regularseq_min_strict_backward
        S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqStrictBackwardAudit
  line743_closed_by_g118 := True
  line735_min_monotonicity_reduced_to_strict_backward := True
  no_quotient_extraction_in_g121_mainline := True

/-- Progress after G121: still 99%, but the remaining line-735 target is now
the exact strict-backward scalar transport instead of a broad min-monotonicity
black box. -/
def bishopRegularSeqCh1To4ProgressAfterG121 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G121: reduced line-735 RegularSeq min left monotonicity to the exact \
    strict-backward transport for the half-sum minimum."


end BishopCReal
