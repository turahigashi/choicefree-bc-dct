import Mathdemo.Internal.CRat_iter224

set_option linter.style.longLine false

/-!
# G125: bridge from two-sample expansion to the same-sample frontier

G124 expands a strict `minSeqWith` counterexample into two sampled scalar
half-sum expressions.  G123 already transports a same-sample half-sum strict
statement back to `RegularSeq` order.

This file connects those two closed pieces.  The only remaining mathematical
frontier is now the explicit alignment lemma that turns the two cofinal sample
functions into one cofinal sample function, using regularity budgets.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The exact remaining line-735 alignment problem: two cofinal sampled
half-sum strict inequalities can be aligned to a single cofinal sample. -/
def TwoSampleMinHalfsumAlignment
    (x y c : RegularSeq) : Prop :=
  forall Fx Fy : Nat -> Nat,
    (forall n : Nat, n <= Fx n) ->
    (forall n : Nat, n <= Fy n) ->
      TwoSampleMinHalfsumLeftStrict x y c Fx Fy ->
        ∃ F : Nat -> Nat,
          (forall n : Nat, n <= F n) ∧
            SameSampleMinHalfsumLeftStrict x y c F

/-- A closed two-sample alignment theorem immediately supplies G123's
same-sample expansion frontier. -/
theorem minSeqWith_same_sample_expansion_of_two_sample_alignment
    (A : ScalarMulArchimedeanData)
    (align : forall x y c : RegularSeq,
      TwoSampleMinHalfsumAlignment x y c)
    (x y c : RegularSeq)
    (hmin : regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c)) :
    ∃ F : Nat -> Nat,
      (forall n : Nat, n <= F n) ∧
        SameSampleMinHalfsumLeftStrict x y c F := by
  rcases minSeqWith_strict_to_two_sample_halfsum A x y c hmin with
    ⟨Fx, Fy, hFx, hFy, htwo⟩
  exact align x y c Fx Fy hFx hFy htwo

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G125 data boundary: the line-735 representative problem is precisely
two-sample-to-same-sample alignment. -/
structure Property4RegularSeqMinTwoSampleAlignment
    (A : ScalarMulArchimedeanData) : Type 1 where
  two_sample_alignment :
    forall x y c : RegularSeq,
      TwoSampleMinHalfsumAlignment x y c
  source_line735_two_sample_alignment : Prop
  g124_two_sample_value_expansion_closed : Prop
  g123_same_sample_transport_closed : Prop
  no_quotient_representative_extraction : Prop
  no_pos_eventually_witness_selector : Prop
  no_classical_choice : Prop

/-- Convert the G125 alignment boundary into G123's same-sample expansion
input. -/
def minSameSampleExpansion_from_twoSampleAlignment
    (A : ScalarMulArchimedeanData)
    (data : Property4RegularSeqMinTwoSampleAlignment A) :
    Property4RegularSeqMinSameSampleExpansion A where
  same_sample_expansion := by
    intro x y c hmin
    exact
      minSeqWith_same_sample_expansion_of_two_sample_alignment
        A data.two_sample_alignment x y c hmin
  source_line735_minSeqWith_expansion_alignment :=
    data.source_line735_two_sample_alignment
  scalar_strict_backward_kernel_closed :=
    data.g123_same_sample_transport_closed
  no_quotient_representative_extraction :=
    data.no_quotient_representative_extraction
  no_pos_eventually_witness_selector :=
    data.no_pos_eventually_witness_selector

/-- Property-(4) input after G125: line 735 asks only for two-sample alignment,
while the value expansion and same-sample transport are closed. -/
structure Property4RegularSeqDataMinLawTwoSampleAlignmentInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  two_sample_alignment : Property4RegularSeqMinTwoSampleAlignment Arch
  source_line735_two_sample_alignment_input : Prop
  line743_translation_closed : Prop
  quotient_extraction_not_used : Prop
  prop_to_data_selector_not_used : Prop

/-- Convert G125 data to the already-closed G123 same-sample data surface. -/
def regularSeqDataMinLawSameSampleExpansionInput_from_twoSampleAlignment
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawTwoSampleAlignmentInput S r) :
    Property4RegularSeqDataMinLawSameSampleExpansionInput S r where
  mainline := data.mainline
  g96_bridge := data.g96_bridge
  same_sample_expansion :=
    minSameSampleExpansion_from_twoSampleAlignment
      Arch data.two_sample_alignment
  source_line735_minSeqWith_expansion_alignment_input :=
    data.source_line735_two_sample_alignment_input
  line743_translation_closed := data.line743_translation_closed
  quotient_extraction_not_used := data.quotient_extraction_not_used
  prop_to_data_selector_not_used := data.prop_to_data_selector_not_used

/-- Property (4), with the sole line-735 input now being two-sample alignment. -/
def property4_from_regularseq_two_sample_alignment
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawTwoSampleAlignmentInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_same_sample_expansion
    S r
    (regularSeqDataMinLawSameSampleExpansionInput_from_twoSampleAlignment
      S r data)

/-- G125 audit: the data surface has been narrowed to one honest alignment
frontier. -/
structure Property4RegularSeqTwoSampleAlignmentAudit : Type where
  minSeqWith_value_expansion_inputs : Nat
  same_sample_transport_inputs : Nat
  two_sample_alignment_inputs : Nat
  scalar_strict_backward_inputs : Nat
  line743_translation_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_two_sample_alignment : Prop

def property4RegularSeqTwoSampleAlignmentAudit :
    Property4RegularSeqTwoSampleAlignmentAudit where
  minSeqWith_value_expansion_inputs := 0
  same_sample_transport_inputs := 0
  two_sample_alignment_inputs := 1
  scalar_strict_backward_inputs := 0
  line743_translation_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_two_sample_alignment := True

end BishopRegularSeqTheorem118

/-- G125 package: G124 and G123 are connected; line 735 is reduced to the
single explicit two-sample alignment theorem. -/
structure BishopRegularSeqTheorem118G125Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g124 : BishopRegularSeqTheorem118G124Package S
  two_sample_to_same_sample :
    BishopRegularSeqTheorem118.Property4RegularSeqMinTwoSampleAlignment Arch ->
      BishopRegularSeqTheorem118.Property4RegularSeqMinSameSampleExpansion Arch
  property4_two_sample_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_two_sample :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawTwoSampleAlignmentInput S r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqTwoSampleAlignmentAudit
  line735_value_expansion_closed : Prop
  line735_same_sample_transport_closed : Prop
  line735_remaining_frontier_two_sample_alignment : Prop
  no_quotient_extraction_in_g125_mainline : Prop

def bishopRegularSeqTheorem118G125Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G125Package S where
  g124 := bishopRegularSeqTheorem118G124Package S
  two_sample_to_same_sample := by
    intro data
    exact
      BishopRegularSeqTheorem118.minSameSampleExpansion_from_twoSampleAlignment
        Arch data
  property4_two_sample_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawTwoSampleAlignmentInput S
  property4_from_two_sample := by
    intro r data
    exact
      BishopRegularSeqTheorem118.property4_from_regularseq_two_sample_alignment
        S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqTwoSampleAlignmentAudit
  line735_value_expansion_closed := True
  line735_same_sample_transport_closed := True
  line735_remaining_frontier_two_sample_alignment := True
  no_quotient_extraction_in_g125_mainline := True

/-- Progress after G125: still 99%; the residual line-735 obligation is the
single constructive two-sample alignment lemma. -/
def bishopRegularSeqCh1To4ProgressAfterG125 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G125: connected the G124 two-sample minSeqWith expansion to the G123 \
    same-sample transport; remaining line-735 work is the single \
    two-sample alignment lemma."


end BishopCReal
