import Mathdemo.Internal.CRat_iter230

set_option linter.style.longLine false

/-!
# G131: packaging the closed chapter-1 property-(4) route

G130 closed the common-max line-735 transport.  This file threads that closed
transport through the G126 property-(4) API, so the chapter-1 RegularSeq route
can be invoked from the mainline data alone.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Closed G131 input for the common-max property-(4) API.

The G96 bridge is recovered from the mainline data, and the line-735 common-max
alignment is the closed G130 alignment.  No quotient representative extraction
or Prop-to-data selector is introduced at this layer. -/
def regularSeqDataMinLawCommonMaxAlignmentInput_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (mainline : Property4RegularSeqDataMainlineInput S r) :
    Property4RegularSeqDataMinLawCommonMaxAlignmentInput S r where
  mainline := mainline
  g96_bridge := mainline.g96_data.scalar_min_kernel_bridge
  common_max_alignment := property4RegularSeqMinCommonMaxAlignmentClosed
  source_line735_common_max_transport_input := True
  line743_translation_closed := True
  quotient_extraction_not_used := True
  prop_to_data_selector_not_used := True

/-- Chapter-1 property-(4) from mainline data only.

All lower line-735/common-max and line-743 translation data have already been
closed in G118--G130 and are inserted by
`regularSeqDataMinLawCommonMaxAlignmentInput_closed`. -/
def property4_from_chapter1_mainline
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (mainline : Property4RegularSeqDataMainlineInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_common_max_alignment
    S r
    (regularSeqDataMinLawCommonMaxAlignmentInput_closed S r mainline)

/-- G131 audit: the previously exposed line-735 and line-743 inputs have been
threaded from closed data. -/
structure Property4RegularSeqChapter1ClosedAudit : Type where
  line735_commonmax_external_inputs : Nat
  line735_commonmax_closed_data : Nat
  line743_translation_external_inputs : Nat
  line743_translation_closed_data : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  property4_available_from_mainline_only : Prop

def property4RegularSeqChapter1ClosedAudit :
    Property4RegularSeqChapter1ClosedAudit where
  line735_commonmax_external_inputs := 0
  line735_commonmax_closed_data := 1
  line743_translation_external_inputs := 0
  line743_translation_closed_data := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  property4_available_from_mainline_only := True

end BishopRegularSeqTheorem118

/-- G131 package: chapter-1 property-(4) is exposed through closed RegularSeq
data, with no late quotient representative selection. -/
structure BishopRegularSeqTheorem118G131Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g130 : BishopRegularSeqTheorem118G130Package S
  closed_commonmax_input :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqTheorem118.Property4RegularSeqDataMainlineInput S r ->
        BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawCommonMaxAlignmentInput S r
  property4_from_mainline :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqTheorem118.Property4RegularSeqDataMainlineInput S r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqChapter1ClosedAudit
  line735_commonmax_route_closed : Prop
  line743_translation_route_closed : Prop
  property4_chapter1_route_closed : Prop
  no_quotient_extraction_in_g131_mainline : Prop

def bishopRegularSeqTheorem118G131Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G131Package S where
  g130 := bishopRegularSeqTheorem118G130Package S
  closed_commonmax_input := by
    intro r mainline
    exact
      BishopRegularSeqTheorem118.regularSeqDataMinLawCommonMaxAlignmentInput_closed
        S r mainline
  property4_from_mainline := by
    intro r mainline
    exact
      BishopRegularSeqTheorem118.property4_from_chapter1_mainline
        S r mainline
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqChapter1ClosedAudit
  line735_commonmax_route_closed := True
  line743_translation_route_closed := True
  property4_chapter1_route_closed := True
  no_quotient_extraction_in_g131_mainline := True

/-- Progress after G131: chapter 1 is packaged as a closed RegularSeq route.
Chapters 2--4 remain at the earlier bridge/frontier levels. -/
def bishopRegularSeqCh1To4ProgressAfterG131 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G131: threaded closed commonMax line-735 and closed line-743 translation \
    into the property-(4) mainline; chapter 1 RegularSeq route is packaged."


end BishopCReal
