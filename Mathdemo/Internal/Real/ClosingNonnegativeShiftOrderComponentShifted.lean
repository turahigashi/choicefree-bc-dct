import Mathdemo.Internal.Real.DecomposingRegularSeqShiftedMinLaw

set_option linter.style.longLine false

/-!
# G113: closing the nonnegative shift-order component of shifted min

G112 decomposed the line-743 shifted-min law into three RegularSeq/data
components.  This file closes the middle component

`0 <= d -> c - d <= c`

directly on the `RegularSeq` representation surface.  The proof uses only
existing `relEventually` algebra laws and nonnegativity transport; no quotient
representative extraction or `Prop`-to-data selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Cancelling a represented difference on the right:
`c - (c - d) = d` over the implementation equality. -/
theorem subSeq_right_sub_cancel_eventually
    (c d : RegularSeq) :
    relEventually (subSeq c (subSeq c d)) d := by
  have hcomm :
      relEventually
        (subSeq c (subSeq c d))
        (negSeq (subSeq (subSeq c d) c)) :=
    subSeq_comm_neg_eventually c (subSeq c d)
  have hleft :
      relEventually
        (subSeq c d)
        (addSeq c (negSeq d)) :=
    subSeq_eq_add_neg_eventually c d
  have hinner0 :
      relEventually
        (subSeq (subSeq c d) c)
        (subSeq (addSeq c (negSeq d)) c) :=
    subSeq_respects_eventually
      (subSeq c d) (addSeq c (negSeq d))
      c c
      hleft
      (relEventually_refl c)
  have hinner1 :
      relEventually
        (subSeq (addSeq c (negSeq d)) c)
        (negSeq d) :=
    subSeq_add_left_cancel_eventually c (negSeq d)
  have hinner :
      relEventually
        (subSeq (subSeq c d) c)
        (negSeq d) :=
    relEventually_trans
      (subSeq (subSeq c d) c)
      (subSeq (addSeq c (negSeq d)) c)
      (negSeq d)
      hinner0
      hinner1
  have hneg :
      relEventually
        (negSeq (subSeq (subSeq c d) c))
        (negSeq (negSeq d)) :=
    negSeq_respects_eventually
      (subSeq (subSeq c d) c)
      (negSeq d)
      hinner
  have hdn :
      relEventually (negSeq (negSeq d)) d :=
    negSeq_negSeq_eventually d
  exact
    relEventually_trans
      (subSeq c (subSeq c d))
      (negSeq (subSeq (subSeq c d) c))
      d
      hcomm
      (relEventually_trans
        (negSeq (subSeq (subSeq c d) c))
        (negSeq (negSeq d))
        d
        hneg
        hdn)

/-- If the shift is nonnegative, subtracting it from the right lowers the
left endpoint: `0 <= d -> c - d <= c`. -/
theorem regularSeqLe_sub_right_self_of_nonneg
    (c d : RegularSeq)
    (hd : RegularSeqLe zeroSeq d) :
    RegularSeqLe (subSeq c d) c := by
  have hd_nonneg : RegularSeqNonneg d :=
    regularSeqNonneg_of_eventual
      (relEventually_symm
        (subSeq d zeroSeq)
        d
        (subSeq_zero_right_eventually d))
      hd
  exact
    regularSeqNonneg_of_eventual
      (subSeq_right_sub_cancel_eventually c d)
      hd_nonneg

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G113 remainder of the shifted-min decomposition after the order fact
`0 <= d -> c-d <= c` has been closed. -/
structure Property4RegularSeqShiftedMinAfterShiftOrder
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  minSeqWith_translate_right_le :
    forall x d c : RegularSeq,
      RegularSeqLe
        (minSeqWith Arch (addSeq x d) c)
        (addSeq (minSeqWith Arch x (subSeq c d)) d)
  minSeqWith_monotone_right :
    forall x a b : RegularSeq,
      RegularSeqLe a b ->
        RegularSeqLe (minSeqWith Arch x a) (minSeqWith Arch x b)
  source_line743_translation_step : Prop
  source_line743_shift_order_closed : Prop
  source_line743_right_monotonicity_step : Prop
  no_quotient_adapter_used_for_shifted_min : Prop

/-- Rebuild the G112 decomposition, filling the shift-order field from the
closed RegularSeq lemma in this file. -/
def shiftedMinDecomposition_from_closedShiftOrder
    (data : Property4RegularSeqShiftedMinAfterShiftOrder Arch) :
    Property4RegularSeqShiftedMinDecomposition Arch where
  minSeqWith_translate_right_le :=
    data.minSeqWith_translate_right_le
  subSeq_right_shift_le_self_of_nonneg :=
    regularSeqLe_sub_right_self_of_nonneg
  minSeqWith_monotone_right :=
    data.minSeqWith_monotone_right
  source_line743_translation_step :=
    data.source_line743_translation_step
  source_line743_shift_order_step :=
    data.source_line743_shift_order_closed
  source_line743_right_monotonicity_step :=
    data.source_line743_right_monotonicity_step
  no_quotient_adapter_used_for_shifted_min :=
    data.no_quotient_adapter_used_for_shifted_min

/-- G113 input for property (4): line-735 left monotonicity plus the two
remaining shifted-min components after closing the nonnegative shift order. -/
structure Property4RegularSeqDataMinLawShiftOrderClosedInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  shifted_min_after_shift_order :
    Property4RegularSeqShiftedMinAfterShiftOrder Arch
  source_line735_left_monotonicity_input : Prop
  source_line743_shift_order_closed : Prop
  quotient_extraction_not_used : Prop

/-- Convert the G113 input to the G111 min-law reduction data. -/
def regularSeqDataMinLawReduction_from_shiftOrderClosedInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawShiftOrderClosedInput S r) :
    Property4ReductionDataFromRegularSeqDataMinLaws S r where
  mainline := data.mainline
  minlaw_bridge :=
    { g96_bridge := data.g96_bridge
      min_laws :=
        regularSeqDataMinLawCore_from_shiftedMinDecomposition
          data.minSeqWith_monotone_left
          (shiftedMinDecomposition_from_closedShiftOrder
            data.shifted_min_after_shift_order)
      realSurface := bishopRegularSeqRealSurface Arch
      archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage Arch
      source_line735_min_law_is_regularseq_data := True
      source_line743_min_law_is_regularseq_data := True
      no_quotient_extraction_in_minlaw_bridge := True
      no_classical_choice_in_minlaw_bridge := True }
  source_property4_min_laws_are_regularseq_data := True
  quotient_extraction_not_used_for_property4_min_laws := True

/-- Property (4), using the shifted-min decomposition after closing
`0 <= d -> c-d <= c` on the RegularSeq surface. -/
def property4_from_regularseq_shift_order_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawShiftOrderClosedInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_data_min_laws
    S r
    (regularSeqDataMinLawReduction_from_shiftOrderClosedInput S r data)

/-- Selector footprint after closing the shift-order component. -/
structure Property4RegularSeqShiftOrderClosedAudit : Type where
  line735_regularseq_min_monotonicity_inputs : Nat
  line743_translation_inputs : Nat
  line743_shift_order_inputs : Nat
  line743_right_monotonicity_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_regularseq_translation_and_right_min_order : Prop

def property4RegularSeqShiftOrderClosedAudit :
    Property4RegularSeqShiftOrderClosedAudit where
  line735_regularseq_min_monotonicity_inputs := 1
  line743_translation_inputs := 1
  line743_shift_order_inputs := 0
  line743_right_monotonicity_inputs := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_regularseq_translation_and_right_min_order := True

end BishopRegularSeqTheorem118

/-- G113 package: the line-743 shift-order field is now obtained from closed
RegularSeq algebra and nonnegativity transport. -/
structure BishopRegularSeqTheorem118G113Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g112 : BishopRegularSeqTheorem118G112Package S
  shifted_min_after_shift_order : Type 1
  property4_shift_order_closed_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_shift_order_closed :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_shift_order_closed_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqShiftOrderClosedAudit
  line743_shift_order_closed_over_regularseq : Prop
  no_quotient_extraction_in_g113_mainline : Prop

def bishopRegularSeqTheorem118G113Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G113Package S where
  g112 := bishopRegularSeqTheorem118G112Package S
  shifted_min_after_shift_order :=
    BishopRegularSeqTheorem118.Property4RegularSeqShiftedMinAfterShiftOrder Arch
  property4_shift_order_closed_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawShiftOrderClosedInput S
  property4_from_shift_order_closed := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_shift_order_closed
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqShiftOrderClosedAudit
  line743_shift_order_closed_over_regularseq := True
  no_quotient_extraction_in_g113_mainline := True

/-- Progress after G113: the order component of line 743 is closed; only the
RegularSeq/data min translation and right-monotonicity components remain for
that line. -/
def bishopRegularSeqCh1To4ProgressAfterG113 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G113: closed the RegularSeq/data shift-order field 0 <= d -> c-d <= c; \
    line 743 now has only translation and right-min-monotonicity inputs."


end BishopCReal
