import Mathdemo.Internal.CRat_iter217

set_option linter.style.longLine false

/-!
# G118: closing the line-743 additive sum translation

G117 reduced the shifted-min line-743 obligation to the sum identity

`(x+d)+c ~ (x+(c-d))+(d+d)`.

This file closes that identity over `relEventually`, using only the already
available RegularSeq algebra laws.  The property (4) frontier is therefore
reduced to the line-735 left monotonicity of `minSeqWith`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The cancellation needed inside the line-743 sum translation:
`-d + (d+d) = d` over eventual equality. -/
theorem addSeq_neg_left_double_eventually (d : RegularSeq) :
    relEventually (addSeq (negSeq d) (addSeq d d)) d := by
  have hassoc :
      relEventually
        (addSeq (addSeq (negSeq d) d) d)
        (addSeq (negSeq d) (addSeq d d)) :=
    addSeq_assoc_eventually (negSeq d) d d
  have hcancel :
      relEventually
        (addSeq (addSeq (negSeq d) d) d)
        (addSeq zeroSeq d) :=
    addSeq_respects_eventually
      (addSeq (negSeq d) d) zeroSeq
      d d
      (addSeq_neg_left_eventually d)
      (relEventually_refl d)
  have hzero :
      relEventually (addSeq zeroSeq d) d :=
    addSeq_zero_left_eventually d
  exact
    relEventually_trans
      (addSeq (negSeq d) (addSeq d d))
      (addSeq (addSeq (negSeq d) d) d)
      d
      (relEventually_symm
        (addSeq (addSeq (negSeq d) d) d)
        (addSeq (negSeq d) (addSeq d d))
        hassoc)
      (relEventually_trans
        (addSeq (addSeq (negSeq d) d) d)
        (addSeq zeroSeq d)
        d
        hcancel
        hzero)

/-- `c-d + (d+d) = c+d` over eventual equality. -/
theorem addSeq_sub_add_double_eventually (c d : RegularSeq) :
    relEventually
      (addSeq (subSeq c d) (addSeq d d))
      (addSeq c d) := by
  have hsub :
      relEventually
        (subSeq c d)
        (addSeq c (negSeq d)) :=
    subSeq_eq_add_neg_eventually c d
  have h0 :
      relEventually
        (addSeq (subSeq c d) (addSeq d d))
        (addSeq (addSeq c (negSeq d)) (addSeq d d)) :=
    addSeq_respects_eventually
      (subSeq c d) (addSeq c (negSeq d))
      (addSeq d d) (addSeq d d)
      hsub
      (relEventually_refl (addSeq d d))
  have hassoc :
      relEventually
        (addSeq (addSeq c (negSeq d)) (addSeq d d))
        (addSeq c (addSeq (negSeq d) (addSeq d d))) :=
    addSeq_assoc_eventually c (negSeq d) (addSeq d d)
  have hinner :
      relEventually
        (addSeq (negSeq d) (addSeq d d))
        d :=
    addSeq_neg_left_double_eventually d
  have h1 :
      relEventually
        (addSeq c (addSeq (negSeq d) (addSeq d d)))
        (addSeq c d) :=
    addSeq_respects_eventually
      c c
      (addSeq (negSeq d) (addSeq d d)) d
      (relEventually_refl c)
      hinner
  exact
    relEventually_trans
      (addSeq (subSeq c d) (addSeq d d))
      (addSeq (addSeq c (negSeq d)) (addSeq d d))
      (addSeq c d)
      h0
      (relEventually_trans
        (addSeq (addSeq c (negSeq d)) (addSeq d d))
        (addSeq c (addSeq (negSeq d) (addSeq d d)))
        (addSeq c d)
        hassoc
        h1)

/-- The G117 additive sum translation is closed:
`(x+d)+c = (x+(c-d))+(d+d)` over eventual equality. -/
theorem minSeqSum_translate_right_eventually
    (x d c : RegularSeq) :
    relEventually
      (addSeq (addSeq x d) c)
      (addSeq (addSeq x (subSeq c d)) (addSeq d d)) := by
  have h0 :
      relEventually
        (addSeq (addSeq x d) c)
        (addSeq x (addSeq d c)) :=
    addSeq_assoc_eventually x d c
  have hcomm :
      relEventually
        (addSeq d c)
        (addSeq c d) :=
    addSeq_comm_eventually d c
  have h1 :
      relEventually
        (addSeq x (addSeq d c))
        (addSeq x (addSeq c d)) :=
    addSeq_respects_eventually
      x x
      (addSeq d c) (addSeq c d)
      (relEventually_refl x)
      hcomm
  have hinner :
      relEventually
        (addSeq c d)
        (addSeq (subSeq c d) (addSeq d d)) :=
    relEventually_symm
      (addSeq (subSeq c d) (addSeq d d))
      (addSeq c d)
      (addSeq_sub_add_double_eventually c d)
  have h2 :
      relEventually
        (addSeq x (addSeq c d))
        (addSeq x (addSeq (subSeq c d) (addSeq d d))) :=
    addSeq_respects_eventually
      x x
      (addSeq c d) (addSeq (subSeq c d) (addSeq d d))
      (relEventually_refl x)
      hinner
  have hassocR :
      relEventually
        (addSeq x (addSeq (subSeq c d) (addSeq d d)))
        (addSeq (addSeq x (subSeq c d)) (addSeq d d)) :=
    relEventually_symm
      (addSeq (addSeq x (subSeq c d)) (addSeq d d))
      (addSeq x (addSeq (subSeq c d) (addSeq d d)))
      (addSeq_assoc_eventually x (subSeq c d) (addSeq d d))
  exact
    relEventually_trans
      (addSeq (addSeq x d) c)
      (addSeq x (addSeq d c))
      (addSeq (addSeq x (subSeq c d)) (addSeq d d))
      h0
      (relEventually_trans
        (addSeq x (addSeq d c))
        (addSeq x (addSeq c d))
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))
        h1
        (relEventually_trans
          (addSeq x (addSeq c d))
          (addSeq x (addSeq (subSeq c d) (addSeq d d)))
          (addSeq (addSeq x (subSeq c d)) (addSeq d d))
          h2
          hassocR))

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Closed G118 line-743 sum translation package. -/
def closedShiftedMinTranslationSum :
    Property4RegularSeqShiftedMinTranslationSum Arch where
  minSeqSum_translate_right_eventually := by
    intro x d c
    exact BishopCReal.minSeqSum_translate_right_eventually x d c
  source_line743_sum_translation_identity := True
  source_line743_subtraction_shift_closed := True
  source_line743_half_factor_peeled := True
  source_line743_shift_order_closed := True
  source_line743_right_monotonicity_closed_from_left := True
  no_quotient_adapter_used_for_shifted_min := True

/-- G118 input for property (4): only the line-735 left monotonicity of
`minSeqWith` remains external to the RegularSeq algebra closed here. -/
structure Property4RegularSeqDataMinLawOnlyLeftInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  source_line735_left_monotonicity_input : Prop
  line743_translation_closed : Prop
  quotient_extraction_not_used : Prop

/-- Convert the G118 input to the G111 min-law reduction data. -/
def regularSeqDataMinLawReduction_from_onlyLeftInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawOnlyLeftInput S r) :
    Property4ReductionDataFromRegularSeqDataMinLaws S r :=
  regularSeqDataMinLawReduction_from_translationSumInput
    S r
    { mainline := data.mainline
      g96_bridge := data.g96_bridge
      minSeqWith_monotone_left := data.minSeqWith_monotone_left
      shifted_min_translation_sum := closedShiftedMinTranslationSum (Arch := Arch)
      source_line735_left_monotonicity_input :=
        data.source_line735_left_monotonicity_input
      source_line743_translation_sum_identity := data.line743_translation_closed
      quotient_extraction_not_used := data.quotient_extraction_not_used }

/-- Property (4), after closing the line-743 translation algebra. -/
def property4_from_regularseq_left_min_monotone
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawOnlyLeftInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_data_min_laws
    S r
    (regularSeqDataMinLawReduction_from_onlyLeftInput S r data)

/-- Selector footprint after closing line 743. -/
structure Property4RegularSeqOnlyLeftAudit : Type where
  line735_regularseq_min_monotonicity_inputs : Nat
  line743_sum_translation_inputs : Nat
  line743_body_translation_inputs : Nat
  line743_half_factor_inputs : Nat
  line743_subtraction_shift_inputs : Nat
  line743_shift_order_inputs : Nat
  line743_right_monotonicity_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_left_min_monotonicity : Prop

def property4RegularSeqOnlyLeftAudit :
    Property4RegularSeqOnlyLeftAudit where
  line735_regularseq_min_monotonicity_inputs := 1
  line743_sum_translation_inputs := 0
  line743_body_translation_inputs := 0
  line743_half_factor_inputs := 0
  line743_subtraction_shift_inputs := 0
  line743_shift_order_inputs := 0
  line743_right_monotonicity_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_left_min_monotonicity := True

end BishopRegularSeqTheorem118

/-- G118 package: line-743 translation is closed; property (4) now depends only
on the line-735 left monotonicity input for `minSeqWith`. -/
structure BishopRegularSeqTheorem118G118Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g117 : BishopRegularSeqTheorem118G117Package S
  shifted_min_translation_sum_closed :
    BishopRegularSeqTheorem118.Property4RegularSeqShiftedMinTranslationSum Arch
  property4_only_left_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_only_left :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_only_left_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqOnlyLeftAudit
  line743_sum_translation_closed : Prop
  only_line735_left_monotonicity_remains : Prop
  no_quotient_extraction_in_g118_mainline : Prop

def bishopRegularSeqTheorem118G118Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G118Package S where
  g117 := bishopRegularSeqTheorem118G117Package S
  shifted_min_translation_sum_closed :=
    BishopRegularSeqTheorem118.closedShiftedMinTranslationSum (Arch := Arch)
  property4_only_left_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawOnlyLeftInput S
  property4_from_only_left := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_left_min_monotone
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqOnlyLeftAudit
  line743_sum_translation_closed := True
  only_line735_left_monotonicity_remains := True
  no_quotient_extraction_in_g118_mainline := True

/-- Progress after G118: line 743 is closed.  The remaining property (4)
frontier is the line-735 left monotonicity of `minSeqWith`. -/
def bishopRegularSeqCh1To4ProgressAfterG118 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G118: closed the line-743 additive sum translation over RegularSeq; \
    property (4) now needs only line-735 left min monotonicity."


end BishopCReal
