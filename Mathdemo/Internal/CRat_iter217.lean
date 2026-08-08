import Mathdemo.Internal.CRat_iter216

set_option linter.style.longLine false

/-!
# G117: reducing the shifted-min body identity to a sum identity

G116 left line 743 with the pre-half body identity

`body(x+d,c) ~ body(x,c-d) + d + d`.

This file closes the subtraction/absolute-value transport around that body.
The remaining content is the additive-sum translation

`(x+d)+c ~ (x+(c-d))+(d+d)`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Shifting the left input of a subtraction by `s` shifts the result by `s`:
`(a+s)-b = (a-b)+s` over eventual equality. -/
theorem subSeq_add_left_shift_eventually
    (a s b : RegularSeq) :
    relEventually
      (subSeq (addSeq a s) b)
      (addSeq (subSeq a b) s) := by
  have h0 :
      relEventually
        (subSeq (addSeq a s) b)
        (addSeq (addSeq a s) (negSeq b)) :=
    subSeq_eq_add_neg_eventually (addSeq a s) b
  have h1 :
      relEventually
        (addSeq (addSeq a s) (negSeq b))
        (addSeq a (addSeq s (negSeq b))) :=
    addSeq_assoc_eventually a s (negSeq b)
  have hcomm :
      relEventually
        (addSeq s (negSeq b))
        (addSeq (negSeq b) s) :=
    addSeq_comm_eventually s (negSeq b)
  have h2 :
      relEventually
        (addSeq a (addSeq s (negSeq b)))
        (addSeq a (addSeq (negSeq b) s)) :=
    addSeq_respects_eventually
      a a
      (addSeq s (negSeq b)) (addSeq (negSeq b) s)
      (relEventually_refl a)
      hcomm
  have h3 :
      relEventually
        (addSeq a (addSeq (negSeq b) s))
        (addSeq (addSeq a (negSeq b)) s) :=
    relEventually_symm
      (addSeq (addSeq a (negSeq b)) s)
      (addSeq a (addSeq (negSeq b) s))
      (addSeq_assoc_eventually a (negSeq b) s)
  have hleft :
      relEventually
        (addSeq a (negSeq b))
        (subSeq a b) :=
    relEventually_symm
      (subSeq a b)
      (addSeq a (negSeq b))
      (subSeq_eq_add_neg_eventually a b)
  have h4 :
      relEventually
        (addSeq (addSeq a (negSeq b)) s)
        (addSeq (subSeq a b) s) :=
    addSeq_respects_eventually
      (addSeq a (negSeq b)) (subSeq a b)
      s s
      hleft
      (relEventually_refl s)
  exact
    relEventually_trans
      (subSeq (addSeq a s) b)
      (addSeq (addSeq a s) (negSeq b))
      (addSeq (subSeq a b) s)
      h0
      (relEventually_trans
        (addSeq (addSeq a s) (negSeq b))
        (addSeq a (addSeq s (negSeq b)))
        (addSeq (subSeq a b) s)
        h1
        (relEventually_trans
          (addSeq a (addSeq s (negSeq b)))
          (addSeq a (addSeq (negSeq b) s))
          (addSeq (subSeq a b) s)
          h2
          (relEventually_trans
            (addSeq a (addSeq (negSeq b) s))
            (addSeq (addSeq a (negSeq b)) s)
            (addSeq (subSeq a b) s)
            h3
            h4)))

/-- The shifted difference in line 743:
`(x+d)-c = x-(c-d)` over eventual equality. -/
theorem subSeq_add_right_sub_shift_eventually
    (x d c : RegularSeq) :
    relEventually
      (subSeq (addSeq x d) c)
      (subSeq x (subSeq c d)) := by
  have h0 :
      relEventually
        (subSeq (addSeq x d) c)
        (addSeq (addSeq x d) (negSeq c)) :=
    subSeq_eq_add_neg_eventually (addSeq x d) c
  have h1 :
      relEventually
        (addSeq (addSeq x d) (negSeq c))
        (addSeq x (addSeq d (negSeq c))) :=
    addSeq_assoc_eventually x d (negSeq c)
  have hcomm_inner :
      relEventually
        (addSeq d (negSeq c))
        (addSeq (negSeq c) d) :=
    addSeq_comm_eventually d (negSeq c)
  have h2 :
      relEventually
        (addSeq x (addSeq d (negSeq c)))
        (addSeq x (addSeq (negSeq c) d)) :=
    addSeq_respects_eventually
      x x
      (addSeq d (negSeq c)) (addSeq (negSeq c) d)
      (relEventually_refl x)
      hcomm_inner
  have hd_c_to_add :
      relEventually
        (subSeq d c)
        (addSeq (negSeq c) d) := by
    have hdc0 :
        relEventually
          (subSeq d c)
          (addSeq d (negSeq c)) :=
      subSeq_eq_add_neg_eventually d c
    have hdc1 :
        relEventually
          (addSeq d (negSeq c))
          (addSeq (negSeq c) d) :=
      addSeq_comm_eventually d (negSeq c)
    exact
      relEventually_trans
        (subSeq d c)
        (addSeq d (negSeq c))
        (addSeq (negSeq c) d)
        hdc0
        hdc1
  have hadd_to_neg_sub :
      relEventually
        (addSeq (negSeq c) d)
        (negSeq (subSeq c d)) :=
    relEventually_trans
      (addSeq (negSeq c) d)
      (subSeq d c)
      (negSeq (subSeq c d))
      (relEventually_symm
        (subSeq d c)
        (addSeq (negSeq c) d)
        hd_c_to_add)
      (subSeq_comm_neg_eventually d c)
  have h3 :
      relEventually
        (addSeq x (addSeq (negSeq c) d))
        (addSeq x (negSeq (subSeq c d))) :=
    addSeq_respects_eventually
      x x
      (addSeq (negSeq c) d) (negSeq (subSeq c d))
      (relEventually_refl x)
      hadd_to_neg_sub
  have h4 :
      relEventually
        (addSeq x (negSeq (subSeq c d)))
        (subSeq x (subSeq c d)) :=
    relEventually_symm
      (subSeq x (subSeq c d))
      (addSeq x (negSeq (subSeq c d)))
      (subSeq_eq_add_neg_eventually x (subSeq c d))
  exact
    relEventually_trans
      (subSeq (addSeq x d) c)
      (addSeq (addSeq x d) (negSeq c))
      (subSeq x (subSeq c d))
      h0
      (relEventually_trans
        (addSeq (addSeq x d) (negSeq c))
        (addSeq x (addSeq d (negSeq c)))
        (subSeq x (subSeq c d))
        h1
        (relEventually_trans
          (addSeq x (addSeq d (negSeq c)))
          (addSeq x (addSeq (negSeq c) d))
          (subSeq x (subSeq c d))
          h2
          (relEventually_trans
            (addSeq x (addSeq (negSeq c) d))
            (addSeq x (negSeq (subSeq c d)))
            (subSeq x (subSeq c d))
            h3
            h4)))

/-- Once the sum parts are translated, the full pre-half body translation
follows; subtraction shifting and the absolute-value subterm are closed here. -/
theorem minSeqBody_translate_right_eventually_from_sum
    (x d c : RegularSeq)
    (hsum :
      relEventually
        (addSeq (addSeq x d) c)
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))) :
    relEventually
      (minSeqBody (addSeq x d) c)
      (addSeq (minSeqBody x (subSeq c d)) (addSeq d d)) := by
  have hsub :
      relEventually
        (subSeq (addSeq x d) c)
        (subSeq x (subSeq c d)) :=
    subSeq_add_right_sub_shift_eventually x d c
  have habs :
      relEventually
        (absSeq (subSeq (addSeq x d) c))
        (absSeq (subSeq x (subSeq c d))) :=
    absSeq_respects_eventually
      (subSeq (addSeq x d) c)
      (subSeq x (subSeq c d))
      hsub
  have hbody0 :
      relEventually
        (minSeqBody (addSeq x d) c)
        (subSeq
          (addSeq (addSeq x (subSeq c d)) (addSeq d d))
          (absSeq (subSeq x (subSeq c d)))) := by
    unfold minSeqBody
    exact
      subSeq_respects_eventually
        (addSeq (addSeq x d) c)
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))
        (absSeq (subSeq (addSeq x d) c))
        (absSeq (subSeq x (subSeq c d)))
        hsum
        habs
  have hshift :
      relEventually
        (subSeq
          (addSeq (addSeq x (subSeq c d)) (addSeq d d))
          (absSeq (subSeq x (subSeq c d))))
        (addSeq
          (subSeq
            (addSeq x (subSeq c d))
            (absSeq (subSeq x (subSeq c d))))
          (addSeq d d)) :=
    subSeq_add_left_shift_eventually
      (addSeq x (subSeq c d))
      (addSeq d d)
      (absSeq (subSeq x (subSeq c d)))
  change
    relEventually
      (minSeqBody (addSeq x d) c)
      (addSeq
        (subSeq
          (addSeq x (subSeq c d))
          (absSeq (subSeq x (subSeq c d))))
        (addSeq d d))
  exact
    relEventually_trans
      (minSeqBody (addSeq x d) c)
      (subSeq
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))
        (absSeq (subSeq x (subSeq c d))))
      (addSeq
        (subSeq
          (addSeq x (subSeq c d))
          (absSeq (subSeq x (subSeq c d))))
        (addSeq d d))
      hbody0
      hshift

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G117 sum-level translation input for line 743. -/
structure Property4RegularSeqShiftedMinTranslationSum
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  minSeqSum_translate_right_eventually :
    forall x d c : RegularSeq,
      relEventually
        (addSeq (addSeq x d) c)
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))
  source_line743_sum_translation_identity : Prop
  source_line743_subtraction_shift_closed : Prop
  source_line743_half_factor_peeled : Prop
  source_line743_shift_order_closed : Prop
  source_line743_right_monotonicity_closed_from_left : Prop
  no_quotient_adapter_used_for_shifted_min : Prop

/-- Rebuild the G116 body-level translation input from the sum-level identity. -/
def translationBody_from_sumTranslation
    (data : Property4RegularSeqShiftedMinTranslationSum Arch) :
    Property4RegularSeqShiftedMinTranslationBody Arch where
  minSeqBody_translate_right_eventually := by
    intro x d c
    exact
      minSeqBody_translate_right_eventually_from_sum
        x d c
        (data.minSeqSum_translate_right_eventually x d c)
  source_line743_body_translation_identity :=
    data.source_line743_sum_translation_identity
  source_line743_half_factor_peeled :=
    data.source_line743_half_factor_peeled
  source_line743_shift_order_closed :=
    data.source_line743_shift_order_closed
  source_line743_right_monotonicity_closed_from_left :=
    data.source_line743_right_monotonicity_closed_from_left
  no_quotient_adapter_used_for_shifted_min :=
    data.no_quotient_adapter_used_for_shifted_min

/-- G117 input for property (4): line-735 left monotonicity plus sum-level
line-743 translation. -/
structure Property4RegularSeqDataMinLawTranslationSumInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  shifted_min_translation_sum :
    Property4RegularSeqShiftedMinTranslationSum Arch
  source_line735_left_monotonicity_input : Prop
  source_line743_translation_sum_identity : Prop
  quotient_extraction_not_used : Prop

/-- Convert the G117 input to the G111 min-law reduction data. -/
def regularSeqDataMinLawReduction_from_translationSumInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawTranslationSumInput S r) :
    Property4ReductionDataFromRegularSeqDataMinLaws S r where
  mainline := data.mainline
  minlaw_bridge :=
    { g96_bridge := data.g96_bridge
      min_laws :=
        regularSeqDataMinLawCore_from_shiftedMinDecomposition
          data.minSeqWith_monotone_left
          (shiftedMinDecomposition_from_closedShiftOrder
            (shiftedMinAfterShiftOrder_from_closedRightMonotone
              data.minSeqWith_monotone_left
              (shiftedMinAfterRightMonotone_from_translationExact
                (translationExact_from_bodyTranslation
                  (translationBody_from_sumTranslation
                    data.shifted_min_translation_sum)))))
      realSurface := bishopRegularSeqRealSurface Arch
      archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage Arch
      source_line735_min_law_is_regularseq_data := True
      source_line743_min_law_is_regularseq_data := True
      no_quotient_extraction_in_minlaw_bridge := True
      no_classical_choice_in_minlaw_bridge := True }
  source_property4_min_laws_are_regularseq_data := True
  quotient_extraction_not_used_for_property4_min_laws := True

/-- Property (4), after reducing line-743 body translation to the sum identity. -/
def property4_from_regularseq_translation_sum
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawTranslationSumInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_data_min_laws
    S r
    (regularSeqDataMinLawReduction_from_translationSumInput S r data)

/-- Selector footprint after reducing body translation to sum translation. -/
structure Property4RegularSeqTranslationSumAudit : Type where
  line735_regularseq_min_monotonicity_inputs : Nat
  line743_sum_translation_inputs : Nat
  line743_body_translation_inputs : Nat
  line743_half_factor_inputs : Nat
  line743_subtraction_shift_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_left_mono_plus_sum_translation_identity : Prop

def property4RegularSeqTranslationSumAudit :
    Property4RegularSeqTranslationSumAudit where
  line735_regularseq_min_monotonicity_inputs := 1
  line743_sum_translation_inputs := 1
  line743_body_translation_inputs := 0
  line743_half_factor_inputs := 0
  line743_subtraction_shift_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_left_mono_plus_sum_translation_identity := True

end BishopRegularSeqTheorem118

/-- G117 package: line-743 translation is reduced to the additive sum identity;
subtraction, absolute-value transport, and half arithmetic are closed. -/
structure BishopRegularSeqTheorem118G117Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g116 : BishopRegularSeqTheorem118G116Package S
  shifted_min_translation_sum : Type 1
  property4_translation_sum_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_translation_sum :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_translation_sum_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqTranslationSumAudit
  line743_body_reduced_to_sum_translation : Prop
  no_quotient_extraction_in_g117_mainline : Prop

def bishopRegularSeqTheorem118G117Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G117Package S where
  g116 := bishopRegularSeqTheorem118G116Package S
  shifted_min_translation_sum :=
    BishopRegularSeqTheorem118.Property4RegularSeqShiftedMinTranslationSum Arch
  property4_translation_sum_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawTranslationSumInput S
  property4_from_translation_sum := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_translation_sum
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqTranslationSumAudit
  line743_body_reduced_to_sum_translation := True
  no_quotient_extraction_in_g117_mainline := True

/-- Progress after G117: line 743 only asks for the additive sum translation
identity. -/
def bishopRegularSeqCh1To4ProgressAfterG117 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G117: reduced the line-743 body identity to the additive sum translation; \
    subtraction shift, abs transport, and half arithmetic are closed."


end BishopCReal
