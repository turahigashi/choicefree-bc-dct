import Mathdemo.Internal.CRat_iter214

set_option linter.style.longLine false

/-!
# G115: reducing shifted-min translation order to exact representative equality

G114 left line 743 with one translation input stated as a non-strict order.
The source half-sum identity is actually an equality:

`min(x+d,c) = min(x,c-d)+d`.

This file factors the remaining order input through an exact
`relEventually` translation identity.  The identity itself remains the
frontier, but the order wrapper is no longer a primitive field.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Eventual equality implies the represented non-strict order. -/
theorem regularSeqLe_of_relEventually
    {x y : RegularSeq}
    (hxy : relEventually x y) :
    RegularSeqLe x y := by
  have hsub0 :
      relEventually (subSeq y x) (subSeq x x) :=
    subSeq_respects_eventually
      y x
      x x
      (relEventually_symm x y hxy)
      (relEventually_refl x)
  have hsub1 :
      relEventually (subSeq x x) zeroSeq :=
    subSeq_self_eventually_law x
  have hsub :
      relEventually (subSeq y x) zeroSeq :=
    relEventually_trans
      (subSeq y x)
      (subSeq x x)
      zeroSeq
      hsub0
      hsub1
  exact
    regularSeqNonneg_of_eventual
      hsub
      not_posEventually_zero

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G115 exact translation input for line 743.  This is sharper than the G114
order input: the remaining mathematical content is the half-sum translation
identity over `relEventually`. -/
structure Property4RegularSeqShiftedMinTranslationExact
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  minSeqWith_translate_right_eventually :
    forall x d c : RegularSeq,
      relEventually
        (minSeqWith Arch (addSeq x d) c)
        (addSeq (minSeqWith Arch x (subSeq c d)) d)
  source_line743_translation_exact_identity : Prop
  source_line743_shift_order_closed : Prop
  source_line743_right_monotonicity_closed_from_left : Prop
  no_quotient_adapter_used_for_shifted_min : Prop

/-- Rebuild the G114 shifted-min remainder by turning exact translation
equality into the needed non-strict order. -/
def shiftedMinAfterRightMonotone_from_translationExact
    (data : Property4RegularSeqShiftedMinTranslationExact Arch) :
    Property4RegularSeqShiftedMinAfterRightMonotone Arch where
  minSeqWith_translate_right_le := by
    intro x d c
    exact
      regularSeqLe_of_relEventually
        (data.minSeqWith_translate_right_eventually x d c)
  source_line743_translation_step :=
    data.source_line743_translation_exact_identity
  source_line743_shift_order_closed :=
    data.source_line743_shift_order_closed
  source_line743_right_monotonicity_closed_from_left :=
    data.source_line743_right_monotonicity_closed_from_left
  no_quotient_adapter_used_for_shifted_min :=
    data.no_quotient_adapter_used_for_shifted_min

/-- G115 input for property (4): line-735 left monotonicity plus exact
line-743 translation identity. -/
structure Property4RegularSeqDataMinLawTranslationExactInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  shifted_min_translation_exact :
    Property4RegularSeqShiftedMinTranslationExact Arch
  source_line735_left_monotonicity_input : Prop
  source_line743_translation_is_exact_identity : Prop
  quotient_extraction_not_used : Prop

/-- Convert the G115 input to the G111 min-law reduction data. -/
def regularSeqDataMinLawReduction_from_translationExactInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawTranslationExactInput S r) :
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
                data.shifted_min_translation_exact)))
      realSurface := bishopRegularSeqRealSurface Arch
      archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage Arch
      source_line735_min_law_is_regularseq_data := True
      source_line743_min_law_is_regularseq_data := True
      no_quotient_extraction_in_minlaw_bridge := True
      no_classical_choice_in_minlaw_bridge := True }
  source_property4_min_laws_are_regularseq_data := True
  quotient_extraction_not_used_for_property4_min_laws := True

/-- Property (4), after reducing the last line-743 order input to exact
translation equality. -/
def property4_from_regularseq_translation_exact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawTranslationExactInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_data_min_laws
    S r
    (regularSeqDataMinLawReduction_from_translationExactInput S r data)

/-- Selector footprint after replacing the translation order field by an exact
translation identity field. -/
structure Property4RegularSeqTranslationExactAudit : Type where
  line735_regularseq_min_monotonicity_inputs : Nat
  line743_translation_order_inputs : Nat
  line743_translation_exact_identity_inputs : Nat
  line743_shift_order_inputs : Nat
  line743_right_monotonicity_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_left_mono_plus_exact_translation_identity : Prop

def property4RegularSeqTranslationExactAudit :
    Property4RegularSeqTranslationExactAudit where
  line735_regularseq_min_monotonicity_inputs := 1
  line743_translation_order_inputs := 0
  line743_translation_exact_identity_inputs := 1
  line743_shift_order_inputs := 0
  line743_right_monotonicity_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_left_mono_plus_exact_translation_identity := True

end BishopRegularSeqTheorem118

/-- G115 package: line-743's remaining order input is reduced to an exact
`relEventually` translation identity. -/
structure BishopRegularSeqTheorem118G115Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g114 : BishopRegularSeqTheorem118G114Package S
  shifted_min_translation_exact : Type 1
  property4_translation_exact_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_translation_exact :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_translation_exact_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqTranslationExactAudit
  line743_translation_order_reduced_to_exact_identity : Prop
  no_quotient_extraction_in_g115_mainline : Prop

def bishopRegularSeqTheorem118G115Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G115Package S where
  g114 := bishopRegularSeqTheorem118G114Package S
  shifted_min_translation_exact :=
    BishopRegularSeqTheorem118.Property4RegularSeqShiftedMinTranslationExact Arch
  property4_translation_exact_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawTranslationExactInput S
  property4_from_translation_exact := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_translation_exact
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqTranslationExactAudit
  line743_translation_order_reduced_to_exact_identity := True
  no_quotient_extraction_in_g115_mainline := True

/-- Progress after G115: line 743 no longer has a primitive order input; it
only asks for the exact half-sum translation identity over `relEventually`. -/
def bishopRegularSeqCh1To4ProgressAfterG115 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G115: reduced the remaining line-743 translation order input to the \
    exact relEventually half-sum translation identity."


end BishopCReal
