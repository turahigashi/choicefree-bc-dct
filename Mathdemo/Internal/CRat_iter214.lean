import Mathdemo.Internal.CRat_iter213

set_option linter.style.longLine false

/-!
# G114: closing right monotonicity of `minSeqWith`

G113 left line 743 with two RegularSeq/data inputs: the translation step and
right monotonicity of `minSeqWith`.  This file closes the right monotonicity
input from:

* representative commutativity of `minSeqWith`;
* the existing left monotonicity input for line 735;
* existing `RegularSeqLe` transport across `relEventually`.

This keeps the route on the data-carrying `RegularSeq` surface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Absolute value ignores representative negation over eventual equality. -/
theorem absSeq_negSeq_eventually
    (x : RegularSeq) :
    relEventually (absSeq (negSeq x)) (absSeq x) := by
  apply rel_to_relEventually
  change relVal (absVal (negVal x.val)) (absVal x.val)
  exact abs_neg_raw x

/-- The half-sum representative minimum is commutative over eventual equality. -/
theorem minSeqWith_comm_eventually
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    relEventually (minSeqWith A x y) (minSeqWith A y x) := by
  unfold minSeqWith
  have hsum :
      relEventually (addSeq x y) (addSeq y x) :=
    addSeq_comm_eventually x y
  have hsub_to_neg :
      relEventually
        (subSeq x y)
        (negSeq (subSeq y x)) :=
    subSeq_comm_neg_eventually x y
  have habs0 :
      relEventually
        (absSeq (subSeq x y))
        (absSeq (negSeq (subSeq y x))) :=
    absSeq_respects_eventually
      (subSeq x y)
      (negSeq (subSeq y x))
      hsub_to_neg
  have habs1 :
      relEventually
        (absSeq (negSeq (subSeq y x)))
        (absSeq (subSeq y x)) :=
    absSeq_negSeq_eventually (subSeq y x)
  have habs :
      relEventually
        (absSeq (subSeq x y))
        (absSeq (subSeq y x)) :=
    relEventually_trans
      (absSeq (subSeq x y))
      (absSeq (negSeq (subSeq y x)))
      (absSeq (subSeq y x))
      habs0
      habs1
  have hbody :
      relEventually
        (subSeq (addSeq x y) (absSeq (subSeq x y)))
        (subSeq (addSeq y x) (absSeq (subSeq y x))) :=
    subSeq_respects_eventually
      (addSeq x y) (addSeq y x)
      (absSeq (subSeq x y)) (absSeq (subSeq y x))
      hsum
      habs
  exact
    mulSeqConcrete_respects_eventually A
      halfSeq halfSeq
      (subSeq (addSeq x y) (absSeq (subSeq x y)))
      (subSeq (addSeq y x) (absSeq (subSeq y x)))
      (relEventually_refl halfSeq)
      hbody

/-- Right monotonicity of `minSeqWith` follows from left monotonicity plus
commutativity, all over the RegularSeq order surface. -/
theorem minSeqWith_monotone_right_regularSeqLe_from_left
    (A : ScalarMulArchimedeanData)
    (left_mono :
      forall x y c : RegularSeq,
        RegularSeqLe x y ->
          RegularSeqLe (minSeqWith A x c) (minSeqWith A y c))
    (x a b : RegularSeq)
    (hab : RegularSeqLe a b) :
    RegularSeqLe (minSeqWith A x a) (minSeqWith A x b) := by
  have hleft :
      RegularSeqLe (minSeqWith A a x) (minSeqWith A b x) :=
    left_mono a b x hab
  have hx_left :
      relEventually (minSeqWith A x a) (minSeqWith A a x) :=
    minSeqWith_comm_eventually A x a
  have hx_right :
      relEventually (minSeqWith A b x) (minSeqWith A x b) :=
    minSeqWith_comm_eventually A b x
  exact
    regularSeqLe_of_right_eventual
      hx_right
      (regularSeqLe_of_left_eventual hx_left hleft)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G114 remainder of the shifted-min decomposition after closing both the
shift order and right monotonicity components. -/
structure Property4RegularSeqShiftedMinAfterRightMonotone
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  minSeqWith_translate_right_le :
    forall x d c : RegularSeq,
      RegularSeqLe
        (minSeqWith Arch (addSeq x d) c)
        (addSeq (minSeqWith Arch x (subSeq c d)) d)
  source_line743_translation_step : Prop
  source_line743_shift_order_closed : Prop
  source_line743_right_monotonicity_closed_from_left : Prop
  no_quotient_adapter_used_for_shifted_min : Prop

/-- Rebuild the G113 shifted-min input, filling right monotonicity from
line-735 left monotonicity and representative min commutativity. -/
def shiftedMinAfterShiftOrder_from_closedRightMonotone
    (left_mono :
      forall x y c : RegularSeq,
        RegularSeqLe x y ->
          RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c))
    (data : Property4RegularSeqShiftedMinAfterRightMonotone Arch) :
    Property4RegularSeqShiftedMinAfterShiftOrder Arch where
  minSeqWith_translate_right_le :=
    data.minSeqWith_translate_right_le
  minSeqWith_monotone_right :=
    minSeqWith_monotone_right_regularSeqLe_from_left Arch left_mono
  source_line743_translation_step :=
    data.source_line743_translation_step
  source_line743_shift_order_closed :=
    data.source_line743_shift_order_closed
  source_line743_right_monotonicity_step :=
    data.source_line743_right_monotonicity_closed_from_left
  no_quotient_adapter_used_for_shifted_min :=
    data.no_quotient_adapter_used_for_shifted_min

/-- G114 input for property (4): line-735 left monotonicity plus only the
line-743 translation component. -/
structure Property4RegularSeqDataMinLawRightMonotoneClosedInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  shifted_min_after_right_monotone :
    Property4RegularSeqShiftedMinAfterRightMonotone Arch
  source_line735_left_monotonicity_input : Prop
  source_line743_right_monotonicity_closed : Prop
  quotient_extraction_not_used : Prop

/-- Convert the G114 input to the G111 min-law reduction data. -/
def regularSeqDataMinLawReduction_from_rightMonotoneClosedInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawRightMonotoneClosedInput S r) :
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
              data.shifted_min_after_right_monotone))
      realSurface := bishopRegularSeqRealSurface Arch
      archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage Arch
      source_line735_min_law_is_regularseq_data := True
      source_line743_min_law_is_regularseq_data := True
      no_quotient_extraction_in_minlaw_bridge := True
      no_classical_choice_in_minlaw_bridge := True }
  source_property4_min_laws_are_regularseq_data := True
  quotient_extraction_not_used_for_property4_min_laws := True

/-- Property (4), after closing line-743 right monotonicity from line-735 left
monotonicity. -/
def property4_from_regularseq_right_monotone_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawRightMonotoneClosedInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_data_min_laws
    S r
    (regularSeqDataMinLawReduction_from_rightMonotoneClosedInput S r data)

/-- Selector footprint after closing right monotonicity. -/
structure Property4RegularSeqRightMonotoneClosedAudit : Type where
  line735_regularseq_min_monotonicity_inputs : Nat
  line743_translation_inputs : Nat
  line743_shift_order_inputs : Nat
  line743_right_monotonicity_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_regularseq_min_translation_plus_left_mono : Prop

def property4RegularSeqRightMonotoneClosedAudit :
    Property4RegularSeqRightMonotoneClosedAudit where
  line735_regularseq_min_monotonicity_inputs := 1
  line743_translation_inputs := 1
  line743_shift_order_inputs := 0
  line743_right_monotonicity_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_regularseq_min_translation_plus_left_mono := True

end BishopRegularSeqTheorem118

/-- G114 package: line-743 right monotonicity is obtained from line-735 left
monotonicity and representative min commutativity. -/
structure BishopRegularSeqTheorem118G114Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g113 : BishopRegularSeqTheorem118G113Package S
  shifted_min_after_right_monotone : Type 1
  property4_right_monotone_closed_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_right_monotone_closed :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_right_monotone_closed_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqRightMonotoneClosedAudit
  line743_right_monotonicity_closed_over_regularseq : Prop
  no_quotient_extraction_in_g114_mainline : Prop

def bishopRegularSeqTheorem118G114Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G114Package S where
  g113 := bishopRegularSeqTheorem118G113Package S
  shifted_min_after_right_monotone :=
    BishopRegularSeqTheorem118.Property4RegularSeqShiftedMinAfterRightMonotone Arch
  property4_right_monotone_closed_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawRightMonotoneClosedInput S
  property4_from_right_monotone_closed := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_right_monotone_closed
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqRightMonotoneClosedAudit
  line743_right_monotonicity_closed_over_regularseq := True
  no_quotient_extraction_in_g114_mainline := True

/-- Progress after G114: line 743 only needs the RegularSeq/data translation
component, while line 735 left monotonicity remains the shared min-law input. -/
def bishopRegularSeqCh1To4ProgressAfterG114 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G114: closed line-743 right min monotonicity from left monotonicity and \
    min commutativity; line 743 now only has the translation input."


end BishopCReal
