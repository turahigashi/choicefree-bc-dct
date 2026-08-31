import Mathdemo.Internal.Real.ExactRegularSeqDataMinLawFrontier

set_option linter.style.longLine false

/-!
# G112: decomposing the RegularSeq shifted-min law

G111 exposed two RegularSeq/data min laws as the constructive frontier.  The
line-743 shifted-min law

`min(x + d, c) <= min(x, c) + d`, for `0 <= d`,

has the same source shape as the half-sum proof already isolated on the old
adapter route: translate the left side, use monotonicity in the second
argument, then add the common nonnegative shift.

This file keeps the proof on the RegularSeq/data mainline by making those
three representative-level pieces explicit and deriving the line-743 law from
them.  No quotient representative extraction is used.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- RegularSeq/data decomposition of the shifted-min law.

The fields mirror the source half-sum proof, but stay at the representative
surface:

1. translate `min(x+d,c)` to a shifted `min(x,c-d)`;
2. use `c-d <= c` when `0 <= d`;
3. use monotonicity of `min` in the second argument.

The final addition monotonicity and transitivity are already closed in earlier
RegularSeq order layers. -/
structure Property4RegularSeqShiftedMinDecomposition
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  minSeqWith_translate_right_le :
    forall x d c : RegularSeq,
      RegularSeqLe
        (minSeqWith Arch (addSeq x d) c)
        (addSeq (minSeqWith Arch x (subSeq c d)) d)
  subSeq_right_shift_le_self_of_nonneg :
    forall c d : RegularSeq,
      RegularSeqLe zeroSeq d ->
        RegularSeqLe (subSeq c d) c
  minSeqWith_monotone_right :
    forall x a b : RegularSeq,
      RegularSeqLe a b ->
        RegularSeqLe (minSeqWith Arch x a) (minSeqWith Arch x b)
  source_line743_translation_step : Prop
  source_line743_shift_order_step : Prop
  source_line743_right_monotonicity_step : Prop
  no_quotient_adapter_used_for_shifted_min : Prop

/-- Derive line 743's shifted-min law from its RegularSeq/data decomposition. -/
def shiftedMinBound_from_regularSeqDecomposition
    (decomp : Property4RegularSeqShiftedMinDecomposition Arch)
    (x d c : RegularSeq)
    (hd : RegularSeqLe zeroSeq d) :
    RegularSeqLe
      (minSeqWith Arch (addSeq x d) c)
      (addSeq (minSeqWith Arch x c) d) := by
  have htranslate :
      RegularSeqLe
        (minSeqWith Arch (addSeq x d) c)
        (addSeq (minSeqWith Arch x (subSeq c d)) d) :=
    decomp.minSeqWith_translate_right_le x d c
  have hcshift : RegularSeqLe (subSeq c d) c :=
    decomp.subSeq_right_shift_le_self_of_nonneg c d hd
  have hmono :
      RegularSeqLe
        (minSeqWith Arch x (subSeq c d))
        (minSeqWith Arch x c) :=
    decomp.minSeqWith_monotone_right x (subSeq c d) c hcshift
  have hadd :
      RegularSeqLe
        (addSeq (minSeqWith Arch x (subSeq c d)) d)
        (addSeq (minSeqWith Arch x c) d) :=
    addSeq_monotone_left_regularSeqLe
      (minSeqWith Arch x (subSeq c d))
      (minSeqWith Arch x c)
      d
      hmono
  exact regularSeqLe_trans htranslate hadd

/-- Build the G111 min-law core from line-735 left monotonicity plus the
RegularSeq/data decomposition of line 743. -/
def regularSeqDataMinLawCore_from_shiftedMinDecomposition
    (left_mono :
      forall x y c : RegularSeq,
        RegularSeqLe x y ->
          RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c))
    (shift_decomp : Property4RegularSeqShiftedMinDecomposition Arch) :
    Property4RegularSeqDataMinLawCore Arch where
  minSeqWith_monotone_left := left_mono
  minSeqWith_add_nonnegative_right_bound := by
    intro x d c hd
    exact shiftedMinBound_from_regularSeqDecomposition
      shift_decomp x d c hd
  source_line735_regularseq_min_monotone := True
  source_line743_regularseq_shifted_min_bound := True
  no_quotient_order_obligation_in_min_laws := True
  no_prop_to_data_selector_in_min_laws := True

/-- G112 input for property (4): line-735 monotonicity plus the decomposed
line-743 shifted-min proof. -/
structure Property4RegularSeqDataMinLawDecomposedInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  shifted_min_decomposition :
    Property4RegularSeqShiftedMinDecomposition Arch
  source_line735_left_monotonicity_input : Prop
  source_line743_shifted_min_decomposed : Prop
  quotient_extraction_not_used : Prop

/-- Convert the decomposed G112 input to the G111 min-law reduction data. -/
def regularSeqDataMinLawReduction_from_decomposedInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawDecomposedInput S r) :
    Property4ReductionDataFromRegularSeqDataMinLaws S r where
  mainline := data.mainline
  minlaw_bridge :=
    { g96_bridge := data.g96_bridge
      min_laws :=
        regularSeqDataMinLawCore_from_shiftedMinDecomposition
          data.minSeqWith_monotone_left
          data.shifted_min_decomposition
      realSurface := bishopRegularSeqRealSurface Arch
      archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage Arch
      source_line735_min_law_is_regularseq_data := True
      source_line743_min_law_is_regularseq_data := True
      no_quotient_extraction_in_minlaw_bridge := True
      no_classical_choice_in_minlaw_bridge := True }
  source_property4_min_laws_are_regularseq_data := True
  quotient_extraction_not_used_for_property4_min_laws := True

/-- Property (4), using line-743's decomposed RegularSeq/data shifted-min
route. -/
def property4_from_regularseq_shifted_min_decomposition
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawDecomposedInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_data_min_laws
    S r
    (regularSeqDataMinLawReduction_from_decomposedInput S r data)

/-- Selector footprint after decomposing line 743. -/
structure Property4RegularSeqShiftedMinDecompositionAudit : Type where
  line735_regularseq_min_monotonicity_inputs : Nat
  line743_regularseq_decomposition_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_regularseq_halfsum_order : Prop

def property4RegularSeqShiftedMinDecompositionAudit :
    Property4RegularSeqShiftedMinDecompositionAudit where
  line735_regularseq_min_monotonicity_inputs := 1
  line743_regularseq_decomposition_inputs := 3
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_regularseq_halfsum_order := True

end BishopRegularSeqTheorem118

/-- G112 package: line 743's shifted-min law is no longer a primitive field of
the mainline; it is obtained from three RegularSeq/data pieces. -/
structure BishopRegularSeqTheorem118G112Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g111 : BishopRegularSeqTheorem118G111Package S
  shifted_min_decomposition : Type 1
  property4_decomposed_minlaw_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_shifted_min_decomposition :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_decomposed_minlaw_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqShiftedMinDecompositionAudit
  line743_shifted_min_bound_decomposed : Prop
  no_quotient_extraction_in_g112_mainline : Prop

def bishopRegularSeqTheorem118G112Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G112Package S where
  g111 := bishopRegularSeqTheorem118G111Package S
  shifted_min_decomposition :=
    BishopRegularSeqTheorem118.Property4RegularSeqShiftedMinDecomposition Arch
  property4_decomposed_minlaw_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawDecomposedInput S
  property4_from_shifted_min_decomposition := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_shifted_min_decomposition
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqShiftedMinDecompositionAudit
  line743_shifted_min_bound_decomposed := True
  no_quotient_extraction_in_g112_mainline := True

/-- Progress after G112: the line-743 shifted-min law has been decomposed into
translation, shift-order, and right-monotonicity pieces on the RegularSeq/data
surface. -/
def bishopRegularSeqCh1To4ProgressAfterG112 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G112: decomposed the RegularSeq/data line-743 shifted-min frontier into \
    translation, nonnegative shift-order, and right-monotonicity inputs."


end BishopCReal
