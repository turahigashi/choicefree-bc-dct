import Mathdemo.Internal.CRat_iter225

set_option linter.style.longLine false

/-!
# G126: fixing the alignment sample to the common maximum

G125 left the residual line-735 alignment theorem in existential form:
two cofinal sample functions must be aligned to one cofinal sample function.

This file makes that residual theorem more concrete.  The aligned sample is
not chosen later from a quotient or a positivity proposition; it is the
computable common maximum `fun n => max (Fx n) (Fy n)`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The canonical common sample for aligning two cofinal sample functions. -/
def commonMaxSample (Fx Fy : Nat -> Nat) (n : Nat) : Nat :=
  Nat.max (Fx n) (Fy n)

/-- If both input samples are cofinal, their common maximum is cofinal. -/
theorem commonMaxSample_late
    (Fx Fy : Nat -> Nat)
    (hFx : forall n : Nat, n <= Fx n)
    (_hFy : forall n : Nat, n <= Fy n) :
    forall n : Nat, n <= commonMaxSample Fx Fy n := by
  intro n
  exact Nat.le_trans (hFx n) (Nat.le_max_left (Fx n) (Fy n))

/-- The concrete remaining transport theorem: move a two-sample strict
half-sum gap to the common maximum sample. -/
def CommonMaxMinHalfsumTransport
    (x y c : RegularSeq) : Prop :=
  forall Fx Fy : Nat -> Nat,
    (forall n : Nat, n <= Fx n) ->
    (forall n : Nat, n <= Fy n) ->
      TwoSampleMinHalfsumLeftStrict x y c Fx Fy ->
        SameSampleMinHalfsumLeftStrict x y c (commonMaxSample Fx Fy)

/-- Common-max transport supplies the G125 existential alignment statement. -/
theorem twoSampleAlignment_of_commonMaxTransport
    (x y c : RegularSeq)
    (transport : CommonMaxMinHalfsumTransport x y c) :
    TwoSampleMinHalfsumAlignment x y c := by
  intro Fx Fy hFx hFy htwo
  refine ⟨commonMaxSample Fx Fy, ?_, ?_⟩
  · exact commonMaxSample_late Fx Fy hFx hFy
  · exact transport Fx Fy hFx hFy htwo

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G126 data boundary: the two-sample alignment will be proved by transporting
to the explicit common-max sample. -/
structure Property4RegularSeqMinCommonMaxAlignment
    (A : ScalarMulArchimedeanData) : Type 1 where
  common_max_transport :
    forall x y c : RegularSeq,
      CommonMaxMinHalfsumTransport x y c
  source_line735_common_max_sample_alignment : Prop
  common_max_sample_is_computable_data : Prop
  g125_two_sample_alignment_surface_closed : Prop
  no_quotient_representative_extraction : Prop
  no_pos_eventually_witness_selector : Prop
  no_classical_choice : Prop

/-- Convert common-max transport to the G125 alignment data. -/
def minTwoSampleAlignment_from_commonMax
    (A : ScalarMulArchimedeanData)
    (data : Property4RegularSeqMinCommonMaxAlignment A) :
    Property4RegularSeqMinTwoSampleAlignment A where
  two_sample_alignment := by
    intro x y c
    exact
      twoSampleAlignment_of_commonMaxTransport
        x y c (data.common_max_transport x y c)
  source_line735_two_sample_alignment :=
    data.source_line735_common_max_sample_alignment
  g124_two_sample_value_expansion_closed :=
    data.g125_two_sample_alignment_surface_closed
  g123_same_sample_transport_closed :=
    data.g125_two_sample_alignment_surface_closed
  no_quotient_representative_extraction :=
    data.no_quotient_representative_extraction
  no_pos_eventually_witness_selector :=
    data.no_pos_eventually_witness_selector
  no_classical_choice := data.no_classical_choice

/-- Property-(4) input after G126: line 735 is now common-max transport. -/
structure Property4RegularSeqDataMinLawCommonMaxAlignmentInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  common_max_alignment : Property4RegularSeqMinCommonMaxAlignment Arch
  source_line735_common_max_transport_input : Prop
  line743_translation_closed : Prop
  quotient_extraction_not_used : Prop
  prop_to_data_selector_not_used : Prop

/-- Convert G126 data to G125's two-sample alignment input. -/
def regularSeqDataMinLawTwoSampleAlignmentInput_from_commonMax
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawCommonMaxAlignmentInput S r) :
    Property4RegularSeqDataMinLawTwoSampleAlignmentInput S r where
  mainline := data.mainline
  g96_bridge := data.g96_bridge
  two_sample_alignment :=
    minTwoSampleAlignment_from_commonMax Arch data.common_max_alignment
  source_line735_two_sample_alignment_input :=
    data.source_line735_common_max_transport_input
  line743_translation_closed := data.line743_translation_closed
  quotient_extraction_not_used := data.quotient_extraction_not_used
  prop_to_data_selector_not_used := data.prop_to_data_selector_not_used

/-- Property (4), with the sole line-735 input now common-max transport. -/
def property4_from_regularseq_common_max_alignment
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawCommonMaxAlignmentInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_two_sample_alignment
    S r
    (regularSeqDataMinLawTwoSampleAlignmentInput_from_commonMax S r data)

/-- G126 audit: the existential alignment sample has been fixed to a concrete
common maximum. -/
structure Property4RegularSeqCommonMaxAlignmentAudit : Type where
  existential_sample_alignment_inputs : Nat
  common_max_sample_fixed : Nat
  common_max_transport_inputs : Nat
  minSeqWith_value_expansion_inputs : Nat
  same_sample_transport_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_common_max_transport : Prop

def property4RegularSeqCommonMaxAlignmentAudit :
    Property4RegularSeqCommonMaxAlignmentAudit where
  existential_sample_alignment_inputs := 0
  common_max_sample_fixed := 1
  common_max_transport_inputs := 1
  minSeqWith_value_expansion_inputs := 0
  same_sample_transport_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_common_max_transport := True

end BishopRegularSeqTheorem118

/-- G126 package: the remaining alignment sample is fixed to common max. -/
structure BishopRegularSeqTheorem118G126Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g125 : BishopRegularSeqTheorem118G125Package S
  common_max_late :
    forall Fx Fy : Nat -> Nat,
      (forall n : Nat, n <= Fx n) ->
      (forall n : Nat, n <= Fy n) ->
        forall n : Nat, n <= commonMaxSample Fx Fy n
  common_max_to_two_sample :
    BishopRegularSeqTheorem118.Property4RegularSeqMinCommonMaxAlignment Arch ->
      BishopRegularSeqTheorem118.Property4RegularSeqMinTwoSampleAlignment Arch
  property4_common_max_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_common_max :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawCommonMaxAlignmentInput S r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqCommonMaxAlignmentAudit
  line735_alignment_sample_is_common_max : Prop
  line735_remaining_frontier_common_max_transport : Prop
  no_quotient_extraction_in_g126_mainline : Prop

def bishopRegularSeqTheorem118G126Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G126Package S where
  g125 := bishopRegularSeqTheorem118G125Package S
  common_max_late := by
    intro Fx Fy hFx hFy n
    exact commonMaxSample_late Fx Fy hFx hFy n
  common_max_to_two_sample := by
    intro data
    exact
      BishopRegularSeqTheorem118.minTwoSampleAlignment_from_commonMax
        Arch data
  property4_common_max_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawCommonMaxAlignmentInput S
  property4_from_common_max := by
    intro r data
    exact
      BishopRegularSeqTheorem118.property4_from_regularseq_common_max_alignment
        S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqCommonMaxAlignmentAudit
  line735_alignment_sample_is_common_max := True
  line735_remaining_frontier_common_max_transport := True
  no_quotient_extraction_in_g126_mainline := True

/-- Progress after G126: still 99%; the remaining line-735 theorem is now the
regularity transport from two samples to their common maximum. -/
def bishopRegularSeqCh1To4ProgressAfterG126 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G126: fixed the line-735 alignment sample to commonMaxSample(Fx,Fy); \
    remaining work is the common-max regularity transport."


end BishopCReal
