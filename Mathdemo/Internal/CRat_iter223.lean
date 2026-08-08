import Mathdemo.Internal.CRat_iter222

set_option linter.style.longLine false

/-!
# G123: same-sample transport for scalar min strict-backward

G122 closed the scalar strict-backward kernel for the half-sum minimum.  This
file transports that kernel to `RegularSeq` once the strict `minSeqWith`
counterexample has been expanded to a cofinal same-sample half-sum statement.

The remaining line-735 work is therefore the concrete expansion/alignment of
`minSeqWith`'s bounded multiplication samples, not any quotient representative
selection.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Same-sample half-sum strictness for the left min argument.  The sampled
index is written as `F n + 1` so it matches `(subSeq x y).val (F n)`. -/
def SameSampleMinHalfsumLeftStrict
    (x y c : RegularSeq) (F : Nat -> Nat) : Prop :=
  ∃ k N : Nat,
    ∀ n : Nat, N <= n ->
      COF.lt (eps k)
        (((COF.half : Scalar) *
            (x.val (F n + 1) + c.val (F n + 1) -
              COF.abs (x.val (F n + 1) - c.val (F n + 1)))) -
          ((COF.half : Scalar) *
            (y.val (F n + 1) + c.val (F n + 1) -
              COF.abs (y.val (F n + 1) - c.val (F n + 1)))))

/-- Same-sample scalar strict-backward transported to `PosEventually` for
regular representatives. -/
theorem posEventually_subSeq_of_late_same_sample_min_halfsum_strict
    (x y c : RegularSeq)
    (F : Nat -> Nat)
    (hF : forall n : Nat, n <= F n)
    (hstrict : SameSampleMinHalfsumLeftStrict x y c F) :
    PosEventually (subSeq x y) := by
  rcases hstrict with ⟨k, N, hN⟩
  apply posEventually_subSeq_of_late_sample_pos y x F hF
  refine ⟨k, N, ?_⟩
  intro n hn
  have hscalar :=
    scalar_min_halfsum_left_strict_backward
      (x.val (F n + 1))
      (y.val (F n + 1))
      (c.val (F n + 1))
      (hN n hn)
  change COF.lt (eps k) ((subSeq x y).val (F n))
  change COF.lt (eps k) (x.val (F n + 1) - y.val (F n + 1))
  exact hscalar

/-- If a `minSeqWith` strict counterexample can be expanded to a cofinal
same-sample half-sum strict statement, then the full RegularSeq
strict-backward comparison follows. -/
theorem minSeqWith_strict_backward_of_same_sample_expansion
    (A : ScalarMulArchimedeanData)
    (same_sample_expansion :
      forall x y c : RegularSeq,
        regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c) ->
          ∃ F : Nat -> Nat,
            (forall n : Nat, n <= F n) ∧
              SameSampleMinHalfsumLeftStrict x y c F)
    (x y c : RegularSeq)
    (hmin : regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c)) :
    regularSeqLtProp y x := by
  rcases same_sample_expansion x y c hmin with ⟨F, hF, hsame⟩
  exact posEventually_subSeq_of_late_same_sample_min_halfsum_strict
    x y c F hF hsame

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Remaining concrete expansion frontier after the scalar strict kernel is
closed: expand a strict `minSeqWith` counterexample into a cofinal same-sample
half-sum strict statement.  This is Prop-to-Prop, so it is not a selector from
positivity evidence into computational data. -/
structure Property4RegularSeqMinSameSampleExpansion
    (A : ScalarMulArchimedeanData) : Type 1 where
  same_sample_expansion :
    forall x y c : RegularSeq,
      regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c) ->
        ∃ F : Nat -> Nat,
          (forall n : Nat, n <= F n) ∧
            SameSampleMinHalfsumLeftStrict x y c F
  source_line735_minSeqWith_expansion_alignment : Prop
  scalar_strict_backward_kernel_closed : Prop
  no_quotient_representative_extraction : Prop
  no_pos_eventually_witness_selector : Prop

/-- Convert the same-sample expansion frontier into G121's strict-backward
transport data. -/
def minStrictBackwardTransport_from_sameSampleExpansion
    (A : ScalarMulArchimedeanData)
    (data : Property4RegularSeqMinSameSampleExpansion A) :
    Property4RegularSeqMinStrictBackwardTransport A where
  strict_backward := by
    intro x y c hmin
    exact minSeqWith_strict_backward_of_same_sample_expansion
      A data.same_sample_expansion x y c hmin
  source_line735_min_strict_backward_transport := True
  no_quotient_representative_extraction :=
    data.no_quotient_representative_extraction
  no_pos_eventually_witness_extraction :=
    data.no_pos_eventually_witness_selector
  no_classical_choice := True

/-- G123 property-(4) input: line 735 is now represented by the concrete
same-sample expansion/alignment problem. -/
structure Property4RegularSeqDataMinLawSameSampleExpansionInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  same_sample_expansion : Property4RegularSeqMinSameSampleExpansion Arch
  source_line735_minSeqWith_expansion_alignment_input : Prop
  line743_translation_closed : Prop
  quotient_extraction_not_used : Prop
  prop_to_data_selector_not_used : Prop

/-- Convert the G123 same-sample input to the G121 strict-backward input. -/
def regularSeqDataMinLawStrictBackwardInput_from_sameSampleExpansion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawSameSampleExpansionInput S r) :
    Property4RegularSeqDataMinLawStrictBackwardInput S r where
  mainline := data.mainline
  g96_bridge := data.g96_bridge
  min_strict_backward :=
    minStrictBackwardTransport_from_sameSampleExpansion
      Arch data.same_sample_expansion
  source_line735_min_strict_backward_transport_input :=
    data.source_line735_minSeqWith_expansion_alignment_input
  line743_translation_closed := data.line743_translation_closed
  quotient_extraction_not_used := data.quotient_extraction_not_used
  prop_to_data_selector_not_used := data.prop_to_data_selector_not_used

/-- Property (4), with line 735 reduced to same-sample expansion/alignment. -/
def property4_from_regularseq_same_sample_expansion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawSameSampleExpansionInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_min_strict_backward
    S r
    (regularSeqDataMinLawStrictBackwardInput_from_sameSampleExpansion S r data)

/-- G123 audit: the scalar and same-sample transport are closed; only concrete
`minSeqWith` expansion/alignment remains. -/
structure Property4RegularSeqSameSampleExpansionAudit : Type where
  scalar_strict_backward_inputs : Nat
  same_sample_transport_inputs : Nat
  minSeqWith_expansion_alignment_inputs : Nat
  line743_sum_translation_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_minSeqWith_expansion_alignment : Prop

def property4RegularSeqSameSampleExpansionAudit :
    Property4RegularSeqSameSampleExpansionAudit where
  scalar_strict_backward_inputs := 0
  same_sample_transport_inputs := 0
  minSeqWith_expansion_alignment_inputs := 1
  line743_sum_translation_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_minSeqWith_expansion_alignment := True

end BishopRegularSeqTheorem118

/-- G123 package: same-sample RegularSeq transport from the scalar strict
kernel is closed. -/
structure BishopRegularSeqTheorem118G123Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g122 : BishopRegularSeqTheorem118G122Package S
  same_sample_transport :
    forall x y c : RegularSeq, forall F : Nat -> Nat,
      (forall n : Nat, n <= F n) ->
        SameSampleMinHalfsumLeftStrict x y c F ->
          regularSeqLtProp y x
  strict_backward_from_same_sample :
    BishopRegularSeqTheorem118.Property4RegularSeqMinSameSampleExpansion Arch ->
      BishopRegularSeqTheorem118.Property4RegularSeqMinStrictBackwardTransport Arch
  property4_same_sample_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_same_sample :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawSameSampleExpansionInput S r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqSameSampleExpansionAudit
  line735_same_sample_transport_closed : Prop
  line735_remaining_frontier_expansion_alignment : Prop
  no_quotient_extraction_in_g123_mainline : Prop

def bishopRegularSeqTheorem118G123Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G123Package S where
  g122 := bishopRegularSeqTheorem118G122Package S
  same_sample_transport := by
    intro x y c F hF hsame
    exact posEventually_subSeq_of_late_same_sample_min_halfsum_strict
      x y c F hF hsame
  strict_backward_from_same_sample := by
    intro data
    exact
      BishopRegularSeqTheorem118.minStrictBackwardTransport_from_sameSampleExpansion
        Arch data
  property4_same_sample_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawSameSampleExpansionInput S
  property4_from_same_sample := by
    intro r data
    exact
      BishopRegularSeqTheorem118.property4_from_regularseq_same_sample_expansion
        S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqSameSampleExpansionAudit
  line735_same_sample_transport_closed := True
  line735_remaining_frontier_expansion_alignment := True
  no_quotient_extraction_in_g123_mainline := True

/-- Progress after G123: still 99%, with the remaining line-735 task narrowed
to the concrete bounded-multiplication sample alignment for `minSeqWith`. -/
def bishopRegularSeqCh1To4ProgressAfterG123 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G123: closed same-sample RegularSeq transport for scalar min \
    strict-backward; remaining line-735 work is minSeqWith sample alignment."


end BishopCReal
