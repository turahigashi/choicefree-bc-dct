import Mathdemo.Internal.Real.ReducingShiftedMinTranslationOrderExact

set_option linter.style.longLine false

/-!
# G116: peeling off the half factor in the shifted-min translation identity

G115 reduced the last line-743 order input to the exact `relEventually`
identity

`min(x+d,c) ~ min(x,c-d)+d`.

This file separates the half-sum minimum into its pre-half body and proves the
representative half-arithmetic needed to move between

`half * (body + d + d)`

and

`half * body + d`.

The remaining translation frontier is thereby narrowed to the pre-half body
identity.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The pre-half body of the half-sum minimum. -/
def minSeqBody (x y : RegularSeq) : RegularSeq :=
  subSeq (addSeq x y) (absSeq (subSeq x y))

/-- Representative half satisfies `half + half = 1` over eventual equality. -/
theorem addSeq_half_half_eventually_one :
    relEventually (addSeq halfSeq halfSeq) oneSeq := by
  apply rel_to_relEventually
  change relVal (addVal halfVal halfVal) oneVal
  intro n
  unfold addVal addIndex halfVal oneVal constVal
  rw [COF.half_add_half]
  rw [show (1 : Scalar) - 1 = 0 from by ring]
  change Le (BishopCRat.CRat.absF (0 : Scalar)) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Adding two half-multiples of the same representative gives the
representative itself. -/
theorem addSeq_half_mul_self_eventually
    (A : ScalarMulArchimedeanData)
    (d : RegularSeq) :
    relEventually
      (addSeq
        (mulSeqConcreteWith A halfSeq d)
        (mulSeqConcreteWith A halfSeq d))
      d := by
  have hdist :
      relEventually
        (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
        (addSeq
          (mulSeqConcreteWith A halfSeq d)
          (mulSeqConcreteWith A halfSeq d)) :=
    mulSeqConcrete_right_distrib_eventually A halfSeq halfSeq d
  have hsum :
      relEventually (addSeq halfSeq halfSeq) oneSeq :=
    addSeq_half_half_eventually_one
  have hmul :
      relEventually
        (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
        (mulSeqConcreteWith A oneSeq d) :=
    mulSeqConcrete_respects_eventually
      A
      (addSeq halfSeq halfSeq) oneSeq
      d d
      hsum
      (relEventually_refl d)
  have hone :
      relEventually (mulSeqConcreteWith A oneSeq d) d :=
    mulSeqConcrete_one_left_eventually A d
  exact
    relEventually_trans
      (addSeq
        (mulSeqConcreteWith A halfSeq d)
        (mulSeqConcreteWith A halfSeq d))
      (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
      d
      (relEventually_symm
        (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
        (addSeq
          (mulSeqConcreteWith A halfSeq d)
          (mulSeqConcreteWith A halfSeq d))
        hdist)
      (relEventually_trans
        (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
        (mulSeqConcreteWith A oneSeq d)
        d
        hmul
        hone)

/-- Multiplying a doubled representative by one half returns the original
representative. -/
theorem half_mul_double_eventually_self
    (A : ScalarMulArchimedeanData)
    (d : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A halfSeq (addSeq d d))
      d := by
  have hdist :
      relEventually
        (mulSeqConcreteWith A halfSeq (addSeq d d))
        (addSeq
          (mulSeqConcreteWith A halfSeq d)
          (mulSeqConcreteWith A halfSeq d)) :=
    mulSeqConcrete_left_distrib_eventually A halfSeq d d
  exact
    relEventually_trans
      (mulSeqConcreteWith A halfSeq (addSeq d d))
      (addSeq
        (mulSeqConcreteWith A halfSeq d)
        (mulSeqConcreteWith A halfSeq d))
      d
      hdist
      (addSeq_half_mul_self_eventually A d)

/-- If the pre-half bodies satisfy the translation identity with a doubled
shift, then the full half-sum `minSeqWith` translation identity follows. -/
theorem minSeqWith_translate_right_eventually_from_body
    (A : ScalarMulArchimedeanData)
    (x d c : RegularSeq)
    (hbody :
      relEventually
        (minSeqBody (addSeq x d) c)
        (addSeq (minSeqBody x (subSeq c d)) (addSeq d d))) :
    relEventually
      (minSeqWith A (addSeq x d) c)
      (addSeq (minSeqWith A x (subSeq c d)) d) := by
  change
    relEventually
      (mulSeqConcreteWith A halfSeq (minSeqBody (addSeq x d) c))
      (addSeq
        (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
        d)
  have hmul :
      relEventually
        (mulSeqConcreteWith A halfSeq (minSeqBody (addSeq x d) c))
        (mulSeqConcreteWith A halfSeq
          (addSeq (minSeqBody x (subSeq c d)) (addSeq d d))) :=
    mulSeqConcrete_respects_eventually
      A
      halfSeq halfSeq
      (minSeqBody (addSeq x d) c)
      (addSeq (minSeqBody x (subSeq c d)) (addSeq d d))
      (relEventually_refl halfSeq)
      hbody
  have hdist :
      relEventually
        (mulSeqConcreteWith A halfSeq
          (addSeq (minSeqBody x (subSeq c d)) (addSeq d d)))
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          (mulSeqConcreteWith A halfSeq (addSeq d d))) :=
    mulSeqConcrete_left_distrib_eventually
      A halfSeq (minSeqBody x (subSeq c d)) (addSeq d d)
  have hdouble :
      relEventually
        (mulSeqConcreteWith A halfSeq (addSeq d d))
        d :=
    half_mul_double_eventually_self A d
  have hadd :
      relEventually
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          (mulSeqConcreteWith A halfSeq (addSeq d d)))
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          d) :=
    addSeq_respects_eventually
      (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
      (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
      (mulSeqConcreteWith A halfSeq (addSeq d d))
      d
      (relEventually_refl
        (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d))))
      hdouble
  exact
    relEventually_trans
      (mulSeqConcreteWith A halfSeq (minSeqBody (addSeq x d) c))
      (mulSeqConcreteWith A halfSeq
        (addSeq (minSeqBody x (subSeq c d)) (addSeq d d)))
      (addSeq
        (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
        d)
      hmul
      (relEventually_trans
        (mulSeqConcreteWith A halfSeq
          (addSeq (minSeqBody x (subSeq c d)) (addSeq d d)))
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          (mulSeqConcreteWith A halfSeq (addSeq d d)))
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          d)
        hdist
        hadd)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G116 body-level translation input for line 743. -/
structure Property4RegularSeqShiftedMinTranslationBody
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  minSeqBody_translate_right_eventually :
    forall x d c : RegularSeq,
      relEventually
        (minSeqBody (addSeq x d) c)
        (addSeq (minSeqBody x (subSeq c d)) (addSeq d d))
  source_line743_body_translation_identity : Prop
  source_line743_half_factor_peeled : Prop
  source_line743_shift_order_closed : Prop
  source_line743_right_monotonicity_closed_from_left : Prop
  no_quotient_adapter_used_for_shifted_min : Prop

/-- Rebuild the G115 exact translation input from the body-level identity. -/
def translationExact_from_bodyTranslation
    (data : Property4RegularSeqShiftedMinTranslationBody Arch) :
    Property4RegularSeqShiftedMinTranslationExact Arch where
  minSeqWith_translate_right_eventually := by
    intro x d c
    exact
      minSeqWith_translate_right_eventually_from_body
        Arch x d c
        (data.minSeqBody_translate_right_eventually x d c)
  source_line743_translation_exact_identity :=
    data.source_line743_body_translation_identity
  source_line743_shift_order_closed :=
    data.source_line743_shift_order_closed
  source_line743_right_monotonicity_closed_from_left :=
    data.source_line743_right_monotonicity_closed_from_left
  no_quotient_adapter_used_for_shifted_min :=
    data.no_quotient_adapter_used_for_shifted_min

/-- G116 input for property (4): line-735 left monotonicity plus body-level
line-743 translation. -/
structure Property4RegularSeqDataMinLawTranslationBodyInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 6 where
  mainline : Property4RegularSeqDataMainlineInput S r
  g96_bridge : Property4ScalarMinKernelClosedCoreUnifiedBridge S
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  shifted_min_translation_body :
    Property4RegularSeqShiftedMinTranslationBody Arch
  source_line735_left_monotonicity_input : Prop
  source_line743_translation_body_identity : Prop
  quotient_extraction_not_used : Prop

/-- Convert the G116 input to the G111 min-law reduction data. -/
def regularSeqDataMinLawReduction_from_translationBodyInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawTranslationBodyInput S r) :
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
                  data.shifted_min_translation_body))))
      realSurface := bishopRegularSeqRealSurface Arch
      archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage Arch
      source_line735_min_law_is_regularseq_data := True
      source_line743_min_law_is_regularseq_data := True
      no_quotient_extraction_in_minlaw_bridge := True
      no_classical_choice_in_minlaw_bridge := True }
  source_property4_min_laws_are_regularseq_data := True
  quotient_extraction_not_used_for_property4_min_laws := True

/-- Property (4), after peeling off the half factor from line-743 translation. -/
def property4_from_regularseq_translation_body
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4RegularSeqDataMinLawTranslationBodyInput S r) :
    Property4Conclusion S r :=
  property4_from_regularseq_data_min_laws
    S r
    (regularSeqDataMinLawReduction_from_translationBodyInput S r data)

/-- Selector footprint after reducing exact translation to the body identity. -/
structure Property4RegularSeqTranslationBodyAudit : Type where
  line735_regularseq_min_monotonicity_inputs : Nat
  line743_translation_order_inputs : Nat
  line743_translation_exact_identity_inputs : Nat
  line743_body_translation_inputs : Nat
  line743_half_factor_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_left_mono_plus_body_translation_identity : Prop

def property4RegularSeqTranslationBodyAudit :
    Property4RegularSeqTranslationBodyAudit where
  line735_regularseq_min_monotonicity_inputs := 1
  line743_translation_order_inputs := 0
  line743_translation_exact_identity_inputs := 0
  line743_body_translation_inputs := 1
  line743_half_factor_inputs := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_left_mono_plus_body_translation_identity := True

end BishopRegularSeqTheorem118

/-- G116 package: line-743 translation is reduced to the pre-half body
identity; the half-arithmetic wrapper is closed. -/
structure BishopRegularSeqTheorem118G116Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g115 : BishopRegularSeqTheorem118G115Package S
  shifted_min_translation_body : Type 1
  property4_translation_body_data :
    BishopRegularSeqIntegrableRep S -> Type 6
  property4_from_translation_body :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_translation_body_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqTranslationBodyAudit
  line743_half_factor_closed_over_regularseq : Prop
  no_quotient_extraction_in_g116_mainline : Prop

def bishopRegularSeqTheorem118G116Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G116Package S where
  g115 := bishopRegularSeqTheorem118G115Package S
  shifted_min_translation_body :=
    BishopRegularSeqTheorem118.Property4RegularSeqShiftedMinTranslationBody Arch
  property4_translation_body_data :=
    BishopRegularSeqTheorem118.Property4RegularSeqDataMinLawTranslationBodyInput S
  property4_from_translation_body := fun r data =>
    BishopRegularSeqTheorem118.property4_from_regularseq_translation_body
      S r data
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqTranslationBodyAudit
  line743_half_factor_closed_over_regularseq := True
  no_quotient_extraction_in_g116_mainline := True

/-- Progress after G116: line 743 only asks for the pre-half body translation
identity; the half wrapper is closed on `RegularSeq`. -/
def bishopRegularSeqCh1To4ProgressAfterG116 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G116: closed the half-arithmetic wrapper for line-743 translation; \
    the remaining line-743 frontier is the pre-half body identity."


end BishopCReal
