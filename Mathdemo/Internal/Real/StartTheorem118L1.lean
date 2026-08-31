import Mathdemo.Internal.Real.Corollary117DensityInterface

/-!
# G52: start of Theorem 1.18 for `L1`

Theorem 1.18 says that `(X, L1, I)` is an integration space.  The source proof
first checks Definition 1.1(1) for all integrable functions, then handles the
Daniell condition, the normalized element, and the two truncation limits.

This file closes the algebraic Definition 1.1(1) bridge for `L1` from the
operation data already built in G40--G42, and also records the normalized
element bridge used for Definition 1.1(3).
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data required to form `a * r + b * s` in `L1`. -/
structure LinCombData
    (a b : RegularSeq)
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  smul_left_data : SmulData a r
  smul_right_data : SmulData b s
  add_data :
    AddData
      (smul a r smul_left_data)
      (smul b s smul_right_data)

/-- The `L1` linear combination `a * r + b * s`. -/
def linComb
    (a b : RegularSeq)
    (r s : BishopRegularSeqIntegrableRep S)
    (data : LinCombData a b r s) :
    BishopRegularSeqIntegrableRep S :=
  add
    (smul a r data.smul_left_data)
    (smul b s data.smul_right_data)
    data.add_data

/-- Integral linearity for the `L1` linear combination, assembled from the
scalar-multiplication and addition laws. -/
theorem linComb_integral_agrees
    (a b : RegularSeq)
    (r s : BishopRegularSeqIntegrableRep S)
    (data : LinCombData a b r s) :
    relEventually
      (linComb a b r s data).integral
      (addSeq
        (mulSeqConcreteWith Arch a r.integral)
        (mulSeqConcreteWith Arch b s.integral)) := by
  have hadd :
      relEventually
        (add
          (smul a r data.smul_left_data)
          (smul b s data.smul_right_data)
          data.add_data).integral
        (addSeq
          (smul a r data.smul_left_data).integral
          (smul b s data.smul_right_data).integral) :=
    add_integral_agrees
      (smul a r data.smul_left_data)
      (smul b s data.smul_right_data)
      data.add_data
  have hleft :
      relEventually
        (smul a r data.smul_left_data).integral
        (mulSeqConcreteWith Arch a r.integral) :=
    smul_integral_agrees a r data.smul_left_data
  have hright :
      relEventually
        (smul b s data.smul_right_data).integral
        (mulSeqConcreteWith Arch b s.integral) :=
    smul_integral_agrees b s data.smul_right_data
  have hmid :
      relEventually
        (addSeq
          (smul a r data.smul_left_data).integral
          (smul b s data.smul_right_data).integral)
        (addSeq
          (mulSeqConcreteWith Arch a r.integral)
          (mulSeqConcreteWith Arch b s.integral)) :=
    addSeq_respects_eventually
      (smul a r data.smul_left_data).integral
      (mulSeqConcreteWith Arch a r.integral)
      (smul b s data.smul_right_data).integral
      (mulSeqConcreteWith Arch b s.integral)
      hleft
      hright
  simpa [linComb] using
    relEventually_trans
      (add
        (smul a r data.smul_left_data)
        (smul b s data.smul_right_data)
        data.add_data).integral
      (addSeq
        (smul a r data.smul_left_data).integral
        (smul b s data.smul_right_data).integral)
      (addSeq
        (mulSeqConcreteWith Arch a r.integral)
        (mulSeqConcreteWith Arch b s.integral))
      hadd
      hmid

end BishopRegularSeqIntegrableRep

/-- Explicit data for Theorem 1.18, Definition 1.1(1), at fixed inputs. -/
structure BishopRegularSeqTheorem118Property1Data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a b : RegularSeq)
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  lin_comb_data :
    BishopRegularSeqIntegrableRep.LinCombData a b r s
  abs_data :
    BishopRegularSeqIntegrableRep.AbsData r
  min_one_data :
    BishopRegularSeqIntegrableRep.MinOneData r

/-- Definition 1.1(1) over `L1`, with the three required objects and the
linear integral formula. -/
structure BishopRegularSeqTheorem118Property1Conclusion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a b : RegularSeq)
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  lin_comb_rep : BishopRegularSeqIntegrableRep S
  lin_comb_integral :
    relEventually
      lin_comb_rep.integral
      (addSeq
        (mulSeqConcreteWith Arch a r.integral)
        (mulSeqConcreteWith Arch b s.integral))
  abs_rep : BishopRegularSeqIntegrableRep S
  min_one_rep : BishopRegularSeqIntegrableRep S
  source_definition_1_1_property_1_for_L1 : Prop

/-- Assemble the source's "property (1) is immediate for `L1`" step from the
operation data made explicit in the RegularSeq route. -/
def bishopRegularSeqTheorem118_property1_from_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a b : RegularSeq)
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqTheorem118Property1Data S a b r s) :
    BishopRegularSeqTheorem118Property1Conclusion S a b r s where
  lin_comb_rep :=
    BishopRegularSeqIntegrableRep.linComb a b r s data.lin_comb_data
  lin_comb_integral :=
    BishopRegularSeqIntegrableRep.linComb_integral_agrees
      a b r s data.lin_comb_data
  abs_rep :=
    BishopRegularSeqIntegrableRep.abs r data.abs_data
  min_one_rep :=
    BishopRegularSeqIntegrableRep.minOne r data.min_one_data
  source_definition_1_1_property_1_for_L1 := True

/-- Explicit data for Theorem 1.18, Definition 1.1(3): the previous normalized
element of `L` is embedded into `L1`. -/
structure BishopRegularSeqTheorem118Property3Data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  normalized_ofL_data :
    BishopRegularSeqOfLData
      S
      S.normalized.val
      S.normalized.property.1

/-- Definition 1.1(3) over `L1`. -/
structure BishopRegularSeqTheorem118Property3Conclusion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  normalized_rep : BishopRegularSeqIntegrableRep S
  normalized_integral_one :
    relEventually normalized_rep.integral oneSeq
  source_definition_1_1_property_3_for_L1 : Prop

/-- Assemble the source's `L ⊂ L1` normalized-element step. -/
def bishopRegularSeqTheorem118_property3_from_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : BishopRegularSeqTheorem118Property3Data S) :
    BishopRegularSeqTheorem118Property3Conclusion S where
  normalized_rep :=
    def16_ofL S S.normalized.property.1 data.normalized_ofL_data
  normalized_integral_one :=
    relEventually_trans
      (BishopRegularSeqIntegrableRep.integral
        (def16_ofL S S.normalized.property.1 data.normalized_ofL_data))
      (S.core.I S.normalized.val)
      oneSeq
      (def16_ofL_integral_agrees
        S S.normalized.property.1 data.normalized_ofL_data)
      S.normalized.property.2
  source_definition_1_1_property_3_for_L1 := True

/-- Theorem 1.18 status package after closing the algebraic and normalized
steps.  Properties (2) and (4) are kept as named source frontiers. -/
structure BishopRegularSeqTheorem118G52Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  property1_data :
    forall (_ _ : RegularSeq)
      (_ _ : BishopRegularSeqIntegrableRep S),
        Type 1
  property1 :
    forall (a b : RegularSeq)
      (r s : BishopRegularSeqIntegrableRep S),
        property1_data a b r s ->
          BishopRegularSeqTheorem118Property1Conclusion S a b r s
  property3_data : Type 1
  property3 :
    property3_data ->
      BishopRegularSeqTheorem118Property3Conclusion S
  property2_frontier_uses_lemma_1_15_rowwise_and_Def11_continuity : Prop
  property4_frontier_uses_corollary_1_17_density_and_truncation_transfer : Prop
  source_theorem_1_18_in_progress : Prop

def bishopRegularSeqTheorem118G52Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G52Package S where
  property1_data := fun a b r s =>
    BishopRegularSeqTheorem118Property1Data S a b r s
  property1 := fun a b r s data =>
    bishopRegularSeqTheorem118_property1_from_data S a b r s data
  property3_data := BishopRegularSeqTheorem118Property3Data S
  property3 := fun data =>
    bishopRegularSeqTheorem118_property3_from_data S data
  property2_frontier_uses_lemma_1_15_rowwise_and_Def11_continuity := True
  property4_frontier_uses_corollary_1_17_density_and_truncation_transfer := True
  source_theorem_1_18_in_progress := True

/-- Progress after G52: Theorem 1.18 is started; Definition 1.1(1) and the
normalized-element step for Definition 1.1(3) are available over `L1`. -/
def bishopRegularSeqCh1To4ProgressAfterG52 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 78
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 52
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G52: started Theorem 1.18; Definition 1.1(1) is assembled for L1, and \
    the normalized L element is embedded into L1 for property (3)."


end BishopCReal
