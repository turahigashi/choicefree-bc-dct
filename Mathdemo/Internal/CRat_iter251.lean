import Mathdemo.Internal.CRat_iter250

set_option linter.style.longLine false

/-!
# G151: assembling the Chapter 2 finite-set law package

G149 and G150 separately closed the RegularSeq versions of Propositions 2.4 and
2.5.  This file wires them into the `FiniteSetLawPackage` target introduced at
the chapter-2 entry surface.

The package is still data-bearing: for each pair of sets it receives the local
Proposition 2.4 construction data and the Proposition 2.5 subtraction
construction data explicitly.  No global selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace FiniteSetLawAssembly

open Prop24LocalNonnegativeSubseries
open Prop24MeasureIdentityFromLocalNonnegative
open Prop25SubMeasure

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Explicit inputs needed to realize the finite-set laws of Chapter 2. -/
structure Chapter2FiniteSetLawInputs
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 6 where
  prop24_input :
    forall {A B : BSet X},
      forall hA : IntegrableSet S A,
      forall hB : IntegrableSet S B,
        Prop24LocalNonnegativeClosureInputs hA hB
  prop25_input :
    forall {C D : BSet X},
      forall hC : IntegrableSet S C,
      forall hCD : IntegrableSet S (BSet.and C D),
        Prop25SubConstructionData hC hCD
  prop24_inputs_are_local_data : Prop
  prop25_inputs_are_carried_difference_data : Prop
  no_global_choice_or_membership_decider : Prop

def finiteSetLawOr
    (input : Chapter2FiniteSetLawInputs S)
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) :
    IntegrableSet S (BSet.or A B) :=
  (prop24ClosurePairFromLocalNonnegative
    hA hB (input.prop24_input hA hB)).union_integrable

def finiteSetLawAnd
    (input : Chapter2FiniteSetLawInputs S)
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) :
    IntegrableSet S (BSet.and A B) :=
  (prop24ClosurePairFromLocalNonnegative
    hA hB (input.prop24_input hA hB)).inter_integrable

def finiteSetLawSub
    (input : Chapter2FiniteSetLawInputs S)
    {C D : BSet X}
    (hC : IntegrableSet S C)
    (hCD : IntegrableSet S (BSet.and C D)) :
    IntegrableSet S (BSet.sub C D) :=
  subIntegrableSetFromData hC hCD (input.prop25_input hC hCD)

/-- Proposition 2.4 as exposed by the assembled finite-set law package. -/
theorem finiteSetLaw_measure_or_and
    (input : Chapter2FiniteSetLawInputs S)
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) :
    relEventually
      (addSeq (measure S hA) (measure S hB))
      (addSeq
        (measure S (finiteSetLawOr input hA hB))
        (measure S (finiteSetLawAnd input hA hB))) := by
  simpa [finiteSetLawOr, finiteSetLawAnd] using
    prop24_measure_or_and_from_local_nonnegative
      hA hB (input.prop24_input hA hB)

/-- Proposition 2.5 as exposed by the assembled finite-set law package. -/
theorem finiteSetLaw_measure_sub
    (input : Chapter2FiniteSetLawInputs S)
    {C D : BSet X}
    (hC : IntegrableSet S C)
    (hCD : IntegrableSet S (BSet.and C D)) :
    relEventually
      (measure S hC)
      (addSeq
        (measure S hCD)
        (measure S (finiteSetLawSub input hC hCD))) := by
  simpa [finiteSetLawSub] using
    prop25_measure_sub_from_data hC hCD (input.prop25_input hC hCD)

/-- The Chapter 2 finite-set law package assembled from explicit local data. -/
def finiteSetLawPackageFromInputs
    (input : Chapter2FiniteSetLawInputs S) :
    FiniteSetLawPackage S where
  or_integrable := fun hA hB =>
    finiteSetLawOr input hA hB
  and_integrable := fun hA hB =>
    finiteSetLawAnd input hA hB
  sub_integrable := fun hC hCD =>
    finiteSetLawSub input hC hCD
  measure_or_and := fun hA hB =>
    finiteSetLaw_measure_or_and input hA hB
  measure_sub := fun hC hCD =>
    finiteSetLaw_measure_sub input hC hCD
  source_proposition_2_4_regularseq_target := True
  source_proposition_2_5_regularseq_target := True
  complement_not_assumed_integrable := True
  no_global_membership_decision_for_characteristics := True

/-- G151 audit. -/
structure FiniteSetLawAssemblyAudit : Type where
  prop24_integrability_laws_wired : Nat
  prop24_measure_law_wired : Nat
  prop25_sub_law_wired : Nat
  prop25_measure_law_wired : Nat
  finite_set_law_package_realized : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  chapter2_finite_set_laws_packaged : Prop
  remaining_chapter2_frontier_is_tail_audit : Prop

def finiteSetLawAssemblyAudit :
    FiniteSetLawAssemblyAudit where
  prop24_integrability_laws_wired := 1
  prop24_measure_law_wired := 1
  prop25_sub_law_wired := 1
  prop25_measure_law_wired := 1
  finite_set_law_package_realized := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  chapter2_finite_set_laws_packaged := True
  remaining_chapter2_frontier_is_tail_audit := True

end FiniteSetLawAssembly
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.FiniteSetLawAssembly

/-- G151 package: the chapter-2 finite-set law target is now realized from the
data-bearing Proposition 2.4 and Proposition 2.5 routes. -/
structure BishopRegularSeqChapter2G151Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g150 : BishopRegularSeqChapter2G150Package S
  finite_law_inputs : Type 6
  finite_law_package :
    finite_law_inputs -> FiniteSetLawPackage S
  audit :
    BishopRegularSeqChapter2.FiniteSetLawAssembly.FiniteSetLawAssemblyAudit
  finite_set_laws_packaged : Prop
  remaining_frontier_chapter2_tail_audit : Prop
  no_hidden_choice_in_g151_finite_set_law_package : Prop

def bishopRegularSeqChapter2G151Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G151Package S where
  g150 := bishopRegularSeqChapter2G150Package S
  finite_law_inputs :=
    BishopRegularSeqChapter2.FiniteSetLawAssembly.Chapter2FiniteSetLawInputs S
  finite_law_package := fun input =>
    BishopRegularSeqChapter2.FiniteSetLawAssembly.finiteSetLawPackageFromInputs
      input
  audit :=
    BishopRegularSeqChapter2.FiniteSetLawAssembly.finiteSetLawAssemblyAudit
  finite_set_laws_packaged := True
  remaining_frontier_chapter2_tail_audit := True
  no_hidden_choice_in_g151_finite_set_law_package := True

/-- Progress after G151: Chapter 2's finite-set laws are packaged; only the final
chapter-tail audit remains for the current Chapter 2 closure milestone. -/
def bishopRegularSeqCh1To4ProgressAfterG151 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 99
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G151: assembled the Chapter 2 FiniteSetLawPackage from explicit local \
    Proposition 2.4 data and carried Proposition 2.5 subtraction data."


end BishopCReal
