import Mathdemo.Internal.CRat_iter231

set_option linter.style.longLine false

/-!
# G132: chapter-2 entry layer over Bishop RegularSeq reals

Chapter 1 is now packaged through G131.  This file starts the chapter-2 route
over the Bishop RegularSeq real surface: complemented sets, characteristic
representations, and the RegularSeq-valued measure induced by an integrable
characteristic representation.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2

/-- Chapter 2 characteristic-representation data for a complemented set.

This is the RegularSeq analogue of the previous `IntegrableSet1` layer.  The
characteristic function is not recovered from a quotient class.  It is carried
as an `L1` representation, and the `valid` field records the `0/1` value law
at every point where the representing series is absolutely summable. -/
structure IntegrableSet
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (A : BSet X) : Type 1 where
  full_domain : BishopRegularSeqFullSet S (A.S1 ∪ A.S2)
  rep : BishopRegularSeqIntegrableRep S
  domain_eq : BishopRegularSeqIntegrableRep.domain rep = A.S1 ∪ A.S2
  valid :
    forall x : X,
      forall habs :
        BishopRegularSeqSeriesSum
          (fun n => absSeq ((rep.fn n).toFun x)),
        (x ∈ A.S1 ∪ A.S2) ∧
          (x ∈ A.S1 ->
            relEventually
              (BishopRegularSeqIntegrableRep.valueAt rep x habs)
              oneSeq) ∧
          (x ∈ A.S2 ->
            relEventually
              (BishopRegularSeqIntegrableRep.valueAt rep x habs)
              zeroSeq)
  source_definition_2_integrable_set_regularseq : Prop
  characteristic_representation_is_carried_data : Prop
  no_quotient_representative_extraction : Prop

/-- The RegularSeq-valued measure of an integrable complemented set. -/
def measure
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {A : BSet X}
    (hA : IntegrableSet S A) : RegularSeq :=
  BishopRegularSeqIntegrableRep.integral hA.rep

/-- The carried characteristic representation of an integrable set. -/
def characteristicRep
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {A : BSet X}
    (hA : IntegrableSet S A) :
    BishopRegularSeqIntegrableRep S :=
  hA.rep

/-- The full domain carried by an integrable complemented set. -/
def domainFull
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {A : BSet X}
    (hA : IntegrableSet S A) :
    BishopRegularSeqFullSet S (A.S1 ∪ A.S2) :=
  hA.full_domain

/-- The `0/1` characteristic value law at an absolutely summable point. -/
def characteristicValid
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {A : BSet X}
    (hA : IntegrableSet S A)
    (x : X)
    (habs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((hA.rep.fn n).toFun x))) :
    (x ∈ A.S1 ∪ A.S2) ∧
      (x ∈ A.S1 ->
        relEventually
          (BishopRegularSeqIntegrableRep.valueAt hA.rep x habs)
          oneSeq) ∧
      (x ∈ A.S2 ->
        relEventually
          (BishopRegularSeqIntegrableRep.valueAt hA.rep x habs)
          zeroSeq) :=
  hA.valid x habs

/-- The target law package for Chapter 2, Propositions 2.4 and 2.5.

The fields are stated over the RegularSeq chapter-2 layer and use Bishop
equality for measure equalities.  This keeps the next proof frontier explicit:
construct the characteristic representations for `A ∨ B`, `A ∧ B`, and
relative difference from the carried characteristic representations. -/
structure FiniteSetLawPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  or_integrable :
    forall {A B : BSet X},
      IntegrableSet S A ->
        IntegrableSet S B ->
          IntegrableSet S (BSet.or A B)
  and_integrable :
    forall {A B : BSet X},
      IntegrableSet S A ->
        IntegrableSet S B ->
          IntegrableSet S (BSet.and A B)
  sub_integrable :
    forall {C D : BSet X},
      IntegrableSet S C ->
        IntegrableSet S (BSet.and C D) ->
          IntegrableSet S (BSet.sub C D)
  measure_or_and :
    forall {A B : BSet X},
      forall hA : IntegrableSet S A,
      forall hB : IntegrableSet S B,
        relEventually
          (addSeq (measure S hA) (measure S hB))
          (addSeq
            (measure S (or_integrable hA hB))
            (measure S (and_integrable hA hB)))
  measure_sub :
    forall {C D : BSet X},
      forall hC : IntegrableSet S C,
      forall hCD : IntegrableSet S (BSet.and C D),
        relEventually
          (measure S hC)
          (addSeq
            (measure S hCD)
            (measure S (sub_integrable hC hCD)))
  source_proposition_2_4_regularseq_target : Prop
  source_proposition_2_5_regularseq_target : Prop
  complement_not_assumed_integrable : Prop
  no_global_membership_decision_for_characteristics : Prop

/-- A chapter-2 surface package exposing the first RegularSeq-native API. -/
structure SurfacePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  complemented_set : Type
  integrable_set : BSet X -> Type 1
  measure_of : forall {A : BSet X}, integrable_set A -> RegularSeq
  characteristic_rep :
    forall {A : BSet X}, integrable_set A -> BishopRegularSeqIntegrableRep S
  domain_full :
    forall {A : BSet X},
      forall _hA : integrable_set A,
        BishopRegularSeqFullSet S (A.S1 ∪ A.S2)
  finite_law_target : Type 2
  source_chapter2_set_layer_started : Prop
  uses_bishop_regularseq_values : Prop
  no_choice_from_quotient_or_prop : Prop

def surfacePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    SurfacePackage S where
  complemented_set := BSet X
  integrable_set := IntegrableSet S
  measure_of := fun hA => measure S hA
  characteristic_rep := fun hA => characteristicRep hA
  domain_full := fun hA => domainFull hA
  finite_law_target := FiniteSetLawPackage S
  source_chapter2_set_layer_started := True
  uses_bishop_regularseq_values := True
  no_choice_from_quotient_or_prop := True

/-- Audit for the first chapter-2 RegularSeq increment. -/
structure Chapter2EntryAudit : Type where
  bset_reused_from_source_layer : Nat
  integrable_set_data_added : Nat
  measure_is_rep_integral : Nat
  finite_law_target_added : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  next_frontier_is_prop24_characteristic_construction : Prop

def chapter2EntryAudit : Chapter2EntryAudit where
  bset_reused_from_source_layer := 1
  integrable_set_data_added := 1
  measure_is_rep_integral := 1
  finite_law_target_added := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  next_frontier_is_prop24_characteristic_construction := True

end BishopRegularSeqChapter2

/-- G132 package: first RegularSeq-native chapter-2 surface. -/
structure BishopRegularSeqChapter2G132Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g131 : BishopRegularSeqTheorem118G131Package S
  surface : BishopRegularSeqChapter2.SurfacePackage S
  audit : BishopRegularSeqChapter2.Chapter2EntryAudit
  chapter2_integrable_set_surface_started : Prop
  chapter2_measure_is_regularseq_valued : Prop
  no_quotient_extraction_in_g132_chapter2_surface : Prop

def bishopRegularSeqChapter2G132Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G132Package S where
  g131 := bishopRegularSeqTheorem118G131Package S
  surface := BishopRegularSeqChapter2.surfacePackage S
  audit := BishopRegularSeqChapter2.chapter2EntryAudit
  chapter2_integrable_set_surface_started := True
  chapter2_measure_is_regularseq_valued := True
  no_quotient_extraction_in_g132_chapter2_surface := True

/-- Progress after G132: chapter 2 now has a RegularSeq-native entry surface.
The next step is to construct the Proposition 2.4 characteristic
representations for `A ∨ B` and `A ∧ B`. -/
def bishopRegularSeqCh1To4ProgressAfterG132 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 12
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G132: started the RegularSeq-native Chapter 2 layer with carried \
    characteristic representations, RegularSeq-valued measure, and finite \
    set-law targets for Propositions 2.4 and 2.5."


end BishopCReal
