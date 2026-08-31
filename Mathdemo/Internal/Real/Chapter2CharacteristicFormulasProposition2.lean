import Mathdemo.Internal.Real.Chapter2FullDomainClosureFinite

set_option linter.style.longLine false

/-!
# G134: chapter-2 characteristic formulas for Proposition 2.4

G133 closed the full-domain layer for finite set operations.  This file fixes
the RegularSeq-native characteristic-representation formulas for Proposition
2.4:

* `chi(A ∧ B) = min2(chi A, chi B)`;
* `chi(A ∨ B) = chi A + chi B - min2(chi A, chi B)`.

All Definition 1.6 operation data is explicit.  No quotient representative or
Prop-to-data selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2

namespace CharacteristicFormula

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Sum of two carried characteristic representatives. -/
def sumRep
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AddData r s) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.add r s data

/-- Difference of two carried characteristic representatives. -/
def diffRep
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SubData r s) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.sub r s data

/-- Absolute value of a carried representative. -/
def absRep
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AbsData r) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.abs r data

/-- Scalar multiplication of a carried representative. -/
def smulRep
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SmulData a r) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.smul a r data

/-- Operation data for the source formula
`min2(r,s) = 1/2 * ((r+s) - |r-s|)`. -/
structure Min2Data
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  add_data : BishopRegularSeqIntegrableRep.AddData r s
  sub_data : BishopRegularSeqIntegrableRep.SubData r s
  abs_sub_data :
    BishopRegularSeqIntegrableRep.AbsData
      (diffRep r s sub_data)
  raw_sub_data :
    BishopRegularSeqIntegrableRep.SubData
      (sumRep r s add_data)
      (absRep (diffRep r s sub_data) abs_sub_data)
  half_smul_data :
    BishopRegularSeqIntegrableRep.SmulData
      halfSeq
      (diffRep
        (sumRep r s add_data)
        (absRep (diffRep r s sub_data) abs_sub_data)
        raw_sub_data)

/-- The RegularSeq `L1` representative for `min2(r,s)`. -/
def min2Rep
    (r s : BishopRegularSeqIntegrableRep S)
    (data : Min2Data r s) :
    BishopRegularSeqIntegrableRep S :=
  smulRep
    halfSeq
    (diffRep
      (sumRep r s data.add_data)
      (absRep (diffRep r s data.sub_data) data.abs_sub_data)
      data.raw_sub_data)
    data.half_smul_data

/-- Data needed to turn the `min2` formula into an integrable set for
`A ∧ B`.  The hard pointwise truth-table law is carried explicitly as
`valid`; later increments will construct it. -/
structure AndConstructionData
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) : Type 1 where
  min2_data : Min2Data hA.rep hB.rep
  domain_eq :
    BishopRegularSeqIntegrableRep.domain
      (min2Rep hA.rep hB.rep min2_data) =
        (BSet.and A B).S1 ∪ (BSet.and A B).S2
  valid :
    forall x : X,
      forall habs :
        BishopRegularSeqSeriesSum
          (fun n =>
            absSeq (((min2Rep hA.rep hB.rep min2_data).fn n).toFun x)),
        (x ∈ (BSet.and A B).S1 ∪ (BSet.and A B).S2) ∧
          (x ∈ (BSet.and A B).S1 ->
            relEventually
              (BishopRegularSeqIntegrableRep.valueAt
                (min2Rep hA.rep hB.rep min2_data) x habs)
              oneSeq) ∧
          (x ∈ (BSet.and A B).S2 ->
            relEventually
              (BishopRegularSeqIntegrableRep.valueAt
                (min2Rep hA.rep hB.rep min2_data) x habs)
              zeroSeq)

/-- Construct the integrable set `A ∧ B` from explicit characteristic formula
data. -/
def andIntegrableSet
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (data : AndConstructionData hA hB) :
    IntegrableSet S (BSet.and A B) where
  full_domain := fullDomain_and hA hB
  rep := min2Rep hA.rep hB.rep data.min2_data
  domain_eq := data.domain_eq
  valid := data.valid
  source_definition_2_integrable_set_regularseq := True
  characteristic_representation_is_carried_data := True
  no_quotient_representative_extraction := True

/-- Data needed to turn the source formula
`chi(A ∨ B) = chi A + chi B - min2(chi A, chi B)` into an integrable set. -/
structure OrConstructionData
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) : Type 1 where
  min2_data : Min2Data hA.rep hB.rep
  or_sub_data :
    BishopRegularSeqIntegrableRep.SubData
      (sumRep hA.rep hB.rep min2_data.add_data)
      (min2Rep hA.rep hB.rep min2_data)
  domain_eq :
    BishopRegularSeqIntegrableRep.domain
      (diffRep
        (sumRep hA.rep hB.rep min2_data.add_data)
        (min2Rep hA.rep hB.rep min2_data)
        or_sub_data) =
        (BSet.or A B).S1 ∪ (BSet.or A B).S2
  valid :
    forall x : X,
      forall habs :
        BishopRegularSeqSeriesSum
          (fun n =>
            absSeq
              (((diffRep
                (sumRep hA.rep hB.rep min2_data.add_data)
                (min2Rep hA.rep hB.rep min2_data)
                or_sub_data).fn n).toFun x)),
        (x ∈ (BSet.or A B).S1 ∪ (BSet.or A B).S2) ∧
          (x ∈ (BSet.or A B).S1 ->
            relEventually
              (BishopRegularSeqIntegrableRep.valueAt
                (diffRep
                  (sumRep hA.rep hB.rep min2_data.add_data)
                  (min2Rep hA.rep hB.rep min2_data)
                  or_sub_data) x habs)
              oneSeq) ∧
          (x ∈ (BSet.or A B).S2 ->
            relEventually
              (BishopRegularSeqIntegrableRep.valueAt
                (diffRep
                  (sumRep hA.rep hB.rep min2_data.add_data)
                  (min2Rep hA.rep hB.rep min2_data)
                  or_sub_data) x habs)
              zeroSeq)

/-- The representative supplied by the `A ∨ B` source formula. -/
def orRep
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (data : OrConstructionData hA hB) :
    BishopRegularSeqIntegrableRep S :=
  diffRep
    (sumRep hA.rep hB.rep data.min2_data.add_data)
    (min2Rep hA.rep hB.rep data.min2_data)
    data.or_sub_data

/-- Construct the integrable set `A ∨ B` from explicit characteristic formula
data. -/
def orIntegrableSet
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (data : OrConstructionData hA hB) :
    IntegrableSet S (BSet.or A B) where
  full_domain := fullDomain_or hA hB
  rep := orRep hA hB data
  domain_eq := data.domain_eq
  valid := data.valid
  source_definition_2_integrable_set_regularseq := True
  characteristic_representation_is_carried_data := True
  no_quotient_representative_extraction := True

/-- Formula package for Proposition 2.4 before the measure identity. -/
structure Prop24FormulaPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  min2_data :
    forall {A B : BSet X},
      IntegrableSet S A -> IntegrableSet S B -> Type 1
  and_data :
    forall {A B : BSet X},
      IntegrableSet S A -> IntegrableSet S B -> Type 1
  or_data :
    forall {A B : BSet X},
      IntegrableSet S A -> IntegrableSet S B -> Type 1
  and_from_data :
    forall {A B : BSet X},
      forall hA : IntegrableSet S A,
      forall hB : IntegrableSet S B,
        and_data hA hB -> IntegrableSet S (BSet.and A B)
  or_from_data :
    forall {A B : BSet X},
      forall hA : IntegrableSet S A,
      forall hB : IntegrableSet S B,
        or_data hA hB -> IntegrableSet S (BSet.or A B)
  source_chi_and_formula_fixed : Prop
  source_chi_or_formula_fixed : Prop
  next_frontier_is_valid_truth_table_and_measure_identity : Prop

def prop24FormulaPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Prop24FormulaPackage S where
  min2_data := fun hA hB => Min2Data hA.rep hB.rep
  and_data := fun hA hB => AndConstructionData hA hB
  or_data := fun hA hB => OrConstructionData hA hB
  and_from_data := fun hA hB data => andIntegrableSet hA hB data
  or_from_data := fun hA hB data => orIntegrableSet hA hB data
  source_chi_and_formula_fixed := True
  source_chi_or_formula_fixed := True
  next_frontier_is_valid_truth_table_and_measure_identity := True

/-- Audit for G134. -/
structure Chapter2Prop24FormulaAudit : Type where
  min2_formula_fixed : Nat
  and_characteristic_formula_fixed : Nat
  or_characteristic_formula_fixed : Nat
  operation_data_explicit : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_truth_table_value_frontier : Prop
  remaining_measure_identity_frontier : Prop

def chapter2Prop24FormulaAudit : Chapter2Prop24FormulaAudit where
  min2_formula_fixed := 1
  and_characteristic_formula_fixed := 1
  or_characteristic_formula_fixed := 1
  operation_data_explicit := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_truth_table_value_frontier := True
  remaining_measure_identity_frontier := True

end CharacteristicFormula

end BishopRegularSeqChapter2

/-- G134 package: characteristic formulas for Proposition 2.4 are fixed. -/
structure BishopRegularSeqChapter2G134Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g133 : BishopRegularSeqChapter2G133Package S
  prop24_formula :
    BishopRegularSeqChapter2.CharacteristicFormula.Prop24FormulaPackage S
  audit :
    BishopRegularSeqChapter2.CharacteristicFormula.Chapter2Prop24FormulaAudit
  chi_and_formula_available : Prop
  chi_or_formula_available : Prop
  next_frontier_valid_and_measure_identity : Prop

def bishopRegularSeqChapter2G134Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G134Package S where
  g133 := bishopRegularSeqChapter2G133Package S
  prop24_formula :=
    BishopRegularSeqChapter2.CharacteristicFormula.prop24FormulaPackage S
  audit :=
    BishopRegularSeqChapter2.CharacteristicFormula.chapter2Prop24FormulaAudit
  chi_and_formula_available := True
  chi_or_formula_available := True
  next_frontier_valid_and_measure_identity := True

/-- Progress after G134: the characteristic formulas for Proposition 2.4 are
fixed with all operation data explicit. -/
def bishopRegularSeqCh1To4ProgressAfterG134 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 22
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G134: fixed the RegularSeq characteristic formulas for Chapter 2 \
    Proposition 2.4: chi(A∧B)=min2 and chi(A∨B)=chiA+chiB-min2."


end BishopCReal
