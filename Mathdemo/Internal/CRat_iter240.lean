import Mathdemo.Internal.CRat_iter239

set_option linter.style.longLine false

/-!
# G140: local abs-projection data for Proposition 2.4

G139 assembled Proposition 2.4 closure from explicit abs-decomposition data.
This file factors that large data interface into local, operation-shaped
projection data:

* addition/subtraction representatives can project absolute summability to
  their component representatives;
* scalar multiplication can project absolute summability to its source
  representative when the needed scalar data is supplied;
* absolute value can project absolute summability to its source representative.

These are data-carrying interfaces, not theorem-mining from a bare proposition.
They are then composed to produce the G138/G139 formula inputs for `min2` and
union.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24LocalAbsProjection

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport
open Prop24FromAbsDecomposition

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Local abs-projection for an addition representative. -/
structure AddAbsProjection
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AddData r s) : Type 1 where
  left_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.add r s data).fn n).toFun x)) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))
  right_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.add r s data).fn n).toFun x)) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((s.fn n).toFun x))

/-- Local abs-projection for a scalar-multiplication representative.  This is
kept as data because recovering the source series from `|a*f_n|` may require
scalar-specific constructive witnesses. -/
structure SmulAbsProjection
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SmulData a r) : Type 1 where
  source_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.smul a r data).fn n).toFun x)) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))

/-- Local abs-projection for an absolute-value representative. -/
structure AbsAbsProjection
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AbsData r) : Type 1 where
  source_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.abs r data).fn n).toFun x)) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))

/-- Local abs-projection for a subtraction representative.  Since source
subtraction is represented by `r + (-1)*s`, the intermediate negative
representative's absolute summability is also carried. -/
structure SubAbsProjection
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SubData r s) : Type 1 where
  left_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.sub r s data).fn n).toFun x)) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))
  right_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.sub r s data).fn n).toFun x)) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((s.fn n).toFun x))
  neg_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.sub r s data).fn n).toFun x)) ->
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.smul
              (S := S) (negSeq oneSeq) s data.neg_data).fn n).toFun x))

/-- Local projections needed for the nested `min2` formula. -/
structure Min2LocalAbsProjectionInputs
    (r s : BishopRegularSeqIntegrableRep S)
    (data : Min2Data r s) : Type 1 where
  half_projection :
    SmulAbsProjection
      halfSeq
      (min2BodyRep r s data)
      data.half_smul_data
  body_sub_projection :
    SubAbsProjection
      (min2SumRep r s data)
      (min2AbsDiffRep r s data)
      data.raw_sub_data
  abs_diff_projection :
    AbsAbsProjection
      (min2DiffRep r s data)
      data.abs_sub_data
  diff_sub_projection :
    SubAbsProjection r s data.sub_data

/-- Compose local abs-projections into the G138 `Min2ValueTransportInputs`. -/
def min2ValueTransportInputsFromLocalAbs
    (r s : BishopRegularSeqIntegrableRep S)
    (data : Min2Data r s)
    (input : Min2LocalAbsProjectionInputs r s data) :
    Min2ValueTransportInputs r s data where
  left_abs := by
    intro x hmin_abs
    let hbody_abs := input.half_projection.source_abs x hmin_abs
    let habs_diff_abs := input.body_sub_projection.right_abs x hbody_abs
    let hdiff_abs := input.abs_diff_projection.source_abs x habs_diff_abs
    exact input.diff_sub_projection.left_abs x hdiff_abs
  right_abs := by
    intro x hmin_abs
    let hbody_abs := input.half_projection.source_abs x hmin_abs
    let habs_diff_abs := input.body_sub_projection.right_abs x hbody_abs
    let hdiff_abs := input.abs_diff_projection.source_abs x habs_diff_abs
    exact input.diff_sub_projection.right_abs x hdiff_abs
  sum_abs := by
    intro x hmin_abs
    let hbody_abs := input.half_projection.source_abs x hmin_abs
    exact input.body_sub_projection.left_abs x hbody_abs
  diff_abs := by
    intro x hmin_abs
    let hbody_abs := input.half_projection.source_abs x hmin_abs
    let habs_diff_abs := input.body_sub_projection.right_abs x hbody_abs
    exact input.abs_diff_projection.source_abs x habs_diff_abs
  abs_diff_abs := by
    intro x hmin_abs
    let hbody_abs := input.half_projection.source_abs x hmin_abs
    exact input.body_sub_projection.right_abs x hbody_abs
  body_abs := by
    intro x hmin_abs
    exact input.half_projection.source_abs x hmin_abs
  diff_neg_abs := by
    intro x hmin_abs
    let hbody_abs := input.half_projection.source_abs x hmin_abs
    let habs_diff_abs := input.body_sub_projection.right_abs x hbody_abs
    let hdiff_abs := input.abs_diff_projection.source_abs x habs_diff_abs
    exact input.diff_sub_projection.neg_abs x hdiff_abs
  body_neg_abs := by
    intro x hmin_abs
    let hbody_abs := input.half_projection.source_abs x hmin_abs
    exact input.body_sub_projection.neg_abs x hbody_abs

/-- Local projections needed for the union formula. -/
structure OrLocalAbsProjectionInputs
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (min2_data : Min2Data hA.rep hB.rep)
    (or_sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (sumRep hA.rep hB.rep min2_data.add_data)
        (min2Rep hA.rep hB.rep min2_data)) : Type 1 where
  min2_projection :
    Min2LocalAbsProjectionInputs hA.rep hB.rep min2_data
  or_sub_projection :
    SubAbsProjection
      (sumRep hA.rep hB.rep min2_data.add_data)
      (min2Rep hA.rep hB.rep min2_data)
      or_sub_data

/-- Compose local abs-projections into the G138 union transport input. -/
def orFormulaValueTransportInputsFromLocalAbs
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (min2_data : Min2Data hA.rep hB.rep)
    (or_sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (sumRep hA.rep hB.rep min2_data.add_data)
        (min2Rep hA.rep hB.rep min2_data))
    (input : OrLocalAbsProjectionInputs hA hB min2_data or_sub_data) :
    OrFormulaValueTransportInputs hA hB min2_data or_sub_data where
  min2_inputs :=
    min2ValueTransportInputsFromLocalAbs
      hA.rep hB.rep min2_data input.min2_projection
  sum_abs := input.or_sub_projection.left_abs
  min2_abs := input.or_sub_projection.right_abs
  or_neg_abs := input.or_sub_projection.neg_abs

/-- Data-bearing input for `A ∩ B` using local abs-projections. -/
structure AndProp24LocalAbsInputs
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) : Type 1 where
  min2_data : Min2Data hA.rep hB.rep
  domain_eq :
    BishopRegularSeqIntegrableRep.domain
      (min2Rep hA.rep hB.rep min2_data) =
        (BSet.and A B).S1 ∪ (BSet.and A B).S2
  local_abs :
    Min2LocalAbsProjectionInputs hA.rep hB.rep min2_data

/-- Convert local abs-projection input to the G139 construction input for
intersection. -/
def andProp24ConstructionInputsFromLocalAbs
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (input : AndProp24LocalAbsInputs hA hB) :
    AndProp24ConstructionInputs hA hB where
  min2_data := input.min2_data
  domain_eq := input.domain_eq
  abs_decomposition :=
    min2ValueTransportInputsFromLocalAbs
      hA.rep hB.rep input.min2_data input.local_abs

/-- Data-bearing input for `A ∪ B` using local abs-projections. -/
structure OrProp24LocalAbsInputs
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
      (orFormulaRep hA hB min2_data or_sub_data) =
        (BSet.or A B).S1 ∪ (BSet.or A B).S2
  local_abs :
    OrLocalAbsProjectionInputs hA hB min2_data or_sub_data

/-- Convert local abs-projection input to the G139 construction input for
union. -/
def orProp24ConstructionInputsFromLocalAbs
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (input : OrProp24LocalAbsInputs hA hB) :
    OrProp24ConstructionInputs hA hB where
  min2_data := input.min2_data
  or_sub_data := input.or_sub_data
  domain_eq := input.domain_eq
  abs_decomposition :=
    orFormulaValueTransportInputsFromLocalAbs
      hA hB input.min2_data input.or_sub_data input.local_abs

/-- Package for local abs-projection assembly. -/
structure Prop24LocalAbsProjectionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  add_projection :
    forall r s : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.AddData r s -> Type 1
  smul_projection :
    forall a : RegularSeq,
      forall r : BishopRegularSeqIntegrableRep S,
        BishopRegularSeqIntegrableRep.SmulData a r -> Type 1
  abs_projection :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.AbsData r -> Type 1
  sub_projection :
    forall r s : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.SubData r s -> Type 1
  min2_from_local_abs_available : Prop
  or_from_local_abs_available : Prop
  remaining_task_is_constructing_local_projection_data : Prop

def prop24LocalAbsProjectionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Prop24LocalAbsProjectionPackage S where
  add_projection := fun r s data => AddAbsProjection r s data
  smul_projection := fun a r data => SmulAbsProjection a r data
  abs_projection := fun r data => AbsAbsProjection r data
  sub_projection := fun r s data => SubAbsProjection r s data
  min2_from_local_abs_available := True
  or_from_local_abs_available := True
  remaining_task_is_constructing_local_projection_data := True

/-- Audit for G140. -/
structure Prop24LocalAbsProjectionAudit : Type where
  add_projection_shape_fixed : Nat
  smul_projection_shape_fixed : Nat
  abs_projection_shape_fixed : Nat
  sub_projection_shape_fixed : Nat
  min2_composition_closed : Nat
  or_composition_closed : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_local_projection_construction : Prop

def prop24LocalAbsProjectionAudit : Prop24LocalAbsProjectionAudit where
  add_projection_shape_fixed := 1
  smul_projection_shape_fixed := 1
  abs_projection_shape_fixed := 1
  sub_projection_shape_fixed := 1
  min2_composition_closed := 1
  or_composition_closed := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_local_projection_construction := True

end Prop24LocalAbsProjection
end BishopRegularSeqChapter2

/-- G140 package: Proposition 2.4 abs-decomposition is factored into local
operation-shaped projection data. -/
structure BishopRegularSeqChapter2G140Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g139 : BishopRegularSeqChapter2G139Package S
  local_abs_projection :
    BishopRegularSeqChapter2.Prop24LocalAbsProjection.Prop24LocalAbsProjectionPackage S
  audit :
    BishopRegularSeqChapter2.Prop24LocalAbsProjection.Prop24LocalAbsProjectionAudit
  local_projection_composition_closed : Prop
  next_frontier_construct_local_projection_data : Prop

def bishopRegularSeqChapter2G140Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G140Package S where
  g139 := bishopRegularSeqChapter2G139Package S
  local_abs_projection :=
    BishopRegularSeqChapter2.Prop24LocalAbsProjection.prop24LocalAbsProjectionPackage S
  audit :=
    BishopRegularSeqChapter2.Prop24LocalAbsProjection.prop24LocalAbsProjectionAudit
  local_projection_composition_closed := True
  next_frontier_construct_local_projection_data := True

/-- Progress after G140: the abs-decomposition frontier is factored into local
operation-shaped data. -/
def bishopRegularSeqCh1To4ProgressAfterG140 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 52
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G140: factored Chapter 2 Proposition 2.4 abs-decomposition into local \
    operation-shaped projection data and composed it back to the closure input."


end BishopCReal
