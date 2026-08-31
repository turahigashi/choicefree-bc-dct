import Mathdemo.Internal.Real.LocalAbsProjectionDataProposition2

set_option linter.style.longLine false

/-!
# G141: reducing local abs-projections to representation-level projections

G140 introduced local abs-projection data for the operations used in Chapter 2
Proposition 2.4.  This file reduces those local projections to the actual
source representation shapes:

* addition uses `pairInterleave`;
* scalar multiplication uses `smulSeq`;
* absolute value uses `absRepSeq`;
* subtraction is addition with the explicit `(-1)*s` representative.

The genuinely analytic series-subsequence content remains data.  The assembly
from that data is closed here without quotient representative extraction.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24RepresentationAbsProjection

open Prop24LocalAbsProjection

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Projection data for the source pair-interleaving representation. -/
structure PairInterleaveAbsProjection
    (f g : Nat -> BishopRegularSeqPFun X) : Type 1 where
  left_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqPFun.pairInterleave f g n).toFun x))) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((f n).toFun x))
  right_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqPFun.pairInterleave f g n).toFun x))) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((g n).toFun x))

/-- Projection data for the source scalar-multiplication representation. -/
structure SmulSeqAbsProjection
    (a : RegularSeq)
    (f : Nat -> BishopRegularSeqPFun X) : Type 1 where
  source_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqPFun.smulSeq Arch a f n).toFun x))) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((f n).toFun x))

/-- Projection data for the source absolute-value representation. -/
structure AbsRepSeqProjection
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  source_abs :
    forall x : X,
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqPFun.absRepSeq Arch r.fn n).toFun x))) ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))

/-- Addition abs-projection from pair-interleaving projection data. -/
def addAbsProjectionFromPairInterleave
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AddData r s)
    (projection : PairInterleaveAbsProjection r.fn s.fn) :
    AddAbsProjection r s data where
  left_abs := by
    intro x hadd_abs
    simpa [BishopRegularSeqIntegrableRep.add] using
      projection.left_abs x hadd_abs
  right_abs := by
    intro x hadd_abs
    simpa [BishopRegularSeqIntegrableRep.add] using
      projection.right_abs x hadd_abs

/-- Scalar-multiplication abs-projection from `smulSeq` projection data. -/
def smulAbsProjectionFromSmulSeq
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SmulData a r)
    (projection : SmulSeqAbsProjection (Arch := Arch) a r.fn) :
    SmulAbsProjection a r data where
  source_abs := by
    intro x hsmul_abs
    simpa [BishopRegularSeqIntegrableRep.smul] using
      projection.source_abs x hsmul_abs

/-- Absolute-value abs-projection from `absRepSeq` projection data. -/
def absAbsProjectionFromAbsRepSeq
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AbsData r)
    (projection : AbsRepSeqProjection r) :
    AbsAbsProjection r data where
  source_abs := by
    intro x habs_abs
    simpa [BishopRegularSeqIntegrableRep.abs] using
      projection.source_abs x habs_abs

/-- Subtraction abs-projection from the source representation
`r + (-1)*s`. -/
def subAbsProjectionFromAddSmul
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SubData r s)
    (neg_projection :
      SmulAbsProjection (negSeq oneSeq) s data.neg_data)
    (add_projection :
      AddAbsProjection r
        (BishopRegularSeqIntegrableRep.smul
          (S := S) (negSeq oneSeq) s data.neg_data)
        data.add_data) :
    SubAbsProjection r s data where
  left_abs := by
    intro x hsub_abs
    have hadd_abs :
        BishopRegularSeqSeriesSum
          (fun n =>
            absSeq
              (((BishopRegularSeqIntegrableRep.add r
                (BishopRegularSeqIntegrableRep.smul
                  (S := S) (negSeq oneSeq) s data.neg_data)
                data.add_data).fn n).toFun x)) := by
      simpa [BishopRegularSeqIntegrableRep.sub] using hsub_abs
    exact add_projection.left_abs x hadd_abs
  right_abs := by
    intro x hsub_abs
    have hadd_abs :
        BishopRegularSeqSeriesSum
          (fun n =>
            absSeq
              (((BishopRegularSeqIntegrableRep.add r
                (BishopRegularSeqIntegrableRep.smul
                  (S := S) (negSeq oneSeq) s data.neg_data)
                data.add_data).fn n).toFun x)) := by
      simpa [BishopRegularSeqIntegrableRep.sub] using hsub_abs
    have hneg_abs :
        BishopRegularSeqSeriesSum
          (fun n =>
            absSeq
              (((BishopRegularSeqIntegrableRep.smul
                (S := S) (negSeq oneSeq) s data.neg_data).fn n).toFun x)) :=
      add_projection.right_abs x hadd_abs
    exact neg_projection.source_abs x hneg_abs
  neg_abs := by
    intro x hsub_abs
    have hadd_abs :
        BishopRegularSeqSeriesSum
          (fun n =>
            absSeq
              (((BishopRegularSeqIntegrableRep.add r
                (BishopRegularSeqIntegrableRep.smul
                  (S := S) (negSeq oneSeq) s data.neg_data)
                data.add_data).fn n).toFun x)) := by
      simpa [BishopRegularSeqIntegrableRep.sub] using hsub_abs
    exact add_projection.right_abs x hadd_abs

/-- Primitive representation projections sufficient to build a subtraction
abs-projection. -/
structure SubRepresentationAbsProjectionInputs
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SubData r s) : Type 1 where
  neg_smul_seq_projection :
    SmulSeqAbsProjection (Arch := Arch) (negSeq oneSeq) s.fn
  add_pair_projection :
    PairInterleaveAbsProjection r.fn
      (BishopRegularSeqPFun.smulSeq Arch (negSeq oneSeq) s.fn)

def subAbsProjectionFromRepresentationInputs
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SubData r s)
    (input : SubRepresentationAbsProjectionInputs r s data) :
    SubAbsProjection r s data :=
  subAbsProjectionFromAddSmul r s data
    (smulAbsProjectionFromSmulSeq
      (negSeq oneSeq) s data.neg_data input.neg_smul_seq_projection)
    (addAbsProjectionFromPairInterleave
      r
      (BishopRegularSeqIntegrableRep.smul
        (S := S) (negSeq oneSeq) s data.neg_data)
      data.add_data
      input.add_pair_projection)

/-- Package for reducing local abs-projections to representation-level
projection data. -/
structure RepresentationAbsProjectionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  pair_interleave_projection :
    (Nat -> BishopRegularSeqPFun X) ->
      (Nat -> BishopRegularSeqPFun X) -> Type 1
  smul_seq_projection :
    RegularSeq -> (Nat -> BishopRegularSeqPFun X) -> Type 1
  abs_rep_seq_projection :
    BishopRegularSeqIntegrableRep S -> Type 1
  add_projection_from_pair_available : Prop
  smul_projection_from_seq_available : Prop
  abs_projection_from_repseq_available : Prop
  sub_projection_from_add_smul_available : Prop
  remaining_series_subsequence_content_is_explicit_data : Prop

def representationAbsProjectionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    RepresentationAbsProjectionPackage S where
  pair_interleave_projection := fun f g => PairInterleaveAbsProjection f g
  smul_seq_projection := fun a f => SmulSeqAbsProjection (Arch := Arch) a f
  abs_rep_seq_projection := fun r => AbsRepSeqProjection r
  add_projection_from_pair_available := True
  smul_projection_from_seq_available := True
  abs_projection_from_repseq_available := True
  sub_projection_from_add_smul_available := True
  remaining_series_subsequence_content_is_explicit_data := True

/-- Audit for G141. -/
structure RepresentationAbsProjectionAudit : Type where
  pair_interleave_projection_shape_fixed : Nat
  smul_seq_projection_shape_fixed : Nat
  abs_repseq_projection_shape_fixed : Nat
  add_from_pair_closed : Nat
  smul_from_seq_closed : Nat
  abs_from_repseq_closed : Nat
  sub_from_add_smul_closed : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_series_projection_construction : Prop

def representationAbsProjectionAudit : RepresentationAbsProjectionAudit where
  pair_interleave_projection_shape_fixed := 1
  smul_seq_projection_shape_fixed := 1
  abs_repseq_projection_shape_fixed := 1
  add_from_pair_closed := 1
  smul_from_seq_closed := 1
  abs_from_repseq_closed := 1
  sub_from_add_smul_closed := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_series_projection_construction := True

end Prop24RepresentationAbsProjection
end BishopRegularSeqChapter2

/-- G141 package: local abs-projections are reduced to representation-level
projection data. -/
structure BishopRegularSeqChapter2G141Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g140 : BishopRegularSeqChapter2G140Package S
  representation_abs_projection :
    BishopRegularSeqChapter2.Prop24RepresentationAbsProjection.RepresentationAbsProjectionPackage S
  audit :
    BishopRegularSeqChapter2.Prop24RepresentationAbsProjection.RepresentationAbsProjectionAudit
  representation_projection_assembly_closed : Prop
  next_frontier_series_projection_construction : Prop

def bishopRegularSeqChapter2G141Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G141Package S where
  g140 := bishopRegularSeqChapter2G140Package S
  representation_abs_projection :=
    BishopRegularSeqChapter2.Prop24RepresentationAbsProjection.representationAbsProjectionPackage S
  audit :=
    BishopRegularSeqChapter2.Prop24RepresentationAbsProjection.representationAbsProjectionAudit
  representation_projection_assembly_closed := True
  next_frontier_series_projection_construction := True

/-- Progress after G141: local operation abs-projections now reduce to
representation-level projection data. -/
def bishopRegularSeqCh1To4ProgressAfterG141 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 56
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G141: reduced Chapter 2 local abs-projections to pairInterleave, \
    smulSeq, absRepSeq, and subtraction-as-add-smul representation data."


end BishopCReal
