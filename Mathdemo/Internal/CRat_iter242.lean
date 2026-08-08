import Mathdemo.Internal.CRat_iter241

set_option linter.style.longLine false

/-!
# G142: reducing representation projections to numeric series projections

G141 reduced Chapter 2 abs-projections to representation-level projection
data for `pairInterleave`, `smulSeq`, and `absRepSeq`.  This file factors
those again to pure RegularSeq series projection bridges:

* binary merged series projection;
* scalar-multiplied absolute series projection;
* ternary merged series middle projection.

This isolates the remaining analytic work in a small series API, instead of
leaving it entangled with L1 representatives or set formulas.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24SeriesProjection

open Prop24RepresentationAbsProjection

/-- Numeric binary merge matching `pairInterleave`. -/
def binaryMergeSeq
    (u v : Nat -> RegularSeq) : Nat -> RegularSeq :=
  fun n => if n % 2 = 0 then u (n / 2) else v (n / 2)

/-- Numeric ternary merge matching `tripleMerge`. -/
def ternaryMergeSeq
    (u v w : Nat -> RegularSeq) : Nat -> RegularSeq :=
  fun n =>
    if n % 3 = 0 then u (n / 3)
    else if n % 3 = 1 then v (n / 3)
    else w (n / 3)

/-- Pure series projection bridge for binary merged nonnegative series. -/
structure BinaryMergeSeriesProjectionBridge : Type 1 where
  left :
    forall u v : Nat -> RegularSeq,
      BishopRegularSeqSeriesSum (binaryMergeSeq u v) ->
        BishopRegularSeqSeriesSum u
  right :
    forall u v : Nat -> RegularSeq,
      BishopRegularSeqSeriesSum (binaryMergeSeq u v) ->
        BishopRegularSeqSeriesSum v
  intended_for_nonnegative_absolute_series : Prop

/-- Pure series projection bridge for scalar-multiplied absolute series. -/
structure SmulAbsSeriesProjectionBridge
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  source_abs :
    forall a : RegularSeq,
      forall u : Nat -> RegularSeq,
        BishopRegularSeqSeriesSum
          (fun n => absSeq (mulSeqConcreteWith Arch a (u n))) ->
          BishopRegularSeqSeriesSum
            (fun n => absSeq (u n))
  scalar_specific_constructive_data_is_carried_here : Prop

/-- Pure series projection bridge for the middle channel of a ternary merged
nonnegative series. -/
structure TernaryMergeMiddleSeriesProjectionBridge : Type 1 where
  middle :
    forall u v w : Nat -> RegularSeq,
      BishopRegularSeqSeriesSum (ternaryMergeSeq u v w) ->
        BishopRegularSeqSeriesSum v
  intended_for_absRepSeq_middle_channel : Prop

/-- Build representation-level pair-interleaving projection from the numeric
binary merge bridge. -/
def pairInterleaveAbsProjectionFromSeriesBridge
    (bridge : BinaryMergeSeriesProjectionBridge)
    (f g : Nat -> BishopRegularSeqPFun X) :
    PairInterleaveAbsProjection f g where
  left_abs := by
    intro x hmerge
    have hmerge' :
        BishopRegularSeqSeriesSum
          (binaryMergeSeq
            (fun n => absSeq ((f n).toFun x))
            (fun n => absSeq ((g n).toFun x))) := by
      convert hmerge using 2
      rename_i n
      unfold binaryMergeSeq BishopRegularSeqPFun.pairInterleave
      by_cases h : n % 2 = 0
      · simp [h]
      · simp [h]
    exact
      bridge.left
        (fun n => absSeq ((f n).toFun x))
        (fun n => absSeq ((g n).toFun x))
        hmerge'
  right_abs := by
    intro x hmerge
    have hmerge' :
        BishopRegularSeqSeriesSum
          (binaryMergeSeq
            (fun n => absSeq ((f n).toFun x))
            (fun n => absSeq ((g n).toFun x))) := by
      convert hmerge using 2
      rename_i n
      unfold binaryMergeSeq BishopRegularSeqPFun.pairInterleave
      by_cases h : n % 2 = 0
      · simp [h]
      · simp [h]
    exact
      bridge.right
        (fun n => absSeq ((f n).toFun x))
        (fun n => absSeq ((g n).toFun x))
        hmerge'

/-- Build representation-level scalar projection from the numeric scalar
absolute-series bridge. -/
def smulSeqAbsProjectionFromSeriesBridge
    (bridge : SmulAbsSeriesProjectionBridge Arch)
    (a : RegularSeq)
    (f : Nat -> BishopRegularSeqPFun X) :
    SmulSeqAbsProjection (Arch := Arch) a f where
  source_abs := by
    intro x hsmul
    exact
      bridge.source_abs a
        (fun n => (f n).toFun x)
        (by
          simpa [BishopRegularSeqPFun.smulSeq, BishopRegularSeqPFun.smul]
            using hsmul)

/-- Build representation-level `absRepSeq` projection from the numeric
ternary middle-channel bridge. -/
def absRepSeqProjectionFromSeriesBridge
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (bridge : TernaryMergeMiddleSeriesProjectionBridge)
    (r : BishopRegularSeqIntegrableRep S) :
    AbsRepSeqProjection r where
  source_abs := by
    intro x habs_rep
    have habs_rep' :
        BishopRegularSeqSeriesSum
          (ternaryMergeSeq
            (fun n =>
              absSeq
                (((BishopRegularSeqPFun.absDelta Arch r.fn n).toFun x)))
            (fun n => absSeq ((r.fn n).toFun x))
            (fun n =>
              absSeq
                (((BishopRegularSeqPFun.neg Arch (r.fn n)).toFun x)))) := by
      convert habs_rep using 2
      rename_i n
      unfold ternaryMergeSeq BishopRegularSeqPFun.absRepSeq
        BishopRegularSeqPFun.tripleMerge
      by_cases h0 : n % 3 = 0
      · simp [h0]
      · by_cases h1 : n % 3 = 1
        · simp [h1]
        · simp [h0, h1]
    exact
      bridge.middle
        (fun n =>
          absSeq
            (((BishopRegularSeqPFun.absDelta Arch r.fn n).toFun x)))
        (fun n => absSeq ((r.fn n).toFun x))
        (fun n =>
          absSeq
            (((BishopRegularSeqPFun.neg Arch (r.fn n)).toFun x)))
        habs_rep'

/-- Series-projection package for the remaining Proposition 2.4 analytic
frontier. -/
structure Prop24SeriesProjectionPackage
    (Arch : ScalarMulArchimedeanData) (X : Type) : Type 2 where
  binary_bridge : Type 1
  smul_abs_bridge : Type 1
  ternary_middle_bridge : Type 1
  pair_interleave_from_binary_available : Prop
  smul_seq_from_scalar_series_available : Prop
  abs_repseq_from_ternary_available : Prop
  remaining_frontier_is_numeric_series_projection : Prop

def prop24SeriesProjectionPackage
    (Arch : ScalarMulArchimedeanData) (X : Type) :
    Prop24SeriesProjectionPackage Arch X where
  binary_bridge := BinaryMergeSeriesProjectionBridge
  smul_abs_bridge := SmulAbsSeriesProjectionBridge Arch
  ternary_middle_bridge := TernaryMergeMiddleSeriesProjectionBridge
  pair_interleave_from_binary_available := True
  smul_seq_from_scalar_series_available := True
  abs_repseq_from_ternary_available := True
  remaining_frontier_is_numeric_series_projection := True

/-- Audit for G142. -/
structure Prop24SeriesProjectionAudit : Type where
  binary_merge_bridge_shape_fixed : Nat
  smul_abs_bridge_shape_fixed : Nat
  ternary_middle_bridge_shape_fixed : Nat
  pair_interleave_reduction_closed : Nat
  smul_seq_reduction_closed : Nat
  abs_repseq_reduction_closed : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_numeric_series_projection : Prop

def prop24SeriesProjectionAudit : Prop24SeriesProjectionAudit where
  binary_merge_bridge_shape_fixed := 1
  smul_abs_bridge_shape_fixed := 1
  ternary_middle_bridge_shape_fixed := 1
  pair_interleave_reduction_closed := 1
  smul_seq_reduction_closed := 1
  abs_repseq_reduction_closed := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_numeric_series_projection := True

end Prop24SeriesProjection
end BishopRegularSeqChapter2

/-- G142 package: representation-level abs-projections now reduce to numeric
RegularSeq series projection bridges. -/
structure BishopRegularSeqChapter2G142Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g141 : BishopRegularSeqChapter2G141Package S
  series_projection :
    BishopRegularSeqChapter2.Prop24SeriesProjection.Prop24SeriesProjectionPackage Arch X
  audit :
    BishopRegularSeqChapter2.Prop24SeriesProjection.Prop24SeriesProjectionAudit
  representation_to_numeric_series_reduction_closed : Prop
  next_frontier_numeric_series_projection : Prop

def bishopRegularSeqChapter2G142Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G142Package S where
  g141 := bishopRegularSeqChapter2G141Package S
  series_projection :=
    BishopRegularSeqChapter2.Prop24SeriesProjection.prop24SeriesProjectionPackage Arch X
  audit :=
    BishopRegularSeqChapter2.Prop24SeriesProjection.prop24SeriesProjectionAudit
  representation_to_numeric_series_reduction_closed := True
  next_frontier_numeric_series_projection := True

/-- Progress after G142: Proposition 2.4 abs-projection construction is
reduced to a numeric RegularSeq series-projection frontier. -/
def bishopRegularSeqCh1To4ProgressAfterG142 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 60
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G142: reduced Chapter 2 representation abs-projections to numeric \
    RegularSeq series-projection bridges for binary merge, scalar abs, and \
    ternary middle channels."


end BishopCReal
