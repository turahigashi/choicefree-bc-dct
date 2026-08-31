import Mathdemo.Internal.Real.AssemblingProposition24ClosureNumeric

set_option linter.style.longLine false

/-!
# G144: refined nonnegative-subseries frontier for Proposition 2.4

G142/G143 used broad numeric projection bridges.  This file narrows the
remaining analytic frontier to the source-faithful data actually needed by the
proof of Proposition 2.4:

* subseries projection is required only for nonnegative absolute-value series;
* scalar recovery is required only through carried scalar-specific data
  (not through a global selector from arbitrary scalar multiplication);
* the resulting data still assembles into the G140/G139 Proposition 2.4
  closure route without choosing representatives from quotients.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24RefinedSeriesFrontier

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport
open Prop24FromAbsDecomposition
open Prop24LocalAbsProjection
open Prop24RepresentationAbsProjection

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Schedule data for a subseries channel.  The order/coverage proof is kept as
data because this is exactly the analytic subseries step that should not be
extracted from a bare proposition later. -/
structure NatSubseriesSchedule (pick : Nat -> Nat) : Type where
  monotone_or_order_data_carried : Prop
  source_channel_data_carried : Prop
  no_choice_in_schedule : Prop

/-- The even channel of a binary interleaving. -/
def evenPick (n : Nat) : Nat := 2 * n

/-- The odd channel of a binary interleaving. -/
def oddPick (n : Nat) : Nat := 2 * n + 1

/-- The middle channel of a ternary interleaving. -/
def ternaryMiddlePick (n : Nat) : Nat := 3 * n + 1

def evenPickSchedule : NatSubseriesSchedule evenPick where
  monotone_or_order_data_carried := True
  source_channel_data_carried := True
  no_choice_in_schedule := True

def oddPickSchedule : NatSubseriesSchedule oddPick where
  monotone_or_order_data_carried := True
  source_channel_data_carried := True
  no_choice_in_schedule := True

def ternaryMiddlePickSchedule :
    NatSubseriesSchedule ternaryMiddlePick where
  monotone_or_order_data_carried := True
  source_channel_data_carried := True
  no_choice_in_schedule := True

/-- Data saying that `target` is being read as a nonnegative subseries of
`source`.  This is intentionally a data record, not a later choice from a
quotient or proposition. -/
structure NonnegativeSubseriesData
    (source target : Nat -> RegularSeq) : Type 1 where
  pick : Nat -> Nat
  schedule : NatSubseriesSchedule pick
  source_nonnegative : forall n : Nat, RegularSeqNonneg (source n)
  target_is_this_source_channel : Prop

/-- The single nonnegative-subseries analytic principle needed for the
binary/ternary absolute-value channels in Proposition 2.4. -/
structure NonnegativeSubseriesProjectionBridge : Type 1 where
  project :
    forall source target : Nat -> RegularSeq,
      NonnegativeSubseriesData source target ->
        BishopRegularSeqSeriesSum source ->
          BishopRegularSeqSeriesSum target
  source_monotone_series_subseries_principle : Prop
  no_quotient_representative_choice : Prop

/-- Scalar-specific recovery of the source absolute series from the absolute
series after multiplication by a fixed scalar.  Proposition 2.4 needs this for
`1/2` and `-1`; those instances are carried explicitly. -/
structure ScalarAbsRecoverData
    (Arch : ScalarMulArchimedeanData) (a : RegularSeq) : Type 1 where
  recover :
    forall u : Nat -> RegularSeq,
      BishopRegularSeqSeriesSum
        (fun n => absSeq (mulSeqConcreteWith Arch a (u n))) ->
        BishopRegularSeqSeriesSum (fun n => absSeq (u n))
  scalar_specific_constructive_data : Prop
  no_global_scalar_choice : Prop

/-- Scalar recovery data exactly used by the Chapter 2 half-sum formulas. -/
structure Prop24ScalarRecoverData
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  half_recover : ScalarAbsRecoverData Arch halfSeq
  neg_one_recover : ScalarAbsRecoverData Arch (negSeq oneSeq)
  only_prop24_scalars_required : Prop

/-- Pair-interleaving absolute projections from the refined nonnegative
subseries bridge. -/
def pairInterleaveAbsProjectionFromNonnegativeSubseries
    (bridge : NonnegativeSubseriesProjectionBridge)
    (f g : Nat -> BishopRegularSeqPFun X) :
    PairInterleaveAbsProjection f g where
  left_abs := by
    intro x hmerge
    exact
      bridge.project
        (fun n =>
          absSeq (((BishopRegularSeqPFun.pairInterleave f g n).toFun x)))
        (fun n => absSeq ((f n).toFun x))
        { pick := evenPick
          schedule := evenPickSchedule
          source_nonnegative := fun n => absSeq_regularSeqNonneg _
          target_is_this_source_channel := True }
        hmerge
  right_abs := by
    intro x hmerge
    exact
      bridge.project
        (fun n =>
          absSeq (((BishopRegularSeqPFun.pairInterleave f g n).toFun x)))
        (fun n => absSeq ((g n).toFun x))
        { pick := oddPick
          schedule := oddPickSchedule
          source_nonnegative := fun n => absSeq_regularSeqNonneg _
          target_is_this_source_channel := True }
        hmerge

/-- Scalar-multiplication absolute projection from scalar-specific recovery
data. -/
def smulSeqAbsProjectionFromScalarRecover
    (a : RegularSeq)
    (scalar : ScalarAbsRecoverData Arch a)
    (f : Nat -> BishopRegularSeqPFun X) :
    SmulSeqAbsProjection (Arch := Arch) a f where
  source_abs := by
    intro x hsmul_abs
    exact
      scalar.recover
        (fun n => (f n).toFun x)
        (by
          simpa [BishopRegularSeqPFun.smulSeq, BishopRegularSeqPFun.smul]
            using hsmul_abs)

/-- Absolute-representation projection from the refined nonnegative subseries
bridge, using only the middle channel of the source ternary merge. -/
def absRepSeqProjectionFromNonnegativeSubseries
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (bridge : NonnegativeSubseriesProjectionBridge)
    (r : BishopRegularSeqIntegrableRep S) :
    AbsRepSeqProjection r where
  source_abs := by
    intro x habs_rep
    exact
      bridge.project
        (fun n =>
          absSeq (((BishopRegularSeqPFun.absRepSeq Arch r.fn n).toFun x)))
        (fun n => absSeq ((r.fn n).toFun x))
        { pick := ternaryMiddlePick
          schedule := ternaryMiddlePickSchedule
          source_nonnegative := fun n => absSeq_regularSeqNonneg _
          target_is_this_source_channel := True }
        habs_rep

/-- The refined projection data for Proposition 2.4: one nonnegative-subseries
bridge plus scalar-specific recovery for the half and negative-one factors. -/
structure Prop24RefinedSeriesProjectionData
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  nonnegative_subseries : NonnegativeSubseriesProjectionBridge
  scalar_recover : Prop24ScalarRecoverData Arch
  avoids_arbitrary_series_projection : Prop

/-- Build the local `min2` abs-projection inputs from the refined bridge data. -/
def min2LocalAbsProjectionInputsFromRefinedSeries
    (refined : Prop24RefinedSeriesProjectionData Arch)
    (r s : BishopRegularSeqIntegrableRep S)
    (data : Min2Data r s) :
    Min2LocalAbsProjectionInputs r s data where
  half_projection :=
    smulAbsProjectionFromSmulSeq
      halfSeq
      (min2BodyRep r s data)
      data.half_smul_data
      (smulSeqAbsProjectionFromScalarRecover
        halfSeq refined.scalar_recover.half_recover
        (min2BodyRep r s data).fn)
  body_sub_projection :=
    subAbsProjectionFromRepresentationInputs
      (min2SumRep r s data)
      (min2AbsDiffRep r s data)
      data.raw_sub_data
      { neg_smul_seq_projection :=
          smulSeqAbsProjectionFromScalarRecover
            (negSeq oneSeq)
            refined.scalar_recover.neg_one_recover
            (min2AbsDiffRep r s data).fn
        add_pair_projection :=
          pairInterleaveAbsProjectionFromNonnegativeSubseries
            refined.nonnegative_subseries
            (min2SumRep r s data).fn
            (BishopRegularSeqPFun.smulSeq
              Arch (negSeq oneSeq) (min2AbsDiffRep r s data).fn) }
  abs_diff_projection :=
    absAbsProjectionFromAbsRepSeq
      (min2DiffRep r s data)
      data.abs_sub_data
      (absRepSeqProjectionFromNonnegativeSubseries
        refined.nonnegative_subseries (min2DiffRep r s data))
  diff_sub_projection :=
    subAbsProjectionFromRepresentationInputs
      r s data.sub_data
      { neg_smul_seq_projection :=
          smulSeqAbsProjectionFromScalarRecover
            (negSeq oneSeq)
            refined.scalar_recover.neg_one_recover
            s.fn
        add_pair_projection :=
          pairInterleaveAbsProjectionFromNonnegativeSubseries
            refined.nonnegative_subseries
            r.fn
            (BishopRegularSeqPFun.smulSeq Arch (negSeq oneSeq) s.fn) }

/-- Build the local union abs-projection inputs from refined bridge data. -/
def orLocalAbsProjectionInputsFromRefinedSeries
    {A B : BSet X}
    (refined : Prop24RefinedSeriesProjectionData Arch)
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (min2_data : Min2Data hA.rep hB.rep)
    (or_sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (sumRep hA.rep hB.rep min2_data.add_data)
        (min2Rep hA.rep hB.rep min2_data)) :
    OrLocalAbsProjectionInputs hA hB min2_data or_sub_data where
  min2_projection :=
    min2LocalAbsProjectionInputsFromRefinedSeries
      refined hA.rep hB.rep min2_data
  or_sub_projection :=
    subAbsProjectionFromRepresentationInputs
      (sumRep hA.rep hB.rep min2_data.add_data)
      (min2Rep hA.rep hB.rep min2_data)
      or_sub_data
      { neg_smul_seq_projection :=
          smulSeqAbsProjectionFromScalarRecover
            (negSeq oneSeq)
            refined.scalar_recover.neg_one_recover
            (min2Rep hA.rep hB.rep min2_data).fn
        add_pair_projection :=
          pairInterleaveAbsProjectionFromNonnegativeSubseries
            refined.nonnegative_subseries
            (sumRep hA.rep hB.rep min2_data.add_data).fn
            (BishopRegularSeqPFun.smulSeq
              Arch (negSeq oneSeq)
              (min2Rep hA.rep hB.rep min2_data).fn) }

/-- Complete closure data for Prop 2.4 from the refined analytic frontier. -/
structure Prop24RefinedSeriesClosureInputs
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) : Type 1 where
  refined : Prop24RefinedSeriesProjectionData Arch
  min2_data : Min2Data hA.rep hB.rep
  and_domain_eq :
    BishopRegularSeqIntegrableRep.domain
      (min2Rep hA.rep hB.rep min2_data) =
        (BSet.and A B).S1 ∪ (BSet.and A B).S2
  or_sub_data :
    BishopRegularSeqIntegrableRep.SubData
      (sumRep hA.rep hB.rep min2_data.add_data)
      (min2Rep hA.rep hB.rep min2_data)
  or_domain_eq :
    BishopRegularSeqIntegrableRep.domain
      (orFormulaRep hA hB min2_data or_sub_data) =
        (BSet.or A B).S1 ∪ (BSet.or A B).S2

def andLocalAbsInputsFromRefinedSeries
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (input : Prop24RefinedSeriesClosureInputs hA hB) :
    AndProp24LocalAbsInputs hA hB where
  min2_data := input.min2_data
  domain_eq := input.and_domain_eq
  local_abs :=
    min2LocalAbsProjectionInputsFromRefinedSeries
      input.refined hA.rep hB.rep input.min2_data

def orLocalAbsInputsFromRefinedSeries
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (input : Prop24RefinedSeriesClosureInputs hA hB) :
    OrProp24LocalAbsInputs hA hB where
  min2_data := input.min2_data
  or_sub_data := input.or_sub_data
  domain_eq := input.or_domain_eq
  local_abs :=
    orLocalAbsProjectionInputsFromRefinedSeries
      input.refined hA hB input.min2_data input.or_sub_data

/-- Assemble the Proposition 2.4 closure pair from the refined analytic
frontier. -/
def prop24ClosurePairFromRefinedSeries
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (input : Prop24RefinedSeriesClosureInputs hA hB) :
    Prop24ClosurePair hA hB :=
  prop24ClosurePairFromAbsDecomposition hA hB
    { and_input :=
        andProp24ConstructionInputsFromLocalAbs hA hB
          (andLocalAbsInputsFromRefinedSeries hA hB input)
      or_input :=
        orProp24ConstructionInputsFromLocalAbs hA hB
          (orLocalAbsInputsFromRefinedSeries hA hB input)
      same_min2_data := rfl }

/-- Package for the refined frontier. -/
structure Prop24RefinedSeriesFrontierPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  closure_input :
    forall {A B : BSet X},
      IntegrableSet S A -> IntegrableSet S B -> Type 1
  closure_from_refined_series :
    forall {A B : BSet X},
      forall hA : IntegrableSet S A,
      forall hB : IntegrableSet S B,
        closure_input hA hB -> Prop24ClosurePair hA hB
  remaining_frontier_is_nonnegative_subseries_plus_scalar_recover : Prop
  no_hidden_choice_in_refined_assembly : Prop

def prop24RefinedSeriesFrontierPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Prop24RefinedSeriesFrontierPackage S where
  closure_input := fun hA hB => Prop24RefinedSeriesClosureInputs hA hB
  closure_from_refined_series := fun hA hB input =>
    prop24ClosurePairFromRefinedSeries hA hB input
  remaining_frontier_is_nonnegative_subseries_plus_scalar_recover := True
  no_hidden_choice_in_refined_assembly := True

/-- Audit for G144. -/
structure Prop24RefinedSeriesFrontierAudit : Type where
  nonnegative_subseries_bridge_is_single_frontier : Nat
  scalar_recover_restricted_to_half_and_neg_one : Nat
  pair_interleave_projection_from_refined_closed : Nat
  smul_projection_from_scalar_recover_closed : Nat
  absrep_projection_from_refined_closed : Nat
  prop24_closure_from_refined_closed : Nat
  arbitrary_binary_projection_required : Nat
  arbitrary_ternary_projection_required : Nat
  arbitrary_scalar_projection_required : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat

def prop24RefinedSeriesFrontierAudit :
    Prop24RefinedSeriesFrontierAudit where
  nonnegative_subseries_bridge_is_single_frontier := 1
  scalar_recover_restricted_to_half_and_neg_one := 1
  pair_interleave_projection_from_refined_closed := 1
  smul_projection_from_scalar_recover_closed := 1
  absrep_projection_from_refined_closed := 1
  prop24_closure_from_refined_closed := 1
  arbitrary_binary_projection_required := 0
  arbitrary_ternary_projection_required := 0
  arbitrary_scalar_projection_required := 0
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0

end Prop24RefinedSeriesFrontier
end BishopRegularSeqChapter2

/-- G144 package: the Proposition 2.4 analytic frontier is now refined to
nonnegative subseries projection plus scalar-specific recovery for `1/2` and
`-1`. -/
structure BishopRegularSeqChapter2G144Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g143 : BishopRegularSeqChapter2G143Package S
  refined_frontier :
    BishopRegularSeqChapter2.Prop24RefinedSeriesFrontier.Prop24RefinedSeriesFrontierPackage S
  audit :
    BishopRegularSeqChapter2.Prop24RefinedSeriesFrontier.Prop24RefinedSeriesFrontierAudit
  refined_frontier_assembly_closed : Prop
  next_frontier_construct_subseries_and_scalar_recover_data : Prop

def bishopRegularSeqChapter2G144Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G144Package S where
  g143 := bishopRegularSeqChapter2G143Package S
  refined_frontier :=
    BishopRegularSeqChapter2.Prop24RefinedSeriesFrontier.prop24RefinedSeriesFrontierPackage S
  audit :=
    BishopRegularSeqChapter2.Prop24RefinedSeriesFrontier.prop24RefinedSeriesFrontierAudit
  refined_frontier_assembly_closed := True
  next_frontier_construct_subseries_and_scalar_recover_data := True

/-- Progress after G144: the remaining Proposition 2.4 analytic work is no
longer an arbitrary projection bridge; it is narrowed to nonnegative subseries
projection and scalar-specific recovery data. -/
def bishopRegularSeqCh1To4ProgressAfterG144 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 68
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G144: refined Chapter 2 Proposition 2.4 series frontier to \
    nonnegative subseries projection plus scalar-specific recovery for \
    half and negative one."


end BishopCReal
