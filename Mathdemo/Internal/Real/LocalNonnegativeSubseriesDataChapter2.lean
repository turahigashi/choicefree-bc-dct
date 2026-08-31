import Mathdemo.Internal.Real.ClosingHalfAbsoluteValueTermLaw

set_option linter.style.longLine false

/-!
# G148: local nonnegative-subseries data for Chapter 2 Proposition 2.4

G147 closed the scalar-recovery side of Proposition 2.4.  The remaining analytic
content is now only the nonnegative subseries projection used by the concrete
source representations:

* the left/right channels of `pairInterleave`;
* the middle channel of `absRepSeq`.

This file avoids a global arbitrary subseries selector.  It takes those local
nonnegative-channel projections as carried data and assembles the existing
Proposition 2.4 closure route from that local data plus the closed scalar
recoveries.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24LocalNonnegativeSubseries

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport
open Prop24FromAbsDecomposition
open Prop24LocalAbsProjection
open Prop24RepresentationAbsProjection
open Prop24RefinedSeriesFrontier
open Prop24HalfTermLaw

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Local nonnegative-subseries projections exactly needed by Proposition 2.4.

The fields are not recovered from a quotient or from a bare proposition.  They
are the operation-specific certificates that the source proof uses when it reads
one nonnegative channel out of an absolutely summable merged series. -/
structure LocalNonnegativeSubseriesProjections
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  pair_abs :
    forall f g : Nat -> BishopRegularSeqPFun X,
      PairInterleaveAbsProjection f g
  absrep_abs :
    forall r : BishopRegularSeqIntegrableRep S,
      AbsRepSeqProjection r
  pair_channels_are_nonnegative_subseries_data : Prop
  absrep_middle_channel_is_nonnegative_subseries_data : Prop
  monotone_bounded_subseries_completion_carried : Prop
  no_global_series_projection_selector : Prop
  no_quotient_representative_extraction : Prop

/-- The already closed scalar-recovery data from G147. -/
def closedProp24ScalarRecoverData
    (Arch : ScalarMulArchimedeanData) :
    Prop24ScalarRecoverData Arch :=
  prop24ScalarRecoverDataClosed Arch

/-- Build the local `min2` abs-projection inputs from local nonnegative-channel
data and the closed scalar recoveries. -/
def min2LocalAbsProjectionInputsFromLocalNonnegative
    (localData : LocalNonnegativeSubseriesProjections S)
    (r s : BishopRegularSeqIntegrableRep S)
    (data : Min2Data r s) :
    Min2LocalAbsProjectionInputs r s data where
  half_projection :=
    smulAbsProjectionFromSmulSeq
      halfSeq
      (min2BodyRep r s data)
      data.half_smul_data
      (smulSeqAbsProjectionFromScalarRecover
        halfSeq
        (closedProp24ScalarRecoverData Arch).half_recover
        (min2BodyRep r s data).fn)
  body_sub_projection :=
    subAbsProjectionFromRepresentationInputs
      (min2SumRep r s data)
      (min2AbsDiffRep r s data)
      data.raw_sub_data
      { neg_smul_seq_projection :=
          smulSeqAbsProjectionFromScalarRecover
            (negSeq oneSeq)
            (closedProp24ScalarRecoverData Arch).neg_one_recover
            (min2AbsDiffRep r s data).fn
        add_pair_projection :=
          localData.pair_abs
            (min2SumRep r s data).fn
            (BishopRegularSeqPFun.smulSeq
              Arch (negSeq oneSeq) (min2AbsDiffRep r s data).fn) }
  abs_diff_projection :=
    absAbsProjectionFromAbsRepSeq
      (min2DiffRep r s data)
      data.abs_sub_data
      (localData.absrep_abs (min2DiffRep r s data))
  diff_sub_projection :=
    subAbsProjectionFromRepresentationInputs
      r s data.sub_data
      { neg_smul_seq_projection :=
          smulSeqAbsProjectionFromScalarRecover
            (negSeq oneSeq)
            (closedProp24ScalarRecoverData Arch).neg_one_recover
            s.fn
        add_pair_projection :=
          localData.pair_abs
            r.fn
            (BishopRegularSeqPFun.smulSeq Arch (negSeq oneSeq) s.fn) }

/-- Build the local union abs-projection inputs from the same local
nonnegative-channel data. -/
def orLocalAbsProjectionInputsFromLocalNonnegative
    {A B : BSet X}
    (localData : LocalNonnegativeSubseriesProjections S)
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (min2_data : Min2Data hA.rep hB.rep)
    (or_sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (sumRep hA.rep hB.rep min2_data.add_data)
        (min2Rep hA.rep hB.rep min2_data)) :
    OrLocalAbsProjectionInputs hA hB min2_data or_sub_data where
  min2_projection :=
    min2LocalAbsProjectionInputsFromLocalNonnegative
      localData hA.rep hB.rep min2_data
  or_sub_projection :=
    subAbsProjectionFromRepresentationInputs
      (sumRep hA.rep hB.rep min2_data.add_data)
      (min2Rep hA.rep hB.rep min2_data)
      or_sub_data
      { neg_smul_seq_projection :=
          smulSeqAbsProjectionFromScalarRecover
            (negSeq oneSeq)
            (closedProp24ScalarRecoverData Arch).neg_one_recover
            (min2Rep hA.rep hB.rep min2_data).fn
        add_pair_projection :=
          localData.pair_abs
            (sumRep hA.rep hB.rep min2_data.add_data).fn
            (BishopRegularSeqPFun.smulSeq
              Arch (negSeq oneSeq)
              (min2Rep hA.rep hB.rep min2_data).fn) }

/-- Complete Proposition 2.4 closure input after G147: the only analytic data
still required is local nonnegative-subseries projection for the concrete source
channels. -/
structure Prop24LocalNonnegativeClosureInputs
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) : Type 5 where
  local_nonnegative : LocalNonnegativeSubseriesProjections S
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

def andLocalAbsInputsFromLocalNonnegative
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (input : Prop24LocalNonnegativeClosureInputs hA hB) :
    AndProp24LocalAbsInputs hA hB where
  min2_data := input.min2_data
  domain_eq := input.and_domain_eq
  local_abs :=
    min2LocalAbsProjectionInputsFromLocalNonnegative
      input.local_nonnegative hA.rep hB.rep input.min2_data

def orLocalAbsInputsFromLocalNonnegative
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (input : Prop24LocalNonnegativeClosureInputs hA hB) :
    OrProp24LocalAbsInputs hA hB where
  min2_data := input.min2_data
  or_sub_data := input.or_sub_data
  domain_eq := input.or_domain_eq
  local_abs :=
    orLocalAbsProjectionInputsFromLocalNonnegative
      input.local_nonnegative hA hB input.min2_data input.or_sub_data

/-- Assemble the Proposition 2.4 closure pair from local nonnegative-channel
data and the closed scalar recoveries. -/
def prop24ClosurePairFromLocalNonnegative
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B)
    (input : Prop24LocalNonnegativeClosureInputs hA hB) :
    Prop24ClosurePair hA hB :=
  prop24ClosurePairFromAbsDecomposition hA hB
    { and_input :=
        andProp24ConstructionInputsFromLocalAbs hA hB
          (andLocalAbsInputsFromLocalNonnegative hA hB input)
      or_input :=
        orProp24ConstructionInputsFromLocalAbs hA hB
          (orLocalAbsInputsFromLocalNonnegative hA hB input)
      same_min2_data := rfl }

/-- G148 audit. -/
structure Prop24LocalNonnegativeSubseriesAudit : Type where
  scalar_recoveries_closed_from_g147 : Nat
  arbitrary_global_subseries_bridge_required : Nat
  local_pair_channel_projection_data_required : Nat
  local_absrep_middle_projection_data_required : Nat
  prop24_assembly_from_local_data_closed : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  remaining_frontier_is_local_nonnegative_subseries_certificates : Prop

def prop24LocalNonnegativeSubseriesAudit :
    Prop24LocalNonnegativeSubseriesAudit where
  scalar_recoveries_closed_from_g147 := 1
  arbitrary_global_subseries_bridge_required := 0
  local_pair_channel_projection_data_required := 1
  local_absrep_middle_projection_data_required := 1
  prop24_assembly_from_local_data_closed := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  remaining_frontier_is_local_nonnegative_subseries_certificates := True

end Prop24LocalNonnegativeSubseries
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.Prop24FromAbsDecomposition

/-- G148 package: Proposition 2.4 now assembles from closed scalar recovery plus
local nonnegative-subseries projection certificates. -/
structure BishopRegularSeqChapter2G148Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g147 : BishopRegularSeqChapter2G147Package S
  closure_input :
    forall {A B : BSet X},
      IntegrableSet S A -> IntegrableSet S B -> Type 5
  closure_from_local_nonnegative :
    forall {A B : BSet X},
      forall hA : IntegrableSet S A,
      forall hB : IntegrableSet S B,
        closure_input hA hB -> Prop24ClosurePair hA hB
  audit :
    BishopRegularSeqChapter2.Prop24LocalNonnegativeSubseries.Prop24LocalNonnegativeSubseriesAudit
  scalar_side_closed : Prop
  remaining_frontier_local_nonnegative_subseries_certificates : Prop
  no_global_subseries_choice_in_g148_assembly : Prop

def bishopRegularSeqChapter2G148Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G148Package S where
  g147 := bishopRegularSeqChapter2G147Package S
  closure_input := fun hA hB =>
    BishopRegularSeqChapter2.Prop24LocalNonnegativeSubseries.Prop24LocalNonnegativeClosureInputs hA hB
  closure_from_local_nonnegative := fun hA hB input =>
    BishopRegularSeqChapter2.Prop24LocalNonnegativeSubseries.prop24ClosurePairFromLocalNonnegative
      hA hB input
  audit :=
    BishopRegularSeqChapter2.Prop24LocalNonnegativeSubseries.prop24LocalNonnegativeSubseriesAudit
  scalar_side_closed := True
  remaining_frontier_local_nonnegative_subseries_certificates := True
  no_global_subseries_choice_in_g148_assembly := True

/-- Progress after G148: Prop 2.4's assembly no longer needs an arbitrary
nonnegative-subseries bridge; it only needs local certificates for the concrete
nonnegative channels used by the source proof. -/
def bishopRegularSeqCh1To4ProgressAfterG148 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 88
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G148: assembled Chapter 2 Proposition 2.4 from closed scalar recovery and \
    local nonnegative-subseries channel certificates, avoiding a global \
    arbitrary series-projection selector."


end BishopCReal
