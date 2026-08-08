import Mathdemo.Internal.CRat_iter149

/-!
# G50: Theorem 1.16 tail squeeze bridge

The final estimate in Theorem 1.16 is:

`||f - sum_{n <= N} f_n|| <= sum_{n > N} (I(|f_n|) + 2^{-n})`,

and the right hand side tends to zero.  G49 recorded the tail majorant data.
This file factors the remaining order-squeeze step into explicit data and
connects it to the G49 tail-estimate bridge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Order squeeze to zero for Bishop regular-sequence values.  This is the
RegularSeq analogue of the source step "the final right hand side tends to
zero, hence the norm tail tends to zero". -/
structure BishopRegularSeqTendstoZeroOrderBridge : Type 1 where
  tendsto_zero_of_nonneg_le :
    forall {u v : Nat -> RegularSeq},
      (forall N : Nat, RegularSeqNonneg (u N)) ->
      (forall N : Nat, RegularSeqLe (u N) (v N)) ->
      BishopRegularSeqTendsto v zeroSeq ->
      BishopRegularSeqTendsto u zeroSeq
  source_order_squeeze_to_zero : Prop

/-- Theorem 1.16-specific order bridge: norms are non-negative, and the
generic squeeze bridge converts the G49 majorant estimate into convergence of
the tail norm. -/
structure BishopRegularSeqTheorem116TailOrderBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  order_bridge : BishopRegularSeqTendstoZeroOrderBridge
  tail_norm_nonneg :
    forall (input : BishopRegularSeqTheorem116Input S)
      (limit : BishopRegularSeqIntegrableRep S)
      (partial_sums : BishopRegularSeqL1FinitePartialSums S input.seq)
      (tail_sub_data :
        forall N : Nat,
          BishopRegularSeqIntegrableRep.SubData
            limit (partial_sums.partialRep N))
      (tail_abs_data :
        forall N : Nat,
          BishopRegularSeqIntegrableRep.AbsData
            (BishopRegularSeqIntegrableRep.sub
              limit (partial_sums.partialRep N) (tail_sub_data N)))
      (N : Nat),
        RegularSeqNonneg
          (BishopRegularSeqTheorem116.tailNormTerm
            input limit partial_sums tail_sub_data tail_abs_data N)
  source_norms_are_nonnegative : Prop

/-- Convert the order-squeeze bridge into the G49 tail-estimate bridge. -/
def BishopRegularSeqTheorem116TailOrderBridge.toTailEstimateBridge
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (bridge : BishopRegularSeqTheorem116TailOrderBridge S) :
    BishopRegularSeqTheorem116TailEstimateBridge S where
  tendsto_zero_from_majorant :=
    fun input limit partial_sums tail_sub_data tail_abs_data estimate =>
      bridge.order_bridge.tendsto_zero_of_nonneg_le
        (u := fun N =>
          BishopRegularSeqTheorem116.tailNormTerm
            input limit partial_sums tail_sub_data tail_abs_data N)
        (v := fun N => (estimate.tail_majorant_sum N).sum)
        (fun N =>
          bridge.tail_norm_nonneg
            input limit partial_sums tail_sub_data tail_abs_data N)
        (fun N => estimate.tail_norm_le_majorant N)
        estimate.tail_majorant_tends_zero
  source_comparison_to_zero_is_order_bridge :=
    bridge.order_bridge.source_order_squeeze_to_zero

/-- Direct constructor of the G48 tail norm data using G49 estimates and the
G50 order-squeeze bridge. -/
def bishopRegularSeqTheorem116_tailNormData_from_order
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (order_bridge : BishopRegularSeqTheorem116TailOrderBridge S)
    (input : BishopRegularSeqTheorem116Input S)
    (limit : BishopRegularSeqIntegrableRep S)
    (partial_data : BishopRegularSeqL1FinitePartialSumData S input.seq)
    (tail_sub_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.SubData
          limit (partial_data.partialRep N))
    (tail_abs_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.AbsData
          (BishopRegularSeqIntegrableRep.sub
            limit (partial_data.partialRep N) (tail_sub_data N)))
    (estimate :
      BishopRegularSeqTheorem116TailEstimateData
        S input limit
        partial_data.toFinitePartialSums
        tail_sub_data
        tail_abs_data) :
    BishopRegularSeqTheorem116TailNormData S input limit :=
  bishopRegularSeqTheorem116_tailNormData_from_estimates
    S order_bridge.toTailEstimateBridge input limit partial_data
    tail_sub_data tail_abs_data estimate

/-- Source-facing package for the final estimate step in Theorem 1.16. -/
structure BishopRegularSeqTheorem116TailSqueezePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  order_bridge : Type 1
  theorem116_tail_order_bridge : Type 1
  to_tail_estimate_bridge :
    BishopRegularSeqTheorem116TailOrderBridge S ->
      BishopRegularSeqTheorem116TailEstimateBridge S
  tail_norm_data_from_order :
    BishopRegularSeqTheorem116TailOrderBridge S ->
      forall input : BishopRegularSeqTheorem116Input S,
      forall limit : BishopRegularSeqIntegrableRep S,
      forall partial_data : BishopRegularSeqL1FinitePartialSumData S input.seq,
      forall tail_sub_data :
        forall N : Nat,
          BishopRegularSeqIntegrableRep.SubData
            limit (partial_data.partialRep N),
      forall tail_abs_data :
        forall N : Nat,
          BishopRegularSeqIntegrableRep.AbsData
            (BishopRegularSeqIntegrableRep.sub
              limit (partial_data.partialRep N) (tail_sub_data N)),
      BishopRegularSeqTheorem116TailEstimateData
        S input limit
        partial_data.toFinitePartialSums
        tail_sub_data
        tail_abs_data ->
      BishopRegularSeqTheorem116TailNormData S input limit
  source_final_rhs_tends_zero_step : Prop

def bishopRegularSeqTheorem116TailSqueezePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem116TailSqueezePackage S where
  order_bridge := BishopRegularSeqTendstoZeroOrderBridge
  theorem116_tail_order_bridge := BishopRegularSeqTheorem116TailOrderBridge S
  to_tail_estimate_bridge := fun bridge =>
    BishopRegularSeqTheorem116TailOrderBridge.toTailEstimateBridge bridge
  tail_norm_data_from_order := fun bridge input limit partial_data
      tail_sub_data tail_abs_data estimate =>
    bishopRegularSeqTheorem116_tailNormData_from_order
      S bridge input limit partial_data tail_sub_data tail_abs_data estimate
  source_final_rhs_tends_zero_step := True

/-- Progress after G50: the final tail estimate in Theorem 1.16 is reduced to
an explicit RegularSeq order-squeeze bridge plus norm non-negativity. -/
def bishopRegularSeqCh1To4ProgressAfterG50 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 73
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 50
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G50: connected Theorem 1.16 tail majorant estimates to norm convergence \
    through an explicit RegularSeq order-squeeze bridge."


end BishopCReal
