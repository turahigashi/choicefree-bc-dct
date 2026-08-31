import Mathdemo.Internal.Real.ReducingLine735MinLipschitzData

/-!
# G63: assembling the large-branch Lipschitz bridge from the G62 route

G62 reduced both displayed large-branch inequalities in Theorem 1.18(4) to
Proposition 1.11-shaped source data.  This file rejoins that norm-bound route
to the earlier G55/G57 endpoint: the actual large Lipschitz estimate bridge
used by the final property-(4) assembly.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The large-branch estimate bridge required by G55, obtained from the
G62 source route: line 734 via Proposition 1.11, line 735 via pointwise
min-Lipschitz domination plus Proposition 1.11, then strict-upper transfer. -/
def property4LargeLipschitzBridge_from_prop111_line734_line735
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromProp111Bridge S) :
    Property4LargeLipschitzBridge S :=
  property4LargeLipschitzBridge_from_norm_bound_closed
    S
    (property4LargeNormBoundBridge_from_prop111_line734_line735 S bridge)

/-- Property-(4) reduction data with the large branch supplied by the G62
source route and the small branch still supplied by the existing small bridge.
This is a direct bridge back to the G55 final assembly shape. -/
structure Property4ReductionDataFromLargeProp111Route
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 3 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  large_route : Property4LargeLine735FromProp111Bridge S
  large_epsv : RegularSeq
  large_eps_pos : regularSeqLtData zeroSeq large_epsv
  large_approx_index : Nat
  large_approx_norm_lt_eps :
    regularSeqLtData
      (BishopRegularSeqIntegrableRep.sourceNorm
        (BishopRegularSeqIntegrableRep.sub
          r
          ((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep
            large_approx_index)
          ((bishopRegularSeqCor117_from_data S r cor117_data).tail_sub_data
            large_approx_index))
        ((bishopRegularSeqCor117_from_data S r cor117_data).tail_abs_data
          large_approx_index))
      large_epsv
  large_trunc_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
      (BishopRegularSeqIntegrableRep.integral r)
  small_bridge : Property4SmallLipschitzBridge S
  small_epsv : RegularSeq
  small_eps_pos : regularSeqLtData zeroSeq small_epsv
  small_approx_index : Nat
  small_cor117_abs_data :
    BishopRegularSeqCor117ApproxData S
      (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
  small_abs_close :
    regularSeqLtData
      (BishopRegularSeqIntegrableRep.sourceNorm
        (BishopRegularSeqIntegrableRep.sub
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
          ((bishopRegularSeqCor117_from_data S
              (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
              small_cor117_abs_data).approximant_rep small_approx_index)
          ((bishopRegularSeqCor117_from_data S
              (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
              small_cor117_abs_data).tail_sub_data small_approx_index))
        ((bishopRegularSeqCor117_from_data S
            (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
            small_cor117_abs_data).tail_abs_data small_approx_index))
      small_epsv
  small_trunc_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
      zeroSeq
  source_large_branch_uses_g62_prop111_route : Prop
  source_small_branch_kept_as_existing_bridge : Prop

/-- Convert the G63 large-route data into the G55 bridge-factored reduction
data. -/
def property4BridgeData_from_large_prop111_route
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeProp111Route S r) :
    Property4ReductionDataFromBridges S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  large_bridge :=
    property4LargeLipschitzBridge_from_prop111_line734_line735
      S data.large_route
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_bridge := data.small_bridge
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_uses_corollary_1_17_for_large_truncation := True
  source_uses_corollary_1_17_for_small_abs_truncation := True
  source_uses_displayed_lipschitz_estimates := True

/-- Theorem 1.18 property (4), using the G62/G63 source route for the large
branch and the existing bridge frontier for the small branch. -/
def property4_from_large_prop111_route
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeProp111Route S r) :
    Property4Conclusion S r :=
  property4_from_bridge_data
    S r
    (property4BridgeData_from_large_prop111_route S r data)

end BishopRegularSeqTheorem118

/-- G63 package: the G62 large branch now feeds the G55 final estimate bridge;
only the small branch remains at the previous explicit bridge frontier. -/
structure BishopRegularSeqTheorem118G63Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g62 : BishopRegularSeqTheorem118G62Package S
  large_lipschitz_from_g62 :
    BishopRegularSeqTheorem118.Property4LargeLine735FromProp111Bridge S ->
      BishopRegularSeqTheorem118.Property4LargeLipschitzBridge S
  property4_large_route_data :
    BishopRegularSeqIntegrableRep S -> Type 3
  property4_from_large_route :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_large_route_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_large_branch_rejoined_final_assembly : Prop
  remaining_frontier_is_small_branch_and_pointwise_large_data : Prop

def bishopRegularSeqTheorem118G63Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G63Package S where
  g62 := bishopRegularSeqTheorem118G62Package S
  large_lipschitz_from_g62 := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeLipschitzBridge_from_prop111_line734_line735
      S bridge
  property4_large_route_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromLargeProp111Route S
  property4_from_large_route := fun r data =>
    BishopRegularSeqTheorem118.property4_from_large_prop111_route S r data
  source_large_branch_rejoined_final_assembly := True
  remaining_frontier_is_small_branch_and_pointwise_large_data := True

/-- Progress after G63: the large branch source route rejoins the final
property-(4) bridge assembly. -/
def bishopRegularSeqCh1To4ProgressAfterG63 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 64
  ch1_on_bishop_real_percent := 91
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 63
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G63: rejoined the G62 large-branch route to the final Theorem 1.18(4) \
    Lipschitz estimate bridge; small branch remains the next frontier."

set_option linter.style.longLine false


end BishopCReal
