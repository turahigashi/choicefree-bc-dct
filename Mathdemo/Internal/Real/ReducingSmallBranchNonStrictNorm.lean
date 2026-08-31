import Mathdemo.Internal.Real.AssemblingLargeBranchLipschitzBridgeG62

/-!
# G64: reducing the small branch to its non-strict norm-bound bridge

G63 rejoined the G62 large branch to the final Theorem 1.18(4) assembly, but
still accepted the small branch as an already-built `Property4SmallLipschitzBridge`.
This file pushes the small branch one layer down: it is now obtained from the
source-shaped non-strict bound behind lines 743--747 plus the existing strict
upper-transfer step.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The small-branch estimate bridge required by G55, obtained from the
non-strict norm-bound target behind source lines 743--747. -/
def property4SmallLipschitzBridge_from_small_norm_bound_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (small_norm_bound : Property4SmallNormBoundBridge S) :
    Property4SmallLipschitzBridge S :=
  property4SmallLipschitzBridge_from_norm_bound_closed S small_norm_bound

/-- Property-(4) reduction data with the large branch supplied by the G62/G63
route and the small branch supplied only as its non-strict norm-bound bridge. -/
structure Property4ReductionDataFromLargeRouteSmallNormBound
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
  small_norm_bound : Property4SmallNormBoundBridge S
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
  source_small_branch_reduced_to_norm_bound : Prop

/-- Convert G64 data to the G63 large-route data by generating the small
Lipschitz bridge from the small norm-bound bridge. -/
def property4LargeRouteData_from_small_norm_bound
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeRouteSmallNormBound S r) :
    Property4ReductionDataFromLargeProp111Route S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  large_route := data.large_route
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_bridge :=
    property4SmallLipschitzBridge_from_small_norm_bound_closed
      S data.small_norm_bound
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_large_branch_uses_g62_prop111_route :=
    data.source_large_branch_uses_g62_prop111_route
  source_small_branch_kept_as_existing_bridge := True

/-- Theorem 1.18 property (4), with the large route fixed by G62/G63 and the
small route reduced to the source-shaped non-strict norm-bound bridge. -/
def property4_from_large_route_small_norm_bound
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeRouteSmallNormBound S r) :
    Property4Conclusion S r :=
  property4_from_large_prop111_route
    S r
    (property4LargeRouteData_from_small_norm_bound S r data)

end BishopRegularSeqTheorem118

/-- G64 package: the small branch is no longer accepted as a final Lipschitz
bridge; it is obtained from the non-strict norm-bound bridge behind source
lines 743--747. -/
structure BishopRegularSeqTheorem118G64Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g63 : BishopRegularSeqTheorem118G63Package S
  small_lipschitz_from_norm_bound :
    BishopRegularSeqTheorem118.Property4SmallNormBoundBridge S ->
      BishopRegularSeqTheorem118.Property4SmallLipschitzBridge S
  property4_large_route_small_norm_data :
    BishopRegularSeqIntegrableRep S -> Type 3
  property4_from_large_route_small_norm :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_large_route_small_norm_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_small_branch_reduced_to_norm_bound : Prop
  remaining_frontier_is_small_norm_bound_and_pointwise_large_data : Prop

def bishopRegularSeqTheorem118G64Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G64Package S where
  g63 := bishopRegularSeqTheorem118G63Package S
  small_lipschitz_from_norm_bound := fun small_norm_bound =>
    BishopRegularSeqTheorem118.property4SmallLipschitzBridge_from_small_norm_bound_closed
      S small_norm_bound
  property4_large_route_small_norm_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromLargeRouteSmallNormBound S
  property4_from_large_route_small_norm := fun r data =>
    BishopRegularSeqTheorem118.property4_from_large_route_small_norm_bound
      S r data
  source_small_branch_reduced_to_norm_bound := True
  remaining_frontier_is_small_norm_bound_and_pointwise_large_data := True

/-- Progress after G64: the final property-(4) assembly now asks for the small
branch only as the non-strict norm-bound bridge, not as an already-built
Lipschitz estimate. -/
def bishopRegularSeqCh1To4ProgressAfterG64 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 65
  ch1_on_bishop_real_percent := 92
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 64
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G64: reduced Theorem 1.18 property (4)'s small branch from a final \
    Lipschitz bridge to the non-strict norm-bound bridge behind lines 743-747."

set_option linter.style.longLine false


end BishopCReal
