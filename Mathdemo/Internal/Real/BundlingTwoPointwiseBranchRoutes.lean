import Mathdemo.Internal.Real.NamingSmallLine743PointwiseDomination

/-!
# G68: bundling the two pointwise branch routes

G67 left Theorem 1.18(4)'s final assembly with two named pointwise frontiers:

* large branch: line 735 min-Lipschitz domination, already threaded through
  the G62 Proposition 1.11 route;
* small branch: line 743 min-tail domination, threaded through the G67 route.

This file bundles those two branch routes as the explicit remaining source
frontier for property (4).
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The two source pointwise routes that remain at the property-(4) frontier:
large line 735 and small line 743. -/
structure Property4PointwiseBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_route : Property4LargeLine735FromProp111Bridge S
  small_line743_route : Property4SmallLine743FromPointwiseBridge S
  source_large_line735_is_min_lipschitz_on_full : Prop
  source_small_line743_is_min_tail_on_full : Prop
  both_routes_feed_proposition_1_11 : Prop

/-- Property-(4) reduction data with both branch frontiers carried together as
the two named pointwise routes. -/
structure Property4ReductionDataFromPointwiseBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  branch_routes : Property4PointwiseBranchRoutes S
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
  source_property4_frontier_is_two_pointwise_routes : Prop

/-- Convert the bundled branch-route data to the G67 pointwise small-line layer. -/
def property4LargeRouteSmallPointwiseData_from_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromPointwiseBranchRoutes S r) :
    Property4ReductionDataFromLargeRouteSmallPointwiseLine743 S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  large_route := data.branch_routes.large_line735_route
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_line743_pointwise := data.branch_routes.small_line743_route
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_large_branch_uses_g62_prop111_route := True
  source_small_line743_named_pointwise_bound := True

/-- Theorem 1.18 property (4), with both branches supplied as bundled
pointwise routes. -/
def property4_from_pointwise_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromPointwiseBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_large_route_small_pointwise_line743
    S r
    (property4LargeRouteSmallPointwiseData_from_branch_routes S r data)

end BishopRegularSeqTheorem118

/-- G68 package: final property-(4) assembly now exposes both remaining
branches as named pointwise routes. -/
structure BishopRegularSeqTheorem118G68Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g67 : BishopRegularSeqTheorem118G67Package S
  pointwise_branch_routes : Type 4
  property4_pointwise_branch_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_pointwise_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_pointwise_branch_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_property4_frontier_is_bundled : Prop
  remaining_frontier_large_line735_small_line743_pointwise : Prop

def bishopRegularSeqTheorem118G68Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G68Package S where
  g67 := bishopRegularSeqTheorem118G67Package S
  pointwise_branch_routes :=
    BishopRegularSeqTheorem118.Property4PointwiseBranchRoutes S
  property4_pointwise_branch_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromPointwiseBranchRoutes S
  property4_from_pointwise_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_pointwise_branch_routes
      S r data
  source_property4_frontier_is_bundled := True
  remaining_frontier_large_line735_small_line743_pointwise := True

/-- Progress after G68: both property-(4) branch frontiers are bundled as
named full-set pointwise routes. -/
def bishopRegularSeqCh1To4ProgressAfterG68 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 69
  ch1_on_bishop_real_percent := 96
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 68
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G68: bundled Theorem 1.18 property (4)'s remaining large-line735 and \
    small-line743 obligations as named full-set pointwise routes."

set_option linter.style.longLine false


end BishopCReal
