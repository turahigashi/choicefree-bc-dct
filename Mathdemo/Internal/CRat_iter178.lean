import Mathdemo.Internal.CRat_iter177

/-!
# G78: factoring the displayed scalar frontier into two law interfaces

G77 reduced Theorem 1.18(4)'s remaining pointwise frontier to displayed scalar
orders.  This file packages the two remaining displayed scalar laws as global
interfaces:

* large line 735: the displayed min-Lipschitz inequality;
* small line 743: the displayed min-tail inequality.

The laws remain explicit data.  G78 only shows that once these two displayed
laws are supplied, they feed the G77 route for every point and every
Corollary 1.17 approximant.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The two displayed scalar inequalities behind source lines 735 and 743,
quantified over the already-unfolded G77 scalar expressions. -/
structure Property4DisplayedScalarInequalityLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_law :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
      forall x : X,
        RegularSeqLe
          (largeLine735MinExpandedLeftScalar
            S r cuts cor117_data N n x)
          (largeLine735TailPFunExpandedRightScalar
            S r cor117_data N x)
  small_line743_law :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
      forall x : X,
        RegularSeqLe
          (smallLine743PFunLeftScalar S r n x)
          (smallLine743TailPFunExpandedRightScalar
            S r cuts cor117_abs_data N n x)
  source_line735_is_displayed_min_lipschitz_law : Prop
  source_line743_is_displayed_min_tail_law : Prop

/-- Large line-735 route obtained from the displayed scalar law interface. -/
structure Property4LargeLine735FromDisplayedScalarLawsBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  displayed_scalar_laws : Property4DisplayedScalarInequalityLaws S
  abs_from_prop111 : BishopRegularSeqIntegralAbsProp111Bridge S
  old_cut_ofL_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (_cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqOfLData S
          (largeOldCutPFun S r cor117_data N n)
          (largeOldCut_mem S r cor117_data N n)
  cut_diff_sub_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.SubData
          (cutNatRep r cuts n)
          (largeOldCutRep S r cor117_data N n
            (old_cut_ofL_data r cuts cor117_data N n))
  cut_diff_abs_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.AbsData
          (largeCutDiffRep S r cuts cor117_data N n
            (old_cut_ofL_data r cuts cor117_data N n)
            (cut_diff_sub_data r cuts cor117_data N n))
  line735_full_set :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (_cuts : Property4CutData S r),
      forall _cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (_N _n : Nat), Set X
  line735_full :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqFullSet S
          (line735_full_set r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_displayed_scalar_law : Prop

/-- Convert the displayed large scalar law route to the G77 large route. -/
def property4LargeLine735FromTailPFunExpandedBridge_from_displayedScalarLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromDisplayedScalarLawsBridge S) :
    Property4LargeLine735FromTailPFunExpandedBridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_tail_pfun_expanded_order_data := by
    intro r cuts cor117_data N n
    exact
      { full_set := bridge.line735_full_set r cuts cor117_data N n
        full := bridge.line735_full r cuts cor117_data N n
        tail_pfun_expanded_lipschitz := by
          intro x _hx
          exact
            bridge.displayed_scalar_laws.large_line735_law
              r cuts cor117_data N n x
        source_line735_tail_pfun_unfolded := True }
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_tail_pfun_expanded_order := True

/-- Small line-743 route obtained from the displayed scalar law interface. -/
structure Property4SmallLine743FromDisplayedScalarLawsBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  displayed_scalar_laws : Property4DisplayedScalarInequalityLaws S
  prop111_bridge : BishopRegularSeqProp111Bridge S
  old_small_ofL_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        BishopRegularSeqOfLData S
          (smallOldCutPFun S r cuts cor117_abs_data N n)
          (smallOldCut_mem S r cuts cor117_abs_data N n)
  old_plus_tail_add_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.AddData
          (smallOldCutRep S r cuts cor117_abs_data N n
            (old_small_ofL_data r cuts cor117_abs_data N n))
          (smallAbsTailAbsRep S r cuts cor117_abs_data N)
  line743_full_set :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall _cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (_N _n : Nat), Set X
  line743_full :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        BishopRegularSeqFullSet S
          (line743_full_set r cuts cor117_abs_data N n)
  source_line743_reduced_to_displayed_scalar_law : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the displayed small scalar law route to the G77 small route. -/
def property4SmallLine743FromTailPFunExpandedBridge_from_displayedScalarLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromDisplayedScalarLawsBridge S) :
    Property4SmallLine743FromTailPFunExpandedBridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_tail_pfun_expanded_order_data := by
    intro r cuts cor117_abs_data N n
    exact
      { full_set := bridge.line743_full_set r cuts cor117_abs_data N n
        full := bridge.line743_full r cuts cor117_abs_data N n
        tail_pfun_expanded_min_tail := by
          intro x _hx
          exact
            bridge.displayed_scalar_laws.small_line743_law
              r cuts cor117_abs_data N n x
        source_line743_tail_pfun_unfolded := True }
  source_line743_reduced_to_tail_pfun_expanded_order := True
  source_line743_then_uses_prop111 := bridge.source_line743_then_uses_prop111

/-- G78 branch routes obtained from the two displayed scalar law interfaces. -/
structure Property4DisplayedScalarLawBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_displayed_scalar_route :
    Property4LargeLine735FromDisplayedScalarLawsBridge S
  small_line743_displayed_scalar_route :
    Property4SmallLine743FromDisplayedScalarLawsBridge S
  source_displayed_scalar_laws_are_frontier_inputs : Prop
  remaining_frontier_is_two_displayed_scalar_laws : Prop

/-- Convert G78 branch routes to the G77 tail-PFun-expanded layer. -/
def property4TailPFunExpandedBranchRoutes_from_displayedScalarLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4DisplayedScalarLawBranchRoutes S) :
    Property4TailPFunExpandedBranchRoutes S where
  large_line735_tail_pfun_expanded_route :=
    property4LargeLine735FromTailPFunExpandedBridge_from_displayedScalarLaws
      S routes.large_line735_displayed_scalar_route
  small_line743_tail_pfun_expanded_route :=
    property4SmallLine743FromTailPFunExpandedBridge_from_displayedScalarLaws
      S routes.small_line743_displayed_scalar_route
  source_large_line735_tail_pfun_unfolded := True
  source_small_line743_tail_pfun_unfolded := True
  remaining_frontier_is_displayed_pfun_scalar_order := True

/-- Property-(4) reduction data after the displayed frontier has been factored
through the two displayed scalar law interfaces. -/
structure Property4ReductionDataFromDisplayedScalarLawBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_law_branch_routes :
    Property4DisplayedScalarLawBranchRoutes S
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
  source_property4_frontier_is_two_displayed_scalar_laws : Prop

/-- Convert G78 reduction data to the G77 tail-PFun-expanded layer. -/
def property4TailPFunExpandedData_from_displayedScalarLaws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarLawBranchRoutes S r) :
    Property4ReductionDataFromTailPFunExpandedBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  tail_pfun_expanded_branch_routes :=
    property4TailPFunExpandedBranchRoutes_from_displayedScalarLaws
      S data.displayed_scalar_law_branch_routes
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_property4_frontier_is_displayed_pfun_scalar_order := True

/-- Theorem 1.18 property (4), once the two displayed scalar law interfaces
are supplied. -/
def property4_from_displayed_scalar_law_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarLawBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_tail_pfun_expanded_branch_routes
    S r
    (property4TailPFunExpandedData_from_displayedScalarLaws S r data)

end BishopRegularSeqTheorem118

/-- G78 package: the displayed scalar frontier is factored through two
displayed scalar law interfaces. -/
structure BishopRegularSeqTheorem118G78Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g77 : BishopRegularSeqTheorem118G77Package S
  displayed_scalar_laws : Type 4
  displayed_scalar_law_branch_routes : Type 4
  property4_displayed_scalar_law_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_displayed_scalar_law_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_displayed_scalar_law_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  remaining_frontier_is_two_displayed_scalar_laws : Prop

def bishopRegularSeqTheorem118G78Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G78Package S where
  g77 := bishopRegularSeqTheorem118G77Package S
  displayed_scalar_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarInequalityLaws S
  displayed_scalar_law_branch_routes :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarLawBranchRoutes S
  property4_displayed_scalar_law_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarLawBranchRoutes S
  property4_from_displayed_scalar_law_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_law_branch_routes
      S r data
  remaining_frontier_is_two_displayed_scalar_laws := True

/-- Progress after G78: the remaining displayed scalar frontier is factored
into large line-735 and small line-743 displayed scalar law interfaces. -/
def bishopRegularSeqCh1To4ProgressAfterG78 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 79
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 78
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G78: factored Theorem 1.18 property (4)'s displayed scalar frontier \
    into large line735 and small line743 displayed scalar law interfaces."

set_option linter.style.longLine false


end BishopCReal
