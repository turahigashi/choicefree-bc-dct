import Mathdemo.Internal.Real.BundlingTwoPointwiseBranchRoutes

/-!
# G69: unpacking the pointwise routes to value-level inequalities

G68 bundled the remaining Theorem 1.18(4) frontiers as two full-set pointwise
routes.  This file opens those pointwise routes one layer further: each route
is now supplied by value-level `RegularSeqLe` inequalities for every point and
every pair of value-series witnesses.

The remaining frontier is therefore no longer an anonymous `L1LeOnFull`
object; it is the two scalar-valued source inequalities

* `|min(f,n)-min(g,n)| <= |f-g|`;
* `min(|f|,1/n) <= min(|g_N|,1/n) + ||pointwise tail||`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The left `L1` representative in large source line 735:
`|min(f,n)-min(g_N,n)|`. -/
def largeLine735LeftAbsRep
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (cutNatRep r cuts n)
        (largeOldCutRep S r cor117_data N n ofL_data))
    (cut_diff_abs_data :
      BishopRegularSeqIntegrableRep.AbsData
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.abs
    (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)
    cut_diff_abs_data

/-- The right `L1` representative in large source line 735: `|f-g_N|`. -/
def largeLine735RightAbsRep
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.abs
    (largeTailRep S r cor117_data N)
    (largeTailAbsData S r cor117_data N)

/-- Large line 735 in value-level form.  This is the scalar content behind
`|min(f,n)-min(g_N,n)| <= |f-g_N|` on a full set. -/
structure Property4LargeLine735ValueMinLipschitzData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (cutNatRep r cuts n)
        (largeOldCutRep S r cor117_data N n ofL_data))
    (cut_diff_abs_data :
      BishopRegularSeqIntegrableRep.AbsData
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)) :
    Type 2 where
  full_set : Set X
  full : BishopRegularSeqFullSet S full_set
  min_lipschitz_value :
    forall x : X,
      x ∈ full_set ->
        forall hleft :
          BishopRegularSeqSeriesSum
            (fun k =>
              absSeq
                (((largeLine735LeftAbsRep
                  S r cuts cor117_data N n
                  ofL_data sub_data cut_diff_abs_data).fn k).toFun x)),
        forall hright :
          BishopRegularSeqSeriesSum
            (fun k =>
              absSeq
                (((largeLine735RightAbsRep
                  S r cor117_data N).fn k).toFun x)),
          RegularSeqLe
            (BishopRegularSeqIntegrableRep.valueAt
              (largeLine735LeftAbsRep
                S r cuts cor117_data N n
                ofL_data sub_data cut_diff_abs_data)
              x hleft)
            (BishopRegularSeqIntegrableRep.valueAt
              (largeLine735RightAbsRep S r cor117_data N)
              x hright)
  source_line735_value_min_lipschitz : Prop

/-- Repackage value-level large line 735 data as the G62 `L1LeOnFull` data. -/
def largeLine735MinLipschitzData_from_value
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (cutNatRep r cuts n)
        (largeOldCutRep S r cor117_data N n ofL_data))
    (cut_diff_abs_data :
      BishopRegularSeqIntegrableRep.AbsData
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data))
    (data :
      Property4LargeLine735ValueMinLipschitzData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    Property4LargeLine735MinLipschitzData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data where
  full_set := data.full_set
  full := data.full
  min_lipschitz_on_full :=
    { le_value := by
        intro x hx hleft hright
        exact data.min_lipschitz_value x hx hleft hright }
  source_line735_is_pointwise_min_lipschitz := True

/-- Large branch route whose line-735 input is now value-level data. -/
structure Property4LargeLine735FromValueBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
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
  line735_value_min_lipschitz_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735ValueMinLipschitzData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_value_min_lipschitz : Prop

/-- Convert the value-level large line-735 route to the G62 route. -/
def property4LargeLine735FromProp111Bridge_from_value
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromValueBridge S) :
    Property4LargeLine735FromProp111Bridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_min_lipschitz_data := by
    intro r cuts cor117_data N n
    exact
      largeLine735MinLipschitzData_from_value
        S r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_value_min_lipschitz_data
          r cuts cor117_data N n)
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_min_lipschitz_prop111 := True

/-- Small line 743 in value-level form.  This is the scalar content behind
`min(|f|,1/n) <= min(|g_N|,1/n) + | |f|-g_N |` on a full set. -/
structure Property4SmallLine743ValueMinTailData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (smallOldCutPFun S r cuts cor117_abs_data N n)
        (smallOldCut_mem S r cuts cor117_abs_data N n))
    (add_data :
      BishopRegularSeqIntegrableRep.AddData
        (smallOldCutRep S r cuts cor117_abs_data N n ofL_data)
        (smallAbsTailAbsRep S r cuts cor117_abs_data N)) :
    Type 2 where
  full_set : Set X
  full : BishopRegularSeqFullSet S full_set
  min_tail_value :
    forall x : X,
      x ∈ full_set ->
        forall hleft :
          BishopRegularSeqSeriesSum
            (fun k =>
              absSeq (((cutSmallRep r cuts n).fn k).toFun x)),
        forall hright :
          BishopRegularSeqSeriesSum
            (fun k =>
              absSeq
                (((smallOldPlusTailRep
                  S r cuts cor117_abs_data N n
                  ofL_data add_data).fn k).toFun x)),
          RegularSeqLe
            (BishopRegularSeqIntegrableRep.valueAt
              (cutSmallRep r cuts n) x hleft)
            (BishopRegularSeqIntegrableRep.valueAt
              (smallOldPlusTailRep
                S r cuts cor117_abs_data N n
                ofL_data add_data)
              x hright)
  source_line743_value_min_tail : Prop

/-- Repackage value-level small line 743 data as the G67 min-tail data. -/
def smallLine743MinTailData_from_value
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (smallOldCutPFun S r cuts cor117_abs_data N n)
        (smallOldCut_mem S r cuts cor117_abs_data N n))
    (add_data :
      BishopRegularSeqIntegrableRep.AddData
        (smallOldCutRep S r cuts cor117_abs_data N n ofL_data)
        (smallAbsTailAbsRep S r cuts cor117_abs_data N))
    (data :
      Property4SmallLine743ValueMinTailData
        S r cuts cor117_abs_data N n ofL_data add_data) :
    Property4SmallLine743MinTailData
      S r cuts cor117_abs_data N n ofL_data add_data where
  full_set := data.full_set
  full := data.full
  min_tail_on_full :=
    { le_value := by
        intro x hx hleft hright
        exact data.min_tail_value x hx hleft hright }
  source_line743_pointwise_min_tail_bound := True

/-- Small line-743 route whose input is now value-level data. -/
structure Property4SmallLine743FromValueBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
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
  line743_value_min_tail_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743ValueMinTailData
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_value_min_tail : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the value-level small route to the G67 pointwise route. -/
def property4SmallLine743FromPointwiseBridge_from_value
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromValueBridge S) :
    Property4SmallLine743FromPointwiseBridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_min_tail_data := by
    intro r cuts cor117_abs_data N n
    exact
      smallLine743MinTailData_from_value
        S r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_value_min_tail_data
          r cuts cor117_abs_data N n)
  source_line743_named_pointwise_bound := True
  source_line743_then_uses_prop111 := bridge.source_line743_then_uses_prop111

/-- The two source branch routes with both pointwise frontiers opened to
value-level `RegularSeqLe` inequalities. -/
structure Property4ValueBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_value_route : Property4LargeLine735FromValueBridge S
  small_line743_value_route : Property4SmallLine743FromValueBridge S
  source_large_line735_value_inequality : Prop
  source_small_line743_value_inequality : Prop
  both_value_routes_feed_full_set_monotonicity : Prop

/-- Convert value-level branch routes to the G68 pointwise branch routes. -/
def property4PointwiseBranchRoutes_from_value
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4ValueBranchRoutes S) :
    Property4PointwiseBranchRoutes S where
  large_line735_route :=
    property4LargeLine735FromProp111Bridge_from_value
      S routes.large_line735_value_route
  small_line743_route :=
    property4SmallLine743FromPointwiseBridge_from_value
      S routes.small_line743_value_route
  source_large_line735_is_min_lipschitz_on_full := True
  source_small_line743_is_min_tail_on_full := True
  both_routes_feed_proposition_1_11 := True

/-- Property-(4) reduction data with both pointwise branch routes supplied in
value-level form. -/
structure Property4ReductionDataFromValueBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  value_branch_routes : Property4ValueBranchRoutes S
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
  source_property4_frontier_is_two_value_inequalities : Prop

/-- Convert G69 data to the G68 bundled-pointwise layer. -/
def property4PointwiseBranchData_from_value
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromValueBranchRoutes S r) :
    Property4ReductionDataFromPointwiseBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  branch_routes :=
    property4PointwiseBranchRoutes_from_value
      S data.value_branch_routes
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
  source_property4_frontier_is_two_pointwise_routes := True

/-- Theorem 1.18 property (4), with the final branch frontier opened to
value-level inequalities. -/
def property4_from_value_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromValueBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_pointwise_branch_routes
    S r
    (property4PointwiseBranchData_from_value S r data)

end BishopRegularSeqTheorem118

/-- G69 package: both remaining property-(4) pointwise frontiers are opened to
value-level RegularSeq inequalities. -/
structure BishopRegularSeqTheorem118G69Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g68 : BishopRegularSeqTheorem118G68Package S
  value_branch_routes : Type 4
  property4_value_branch_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_value_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_value_branch_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_property4_frontier_is_value_level : Prop
  remaining_frontier_is_two_scalar_regularseq_inequalities : Prop

def bishopRegularSeqTheorem118G69Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G69Package S where
  g68 := bishopRegularSeqTheorem118G68Package S
  value_branch_routes :=
    BishopRegularSeqTheorem118.Property4ValueBranchRoutes S
  property4_value_branch_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromValueBranchRoutes S
  property4_from_value_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_value_branch_routes
      S r data
  source_property4_frontier_is_value_level := True
  remaining_frontier_is_two_scalar_regularseq_inequalities := True

/-- Progress after G69: the two remaining branch obligations have been opened
from `L1LeOnFull` packages to value-level RegularSeq inequalities. -/
def bishopRegularSeqCh1To4ProgressAfterG69 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 70
  ch1_on_bishop_real_percent := 97
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 69
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G69: opened Theorem 1.18 property (4)'s large-line735 and \
    small-line743 pointwise routes to value-level RegularSeq inequalities."

set_option linter.style.longLine false


end BishopCReal
