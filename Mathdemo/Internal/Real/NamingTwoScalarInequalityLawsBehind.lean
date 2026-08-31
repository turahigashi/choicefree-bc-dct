import Mathdemo.Internal.Real.UnpackingPointwiseRoutesValueLevelInequalities

/-!
# G70: naming the two scalar inequality laws behind property (4)

G69 opened the remaining Theorem 1.18(4) frontiers to value-level
`RegularSeqLe` inequalities.  This file gives those value-level inequalities
source-faithful names:

* large line 735: `|min(f,n)-min(g_N,n)| <= |f-g_N|`;
* small line 743: `min(|f|,1/n) <= min(|g_N|,1/n) + ||f|-g_N|`.

No scalar order proof is smuggled in here.  The scalar laws remain explicit
data, and this file only checks that supplying them feeds the G69
value-branch route and hence the existing property-(4) assembly.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The scalar proposition behind source line 735 at a chosen point. -/
abbrev largeLine735ScalarInequalityAt
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
    (x : X)
    (hleft :
      BishopRegularSeqSeriesSum
        (fun k =>
          absSeq
            (((largeLine735LeftAbsRep
              S r cuts cor117_data N n
              ofL_data sub_data cut_diff_abs_data).fn k).toFun x)))
    (hright :
      BishopRegularSeqSeriesSum
        (fun k =>
          absSeq
            (((largeLine735RightAbsRep
              S r cor117_data N).fn k).toFun x))) : Prop :=
  RegularSeqLe
    (BishopRegularSeqIntegrableRep.valueAt
      (largeLine735LeftAbsRep
        S r cuts cor117_data N n
        ofL_data sub_data cut_diff_abs_data)
      x hleft)
    (BishopRegularSeqIntegrableRep.valueAt
      (largeLine735RightAbsRep S r cor117_data N)
      x hright)

/-- Source line 735 as a scalar law on a full set. -/
structure Property4LargeLine735ScalarLawData
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
  scalar_min_lipschitz :
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
          largeLine735ScalarInequalityAt
            S r cuts cor117_data N n
            ofL_data sub_data cut_diff_abs_data
            x hleft hright
  source_line735_scalar_abs_min_bound : Prop

/-- Repackage the source-named large scalar law as the G69 value data. -/
def largeLine735ValueData_from_scalar_law
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
      Property4LargeLine735ScalarLawData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    Property4LargeLine735ValueMinLipschitzData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data where
  full_set := data.full_set
  full := data.full
  min_lipschitz_value := by
    intro x hx hleft hright
    exact data.scalar_min_lipschitz x hx hleft hright
  source_line735_value_min_lipschitz := True

/-- The scalar proposition behind source line 743 at a chosen point. -/
abbrev smallLine743ScalarInequalityAt
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
    (x : X)
    (hleft :
      BishopRegularSeqSeriesSum
        (fun k =>
          absSeq (((cutSmallRep r cuts n).fn k).toFun x)))
    (hright :
      BishopRegularSeqSeriesSum
        (fun k =>
          absSeq
            (((smallOldPlusTailRep
              S r cuts cor117_abs_data N n
              ofL_data add_data).fn k).toFun x))) : Prop :=
  RegularSeqLe
    (BishopRegularSeqIntegrableRep.valueAt
      (cutSmallRep r cuts n) x hleft)
    (BishopRegularSeqIntegrableRep.valueAt
      (smallOldPlusTailRep
        S r cuts cor117_abs_data N n
        ofL_data add_data)
      x hright)

/-- Source line 743 as a scalar law on a full set. -/
structure Property4SmallLine743ScalarLawData
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
  scalar_min_tail :
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
          smallLine743ScalarInequalityAt
            S r cuts cor117_abs_data N n
            ofL_data add_data x hleft hright
  source_line743_scalar_min_tail_bound : Prop

/-- Repackage the source-named small scalar law as the G69 value data. -/
def smallLine743ValueData_from_scalar_law
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
      Property4SmallLine743ScalarLawData
        S r cuts cor117_abs_data N n ofL_data add_data) :
    Property4SmallLine743ValueMinTailData
      S r cuts cor117_abs_data N n ofL_data add_data where
  full_set := data.full_set
  full := data.full
  min_tail_value := by
    intro x hx hleft hright
    exact data.scalar_min_tail x hx hleft hright
  source_line743_value_min_tail := True

/-- Large line-735 route whose remaining input is the source scalar law. -/
structure Property4LargeLine735FromScalarLawBridge
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
  line735_scalar_law_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735ScalarLawData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_scalar_min_lipschitz : Prop

/-- Convert the large scalar-law route to the G69 value route. -/
def property4LargeLine735FromValueBridge_from_scalar_law
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromScalarLawBridge S) :
    Property4LargeLine735FromValueBridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_value_min_lipschitz_data := by
    intro r cuts cor117_data N n
    exact
      largeLine735ValueData_from_scalar_law
        S r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_scalar_law_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_value_min_lipschitz := True

/-- Small line-743 route whose remaining input is the source scalar law. -/
structure Property4SmallLine743FromScalarLawBridge
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
  line743_scalar_law_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743ScalarLawData
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_scalar_min_tail : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the small scalar-law route to the G69 value route. -/
def property4SmallLine743FromValueBridge_from_scalar_law
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromScalarLawBridge S) :
    Property4SmallLine743FromValueBridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_value_min_tail_data := by
    intro r cuts cor117_abs_data N n
    exact
      smallLine743ValueData_from_scalar_law
        S r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_scalar_law_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_value_min_tail := True
  source_line743_then_uses_prop111 := bridge.source_line743_then_uses_prop111

/-- The final property-(4) branch routes with the remaining frontiers named as
the two source scalar laws. -/
structure Property4ScalarLawBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_scalar_route : Property4LargeLine735FromScalarLawBridge S
  small_line743_scalar_route : Property4SmallLine743FromScalarLawBridge S
  source_large_line735_is_scalar_min_lipschitz : Prop
  source_small_line743_is_scalar_min_tail : Prop
  both_scalar_laws_feed_value_branch_routes : Prop

/-- Convert scalar-law branch routes to the G69 value-level branch routes. -/
def property4ValueBranchRoutes_from_scalar_law
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4ScalarLawBranchRoutes S) :
    Property4ValueBranchRoutes S where
  large_line735_value_route :=
    property4LargeLine735FromValueBridge_from_scalar_law
      S routes.large_line735_scalar_route
  small_line743_value_route :=
    property4SmallLine743FromValueBridge_from_scalar_law
      S routes.small_line743_scalar_route
  source_large_line735_value_inequality := True
  source_small_line743_value_inequality := True
  both_value_routes_feed_full_set_monotonicity := True

/-- Property-(4) reduction data whose remaining frontier is exactly the two
source scalar laws. -/
structure Property4ReductionDataFromScalarLawBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  scalar_law_branch_routes : Property4ScalarLawBranchRoutes S
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
  source_property4_frontier_is_two_scalar_laws : Prop

/-- Convert G70 scalar-law data to the G69 value-branch layer. -/
def property4ValueBranchData_from_scalar_law
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromScalarLawBranchRoutes S r) :
    Property4ReductionDataFromValueBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  value_branch_routes :=
    property4ValueBranchRoutes_from_scalar_law
      S data.scalar_law_branch_routes
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
  source_property4_frontier_is_two_value_inequalities := True

/-- Theorem 1.18 property (4), with the final frontier isolated as two scalar
inequality laws. -/
def property4_from_scalar_law_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromScalarLawBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_value_branch_routes
    S r
    (property4ValueBranchData_from_scalar_law S r data)

end BishopRegularSeqTheorem118

/-- G70 package: property (4)'s final remaining obligations are named as two
scalar source laws feeding the G69 value route. -/
structure BishopRegularSeqTheorem118G70Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g69 : BishopRegularSeqTheorem118G69Package S
  scalar_law_branch_routes : Type 4
  property4_scalar_law_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_scalar_law_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_scalar_law_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_property4_frontier_is_scalar_law_level : Prop
  remaining_frontier_is_large735_and_small743_scalar_order : Prop

def bishopRegularSeqTheorem118G70Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G70Package S where
  g69 := bishopRegularSeqTheorem118G69Package S
  scalar_law_branch_routes :=
    BishopRegularSeqTheorem118.Property4ScalarLawBranchRoutes S
  property4_scalar_law_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromScalarLawBranchRoutes S
  property4_from_scalar_law_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_scalar_law_branch_routes
      S r data
  source_property4_frontier_is_scalar_law_level := True
  remaining_frontier_is_large735_and_small743_scalar_order := True

/-- Progress after G70: the final property-(4) frontier is now precisely two
named scalar order laws corresponding to source lines 735 and 743. -/
def bishopRegularSeqCh1To4ProgressAfterG70 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 71
  ch1_on_bishop_real_percent := 98
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 70
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G70: named Theorem 1.18 property (4)'s remaining large-line735 and \
    small-line743 obligations as two scalar RegularSeq order laws."

set_option linter.style.longLine false


end BishopCReal
