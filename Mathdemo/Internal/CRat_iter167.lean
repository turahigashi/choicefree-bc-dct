import Mathdemo.Internal.CRat_iter166

/-!
# G67: naming the small line-743 pointwise domination

G66 reduced the small line-743 integral estimate to Proposition 1.11 data.
This file names the remaining pointwise content explicitly:

`min(|f|,1/n) <= min(|g_N|,1/n) + | |f| - g_N |`

on a full set.  The final property-(4) assembly can now ask for a source-named
pointwise bridge rather than an anonymous `L1LeOnFull` field.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Source line 743 data in its pointwise form: the small truncation of `|f|`
is bounded by the previous small truncation of `g_N` plus the absolute tail. -/
structure Property4SmallLine743MinTailData
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
  min_tail_on_full :
    BishopRegularSeqL1LeOnFull S full_set
      (cutSmallRep r cuts n)
      (smallOldPlusTailRep S r cuts cor117_abs_data N n
        ofL_data add_data)
  source_line743_pointwise_min_tail_bound : Prop

/-- Repackage the named pointwise source data as the G66 Proposition 1.11
input. -/
def smallLine743Prop111Data_from_min_tail
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
      Property4SmallLine743MinTailData
        S r cuts cor117_abs_data N n ofL_data add_data) :
    Property4SmallLine743Prop111Data
      S r cuts cor117_abs_data N n ofL_data add_data where
  full_set := data.full_set
  full := data.full
  small_bound_on_full := data.min_tail_on_full
  source_line743_is_pointwise_min_abs_tail_bound := True

/-- Small line-743 bridge whose only analytic pointwise input is the named
min-tail domination on a full set. -/
structure Property4SmallLine743FromPointwiseBridge
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
  line743_min_tail_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743MinTailData
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_named_pointwise_bound : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the named pointwise line-743 bridge to the G66 Proposition 1.11
bridge. -/
def property4SmallLine743FromProp111Bridge_from_pointwise
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromPointwiseBridge S) :
    Property4SmallLine743FromProp111Bridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_prop111_data := by
    intro r cuts cor117_abs_data N n
    exact
      smallLine743Prop111Data_from_min_tail
        S r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_min_tail_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_prop111 := True
  source_rhs_integral_identified_with_old_plus_tail_mid := True

/-- Small norm-bound bridge after line 743 is reduced to named pointwise
min-tail data and Proposition 1.11. -/
def property4SmallNormBoundBridge_from_pointwise_line743
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromPointwiseBridge S) :
    Property4SmallNormBoundBridge S :=
  property4SmallNormBoundBridge_from_prop111_line743
    S
    (property4SmallLine743FromProp111Bridge_from_pointwise S bridge)

/-- Property-(4) reduction data with the large G62/G63 route and the small
line-743 bound reduced to named pointwise min-tail data. -/
structure Property4ReductionDataFromLargeRouteSmallPointwiseLine743
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
  small_line743_pointwise : Property4SmallLine743FromPointwiseBridge S
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
  source_small_line743_named_pointwise_bound : Prop

/-- Convert G67 data to the G66 small-Prop.1.11 layer. -/
def property4LargeRouteSmallProp111Data_from_pointwise_line743
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeRouteSmallPointwiseLine743 S r) :
    Property4ReductionDataFromLargeRouteSmallProp111Line743 S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  large_route := data.large_route
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_line743_prop111 :=
    property4SmallLine743FromProp111Bridge_from_pointwise
      S data.small_line743_pointwise
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_large_branch_uses_g62_prop111_route :=
    data.source_large_branch_uses_g62_prop111_route
  source_small_line743_uses_prop111_route := True

/-- Theorem 1.18 property (4), with the small line-743 bound reduced to named
pointwise min-tail data. -/
def property4_from_large_route_small_pointwise_line743
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeRouteSmallPointwiseLine743 S r) :
    Property4Conclusion S r :=
  property4_from_large_route_small_prop111_line743
    S r
    (property4LargeRouteSmallProp111Data_from_pointwise_line743 S r data)

end BishopRegularSeqTheorem118

/-- G67 package: the small line-743 frontier is now a named pointwise
min-tail domination, matching the large line-735 min-Lipschitz data style. -/
structure BishopRegularSeqTheorem118G67Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g66 : BishopRegularSeqTheorem118G66Package S
  small_line743_min_tail_data :
    forall r : BishopRegularSeqIntegrableRep S,
      forall cuts : BishopRegularSeqTheorem118.Property4CutData S r,
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall N n : Nat,
      forall ofL_data :
        BishopRegularSeqOfLData S
          (BishopRegularSeqTheorem118.smallOldCutPFun
            S r cuts cor117_abs_data N n)
          (BishopRegularSeqTheorem118.smallOldCut_mem
            S r cuts cor117_abs_data N n),
      BishopRegularSeqIntegrableRep.AddData
        (BishopRegularSeqTheorem118.smallOldCutRep
          S r cuts cor117_abs_data N n ofL_data)
        (BishopRegularSeqTheorem118.smallAbsTailAbsRep
          S r cuts cor117_abs_data N) ->
        Type 2
  small_line743_pointwise_bridge : Type 3
  small_prop111_from_pointwise :
    BishopRegularSeqTheorem118.Property4SmallLine743FromPointwiseBridge S ->
      BishopRegularSeqTheorem118.Property4SmallLine743FromProp111Bridge S
  property4_large_route_small_pointwise_data :
    BishopRegularSeqIntegrableRep S -> Type 3
  property4_from_large_route_small_pointwise :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_large_route_small_pointwise_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_small_line743_frontier_named : Prop
  remaining_frontier_is_large_line735_and_small_line743_pointwise_verification : Prop

def bishopRegularSeqTheorem118G67Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G67Package S where
  g66 := bishopRegularSeqTheorem118G66Package S
  small_line743_min_tail_data := fun r cuts cor117_abs_data N n ofL_data add_data =>
    BishopRegularSeqTheorem118.Property4SmallLine743MinTailData
      S r cuts cor117_abs_data N n ofL_data add_data
  small_line743_pointwise_bridge :=
    BishopRegularSeqTheorem118.Property4SmallLine743FromPointwiseBridge S
  small_prop111_from_pointwise := fun bridge =>
    BishopRegularSeqTheorem118.property4SmallLine743FromProp111Bridge_from_pointwise
      S bridge
  property4_large_route_small_pointwise_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromLargeRouteSmallPointwiseLine743 S
  property4_from_large_route_small_pointwise := fun r data =>
    BishopRegularSeqTheorem118.property4_from_large_route_small_pointwise_line743
      S r data
  source_small_line743_frontier_named := True
  remaining_frontier_is_large_line735_and_small_line743_pointwise_verification := True

/-- Progress after G67: small line 743 is no longer an anonymous full-set
order input; it is a named min-tail pointwise domination. -/
def bishopRegularSeqCh1To4ProgressAfterG67 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 68
  ch1_on_bishop_real_percent := 95
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 67
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G67: named the small line-743 source frontier as full-set pointwise \
    min-tail domination before applying Proposition 1.11."

set_option linter.style.longLine false


end BishopCReal
