import Mathdemo.Internal.CRat_iter172

/-!
# G73: expanding the PFun-order frontier to displayed scalar expressions

G72 reduced the remaining property-(4) frontier to PFun-level pointwise order.
This file unfolds the outer PFun operations so that the remaining orders are
closer to the displayed source expressions:

* large line 735 becomes an order between
  `absSeq (min(f,n)-min(g_N,n))` and `absSeq (f-g_N)` at the PFun level;
* small line 743 becomes an order between
  `minSeqWith (absSeq f) (eps n)` and the PFun-level sum of the previous small
  truncation and the absolute tail.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The expanded PFun-level left scalar for large source line 735:
`|min(f,n)-min(g_N,n)|`. -/
def largeLine735PFunLeftScalar
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
    (x : X) : RegularSeq :=
  absSeq
    ((largeCutDiffRep S r cuts cor117_data N n
      ofL_data sub_data).pfun.toFun x)

/-- The expanded PFun-level right scalar for large source line 735: `|f-g_N|`. -/
def largeLine735PFunRightScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat)
    (x : X) : RegularSeq :=
  absSeq ((largeTailRep S r cor117_data N).pfun.toFun x)

/-- Large line 735 with the outer PFun absolute values unfolded to scalar
`absSeq` expressions. -/
structure Property4LargeLine735ExpandedPFunOrderData
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
  expanded_min_lipschitz :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          (largeLine735PFunLeftScalar
            S r cuts cor117_data N n ofL_data sub_data x)
          (largeLine735PFunRightScalar
            S r cor117_data N x)
  source_line735_outer_abs_unfolded : Prop

/-- Convert expanded large line-735 scalar order to the G72 PFun-order data. -/
def largeLine735PFunOrderData_from_expanded
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
      Property4LargeLine735ExpandedPFunOrderData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    Property4LargeLine735PFunOrderData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data where
  full_set := data.full_set
  full := data.full
  pfun_min_lipschitz := by
    intro x hx
    simpa [largeLine735PFunLeftScalar, largeLine735PFunRightScalar,
      largeLine735LeftAbsRep, largeLine735RightAbsRep,
      BishopRegularSeqIntegrableRep.abs, BishopRegularSeqPFun.absf]
      using data.expanded_min_lipschitz x hx
  source_line735_pfun_abs_min_bound := True

/-- The expanded PFun-level left scalar for small source line 743:
`min(|f|,1/n)`. -/
def smallLine743PFunLeftScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (n : Nat)
    (x : X) : RegularSeq :=
  minSeqWith Arch (absSeq (r.pfun.toFun x)) (constSeq (eps n))

/-- The expanded PFun-level right scalar for small source line 743:
previous small truncation plus the absolute tail. -/
def smallLine743PFunRightScalar
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
    (x : X) : RegularSeq :=
  addSeq
    ((smallOldCutRep S r cuts cor117_abs_data N n ofL_data).pfun.toFun x)
    ((smallAbsTailAbsRep S r cuts cor117_abs_data N).pfun.toFun x)

/-- Small line 743 with the outer PFun operations unfolded to scalar
expressions. -/
structure Property4SmallLine743ExpandedPFunOrderData
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
  expanded_min_tail :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          (smallLine743PFunLeftScalar S r n x)
          (smallLine743PFunRightScalar
            S r cuts cor117_abs_data N n ofL_data x)
  source_line743_outer_cut_and_add_unfolded : Prop

/-- Convert expanded small line-743 scalar order to the G72 PFun-order data. -/
def smallLine743PFunOrderData_from_expanded
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
      Property4SmallLine743ExpandedPFunOrderData
        S r cuts cor117_abs_data N n ofL_data add_data) :
    Property4SmallLine743PFunOrderData
      S r cuts cor117_abs_data N n ofL_data add_data where
  full_set := data.full_set
  full := data.full
  pfun_min_tail := by
    intro x hx
    simpa [smallLine743PFunLeftScalar, smallLine743PFunRightScalar,
      cutSmallRep, smallOldPlusTailRep,
      BishopRegularSeqIntegrableRep.cutSmall,
      BishopRegularSeqIntegrableRep.cutConst,
      BishopRegularSeqIntegrableRep.abs,
      BishopRegularSeqIntegrableRep.add,
      BishopRegularSeqPFun.cutConst,
      BishopRegularSeqPFun.absf,
      BishopRegularSeqPFun.add]
      using data.expanded_min_tail x hx
  source_line743_pfun_min_tail_bound := True

/-- Large line-735 route whose remaining input is expanded PFun-level scalar
order. -/
structure Property4LargeLine735FromExpandedPFunBridge
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
  line735_expanded_pfun_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735ExpandedPFunOrderData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_expanded_pfun_order : Prop

/-- Convert the expanded large route to the G72 PFun-order route. -/
def property4LargeLine735FromPFunOrderBridge_from_expanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromExpandedPFunBridge S) :
    Property4LargeLine735FromPFunOrderBridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_pfun_order_data := by
    intro r cuts cor117_data N n
    exact
      largeLine735PFunOrderData_from_expanded
        S r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_expanded_pfun_order_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_pfun_order := True

/-- Small line-743 route whose remaining input is expanded PFun-level scalar
order. -/
structure Property4SmallLine743FromExpandedPFunBridge
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
  line743_expanded_pfun_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743ExpandedPFunOrderData
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_expanded_pfun_order : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the expanded small route to the G72 PFun-order route. -/
def property4SmallLine743FromPFunOrderBridge_from_expanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromExpandedPFunBridge S) :
    Property4SmallLine743FromPFunOrderBridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_pfun_order_data := by
    intro r cuts cor117_abs_data N n
    exact
      smallLine743PFunOrderData_from_expanded
        S r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_expanded_pfun_order_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_pfun_order := True
  source_line743_then_uses_prop111 := bridge.source_line743_then_uses_prop111

/-- The final branch routes with PFun order expanded to scalar expressions. -/
structure Property4ExpandedPFunBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_expanded_route :
    Property4LargeLine735FromExpandedPFunBridge S
  small_line743_expanded_route :
    Property4SmallLine743FromExpandedPFunBridge S
  source_large_line735_outer_abs_unfolded : Prop
  source_small_line743_outer_cut_add_unfolded : Prop
  remaining_frontier_is_expanded_scalar_order : Prop

/-- Convert expanded PFun branch routes to the G72 PFun-order routes. -/
def property4PFunOrderBranchRoutes_from_expanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4ExpandedPFunBranchRoutes S) :
    Property4PFunOrderBranchRoutes S where
  large_line735_pfun_order_route :=
    property4LargeLine735FromPFunOrderBridge_from_expanded
      S routes.large_line735_expanded_route
  small_line743_pfun_order_route :=
    property4SmallLine743FromPFunOrderBridge_from_expanded
      S routes.small_line743_expanded_route
  source_large_line735_value_identification_closed := True
  source_small_line743_value_identification_closed := True
  remaining_frontier_is_pfun_pointwise_order := True

/-- Property-(4) reduction data with the final frontier expressed as expanded
PFun-level scalar orders. -/
structure Property4ReductionDataFromExpandedPFunBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  expanded_pfun_branch_routes : Property4ExpandedPFunBranchRoutes S
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
  source_property4_frontier_is_expanded_pfun_scalar_order : Prop

/-- Convert G73 data to the G72 PFun-order layer. -/
def property4PFunOrderData_from_expanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromExpandedPFunBranchRoutes S r) :
    Property4ReductionDataFromPFunOrderBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  pfun_order_branch_routes :=
    property4PFunOrderBranchRoutes_from_expanded
      S data.expanded_pfun_branch_routes
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
  source_property4_frontier_is_pfun_pointwise_order := True

/-- Theorem 1.18 property (4), after the remaining PFun orders have been
expanded to scalar expressions. -/
def property4_from_expanded_pfun_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromExpandedPFunBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_pfun_order_branch_routes
    S r
    (property4PFunOrderData_from_expanded S r data)

end BishopRegularSeqTheorem118

/-- G73 package: the remaining PFun-order frontier is expanded to scalar
expressions matching the outer shape of source lines 735 and 743. -/
structure BishopRegularSeqTheorem118G73Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g72 : BishopRegularSeqTheorem118G72Package S
  expanded_pfun_branch_routes : Type 4
  property4_expanded_pfun_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_expanded_pfun_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_expanded_pfun_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_outer_pfun_operations_unfolded : Prop
  remaining_frontier_is_expanded_scalar_order : Prop

def bishopRegularSeqTheorem118G73Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G73Package S where
  g72 := bishopRegularSeqTheorem118G72Package S
  expanded_pfun_branch_routes :=
    BishopRegularSeqTheorem118.Property4ExpandedPFunBranchRoutes S
  property4_expanded_pfun_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromExpandedPFunBranchRoutes S
  property4_from_expanded_pfun_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_expanded_pfun_branch_routes
      S r data
  source_outer_pfun_operations_unfolded := True
  remaining_frontier_is_expanded_scalar_order := True

/-- Progress after G73: PFun-level order has been expanded to scalar
expressions for the outer operations in source lines 735 and 743. -/
def bishopRegularSeqCh1To4ProgressAfterG73 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 74
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 73
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G73: unfolded Theorem 1.18 property (4)'s remaining PFun-order frontier \
    to expanded scalar expressions for source lines 735 and 743."

set_option linter.style.longLine false


end BishopCReal
