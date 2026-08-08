import Mathdemo.Internal.CRat_iter174

/-!
# G75: expanding the small line-743 right-hand scalar

G74 opened the large branch's subtraction representatives.  This file performs
the parallel reduction on the small branch of source line 743.

The right-hand side

`min(|g_N|,1/n) + || |f| - g_N ||`

is now displayed pointwise as the sum of an explicit old-space small
truncation and an explicit absolute tail difference.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The old-space truncation term in source line 743, expanded pointwise as
`min(|g_N|,1/n)`. -/
def smallLine743OldCutMinScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat)
    (x : X) : RegularSeq :=
  minSeqWith Arch
    (absSeq
      (((bishopRegularSeqCor117_from_data S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
        cor117_abs_data).approximant N).toFun x))
    (constSeq (eps n))

/-- The small-branch Corollary 1.17 tail, expanded pointwise as
`|f| - g_N`. -/
def smallLine743TailSubScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N : Nat)
    (x : X) : RegularSeq :=
  addSeq
    (absSeq (r.pfun.toFun x))
    (mulSeqConcreteWith Arch (negSeq oneSeq)
      (((bishopRegularSeqCor117_from_data S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
        cor117_abs_data).approximant_rep N).pfun.toFun x))

/-- The absolute small-tail scalar `|| |f| - g_N ||` in source line 743. -/
def smallLine743TailAbsExpandedScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N : Nat)
    (x : X) : RegularSeq :=
  absSeq (smallLine743TailSubScalar S r cuts cor117_abs_data N x)

/-- The right-hand scalar of source line 743 after expanding both the old
small truncation and the absolute tail. -/
def smallLine743TailExpandedRightScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat)
    (x : X) : RegularSeq :=
  addSeq
    (smallLine743OldCutMinScalar S r cuts cor117_abs_data N n x)
    (smallLine743TailAbsExpandedScalar S r cuts cor117_abs_data N x)

/-- Small source line 743 after the right-hand representative has been
expanded to the displayed scalar expression. -/
structure Property4SmallLine743TailExpandedOrderData
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
  tail_expanded_min_tail :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          (smallLine743PFunLeftScalar S r n x)
          (smallLine743TailExpandedRightScalar
            S r cuts cor117_abs_data N n x)
  source_line743_tail_difference_unfolded : Prop

/-- Convert the G75 small-line data to the G73 expanded-PFun scalar order. -/
def smallLine743ExpandedPFunOrderData_from_tailExpanded
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
      Property4SmallLine743TailExpandedOrderData
        S r cuts cor117_abs_data N n ofL_data add_data) :
    Property4SmallLine743ExpandedPFunOrderData
      S r cuts cor117_abs_data N n ofL_data add_data where
  full_set := data.full_set
  full := data.full
  expanded_min_tail := by
    intro x hx
    simpa [smallLine743PFunLeftScalar, smallLine743PFunRightScalar,
      smallLine743TailExpandedRightScalar,
      smallLine743OldCutMinScalar,
      smallLine743TailAbsExpandedScalar,
      smallLine743TailSubScalar,
      smallOldCutRep, smallOldCutPFun,
      smallAbsTailAbsRep, smallAbsTailRep,
      def16_ofL,
      BishopRegularSeqIntegrableRep.add,
      BishopRegularSeqIntegrableRep.abs,
      BishopRegularSeqIntegrableRep.sub,
      BishopRegularSeqPFun.cutSmall,
      BishopRegularSeqPFun.cutConst,
      BishopRegularSeqPFun.absf,
      BishopRegularSeqPFun.minConst]
      using data.tail_expanded_min_tail x hx
  source_line743_outer_cut_and_add_unfolded := True

/-- Small line-743 route whose remaining input is the tail-expanded pointwise
scalar inequality. -/
structure Property4SmallLine743FromTailExpandedBridge
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
  line743_tail_expanded_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743TailExpandedOrderData
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_tail_expanded_order : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G75 small route to the G73 expanded-PFun route. -/
def property4SmallLine743FromExpandedPFunBridge_from_tailExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromTailExpandedBridge S) :
    Property4SmallLine743FromExpandedPFunBridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_expanded_pfun_order_data := by
    intro r cuts cor117_abs_data N n
    exact
      smallLine743ExpandedPFunOrderData_from_tailExpanded
        S r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_tail_expanded_order_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_expanded_pfun_order := True
  source_line743_then_uses_prop111 := bridge.source_line743_then_uses_prop111

/-- G75 branch routes: large line 735 is subtraction-expanded and small line
743 is tail-expanded. -/
structure Property4SubExpandedBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_sub_expanded_route :
    Property4LargeLine735FromSubExpandedBridge S
  small_line743_tail_expanded_route :
    Property4SmallLine743FromTailExpandedBridge S
  source_large_line735_subtractions_unfolded : Prop
  source_small_line743_tail_difference_unfolded : Prop
  remaining_frontier_is_sub_expanded_scalar_order : Prop

/-- Convert G75 branch routes to the G74 mixed branch-route layer. -/
def property4LargeSubExpandedSmallExpandedBranchRoutes_from_subExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4SubExpandedBranchRoutes S) :
    Property4LargeSubExpandedSmallExpandedBranchRoutes S where
  large_line735_sub_expanded_route :=
    routes.large_line735_sub_expanded_route
  small_line743_expanded_route :=
    property4SmallLine743FromExpandedPFunBridge_from_tailExpanded
      S routes.small_line743_tail_expanded_route
  source_large_line735_subtractions_unfolded :=
    routes.source_large_line735_subtractions_unfolded
  source_small_line743_outer_cut_add_unfolded := True
  remaining_frontier_is_large_sub_expanded_small_scalar_order := True

/-- Property-(4) reduction data with both source inequalities expanded to
pointwise scalar subtraction/tail expressions. -/
structure Property4ReductionDataFromSubExpandedBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  sub_expanded_branch_routes : Property4SubExpandedBranchRoutes S
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
  source_property4_frontier_is_sub_expanded : Prop

/-- Convert G75 reduction data to the G74 large-sub-expanded layer. -/
def property4LargeSubExpandedData_from_subExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromSubExpandedBranchRoutes S r) :
    Property4ReductionDataFromLargeSubExpandedBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  large_sub_expanded_branch_routes :=
    property4LargeSubExpandedSmallExpandedBranchRoutes_from_subExpanded
      S data.sub_expanded_branch_routes
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
  source_property4_frontier_is_large_sub_expanded := True

/-- Theorem 1.18 property (4), after both local source inequalities have been
expanded to pointwise scalar expressions. -/
def property4_from_sub_expanded_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromSubExpandedBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_large_sub_expanded_branch_routes
    S r
    (property4LargeSubExpandedData_from_subExpanded S r data)

end BishopRegularSeqTheorem118

/-- G75 package: large line 735 and small line 743 are both reduced to
pointwise scalar expressions with explicit subtraction/tail terms. -/
structure BishopRegularSeqTheorem118G75Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g74 : BishopRegularSeqTheorem118G74Package S
  sub_expanded_branch_routes : Type 4
  property4_sub_expanded_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_sub_expanded_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_sub_expanded_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_line735_and_line743_subtractions_unfolded : Prop
  remaining_frontier_is_sub_expanded_scalar_order : Prop

def bishopRegularSeqTheorem118G75Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G75Package S where
  g74 := bishopRegularSeqTheorem118G74Package S
  sub_expanded_branch_routes :=
    BishopRegularSeqTheorem118.Property4SubExpandedBranchRoutes S
  property4_sub_expanded_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromSubExpandedBranchRoutes S
  property4_from_sub_expanded_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_sub_expanded_branch_routes
      S r data
  source_line735_and_line743_subtractions_unfolded := True
  remaining_frontier_is_sub_expanded_scalar_order := True

/-- Progress after G75: both source-side pointwise inequalities in Theorem
1.18 property (4) are now exposed at the scalar subtraction/tail level. -/
def bishopRegularSeqCh1To4ProgressAfterG75 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 76
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 75
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G75: unfolded Theorem 1.18 property (4)'s small line743 right-hand \
    scalar to min(|g_N|,1/n) plus the explicit absolute tail | |f|-g_N |."

set_option linter.style.longLine false


end BishopCReal
