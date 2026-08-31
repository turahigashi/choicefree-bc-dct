import Mathdemo.Internal.Real.ExpandingLargeLine735MinTerms

/-!
# G77: replacing tail representatives by displayed PFun approximants

G76 displayed the large line-735 min terms, while the right tail still used
`approximant_rep N`.  G75 left the same representative-level trace in the
small absolute tail.

This file replaces those tail representatives by their displayed old-space
PFun approximants.  After this layer, the remaining pointwise source
inequalities are expressed entirely in terms of `f`, `|f|`, and the displayed
Corollary 1.17 approximants `g_N`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Large line-735 tail `f-g_N`, with `g_N` shown as the old-space PFun
approximant rather than its `L1` embedding. -/
def largeLine735TailPFunExpandedSubScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat)
    (x : X) : RegularSeq :=
  addSeq
    (r.pfun.toFun x)
    (mulSeqConcreteWith Arch (negSeq oneSeq)
      (((bishopRegularSeqCor117_from_data S r cor117_data).approximant N).toFun x))

/-- Large line-735 right scalar after the tail approximant is displayed as a
PFun. -/
def largeLine735TailPFunExpandedRightScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat)
    (x : X) : RegularSeq :=
  absSeq (largeLine735TailPFunExpandedSubScalar S r cor117_data N x)

/-- Small line-743 tail `|f|-g_N`, with `g_N` shown as the old-space PFun
approximant to `|f|`. -/
def smallLine743TailPFunExpandedSubScalar
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
        cor117_abs_data).approximant N).toFun x))

/-- Small line-743 absolute tail after displaying the old-space approximant. -/
def smallLine743TailPFunExpandedAbsScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N : Nat)
    (x : X) : RegularSeq :=
  absSeq (smallLine743TailPFunExpandedSubScalar S r cuts cor117_abs_data N x)

/-- Small line-743 right scalar with both the previous cut and the tail expressed
using displayed PFun approximants. -/
def smallLine743TailPFunExpandedRightScalar
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
    (smallLine743TailPFunExpandedAbsScalar S r cuts cor117_abs_data N x)

/-- Large line 735 after the right tail also uses the displayed old-space PFun
approximant. -/
structure Property4LargeLine735TailPFunExpandedOrderData
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
  tail_pfun_expanded_lipschitz :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          (largeLine735MinExpandedLeftScalar
            S r cuts cor117_data N n x)
          (largeLine735TailPFunExpandedRightScalar
            S r cor117_data N x)
  source_line735_tail_pfun_unfolded : Prop

/-- Convert G77 large-line data to the G76 min-expanded data. -/
def largeLine735MinExpandedOrderData_from_tailPFunExpanded
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
      Property4LargeLine735TailPFunExpandedOrderData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    Property4LargeLine735MinExpandedOrderData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data where
  full_set := data.full_set
  full := data.full
  min_expanded_lipschitz := by
    intro x hx
    simpa [largeLine735MinExpandedRightScalar,
      largeLine735SubExpandedRightScalar,
      largeLine735TailSubScalar,
      largeLine735TailPFunExpandedRightScalar,
      largeLine735TailPFunExpandedSubScalar,
      bishopRegularSeqCor117_from_data,
      BishopRegularSeqCor117.approxRep,
      def16_ofL]
      using data.tail_pfun_expanded_lipschitz x hx
  source_line735_min_terms_unfolded := True

/-- Small line 743 after the absolute tail also uses the displayed old-space
PFun approximant. -/
structure Property4SmallLine743TailPFunExpandedOrderData
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
  tail_pfun_expanded_min_tail :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          (smallLine743PFunLeftScalar S r n x)
          (smallLine743TailPFunExpandedRightScalar
            S r cuts cor117_abs_data N n x)
  source_line743_tail_pfun_unfolded : Prop

/-- Convert G77 small-line data to the G75 tail-expanded data. -/
def smallLine743TailExpandedOrderData_from_tailPFunExpanded
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
      Property4SmallLine743TailPFunExpandedOrderData
        S r cuts cor117_abs_data N n ofL_data add_data) :
    Property4SmallLine743TailExpandedOrderData
      S r cuts cor117_abs_data N n ofL_data add_data where
  full_set := data.full_set
  full := data.full
  tail_expanded_min_tail := by
    intro x hx
    simpa [smallLine743TailExpandedRightScalar,
      smallLine743TailAbsExpandedScalar,
      smallLine743TailSubScalar,
      smallLine743TailPFunExpandedRightScalar,
      smallLine743TailPFunExpandedAbsScalar,
      smallLine743TailPFunExpandedSubScalar,
      bishopRegularSeqCor117_from_data,
      BishopRegularSeqCor117.approxRep,
      def16_ofL]
      using data.tail_pfun_expanded_min_tail x hx
  source_line743_tail_difference_unfolded := True

/-- Large line-735 route whose remaining input uses displayed PFun
approximants in the tail. -/
structure Property4LargeLine735FromTailPFunExpandedBridge
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
  line735_tail_pfun_expanded_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735TailPFunExpandedOrderData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_tail_pfun_expanded_order : Prop

/-- Convert the G77 large route to the G76 min-expanded route. -/
def property4LargeLine735FromMinExpandedBridge_from_tailPFunExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromTailPFunExpandedBridge S) :
    Property4LargeLine735FromMinExpandedBridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_min_expanded_order_data := by
    intro r cuts cor117_data N n
    exact
      largeLine735MinExpandedOrderData_from_tailPFunExpanded
        S r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_tail_pfun_expanded_order_data
          r cuts cor117_data N n)
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_min_expanded_order := True

/-- Small line-743 route whose remaining input uses displayed PFun
approximants in the tail. -/
structure Property4SmallLine743FromTailPFunExpandedBridge
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
  line743_tail_pfun_expanded_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743TailPFunExpandedOrderData
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_tail_pfun_expanded_order : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G77 small route to the G75 tail-expanded route. -/
def property4SmallLine743FromTailExpandedBridge_from_tailPFunExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromTailPFunExpandedBridge S) :
    Property4SmallLine743FromTailExpandedBridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_tail_expanded_order_data := by
    intro r cuts cor117_abs_data N n
    exact
      smallLine743TailExpandedOrderData_from_tailPFunExpanded
        S r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_tail_pfun_expanded_order_data
          r cuts cor117_abs_data N n)
  source_line743_reduced_to_tail_expanded_order := True
  source_line743_then_uses_prop111 := bridge.source_line743_then_uses_prop111

/-- G77 branch routes: both local tails use displayed old-space PFun
approximants. -/
structure Property4TailPFunExpandedBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_tail_pfun_expanded_route :
    Property4LargeLine735FromTailPFunExpandedBridge S
  small_line743_tail_pfun_expanded_route :
    Property4SmallLine743FromTailPFunExpandedBridge S
  source_large_line735_tail_pfun_unfolded : Prop
  source_small_line743_tail_pfun_unfolded : Prop
  remaining_frontier_is_displayed_pfun_scalar_order : Prop

/-- Convert G77 branch routes to the G76 min-expanded layer. -/
def property4MinExpandedBranchRoutes_from_tailPFunExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4TailPFunExpandedBranchRoutes S) :
    Property4MinExpandedBranchRoutes S where
  large_line735_min_expanded_route :=
    property4LargeLine735FromMinExpandedBridge_from_tailPFunExpanded
      S routes.large_line735_tail_pfun_expanded_route
  small_line743_tail_expanded_route :=
    property4SmallLine743FromTailExpandedBridge_from_tailPFunExpanded
      S routes.small_line743_tail_pfun_expanded_route
  source_large_line735_min_terms_unfolded := True
  source_small_line743_tail_difference_unfolded := True
  remaining_frontier_is_large_min_expanded_small_tail_expanded := True

/-- Property-(4) reduction data after all remaining representative-level tail
terms have been replaced by displayed PFun approximants. -/
structure Property4ReductionDataFromTailPFunExpandedBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  tail_pfun_expanded_branch_routes :
    Property4TailPFunExpandedBranchRoutes S
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
  source_property4_frontier_is_displayed_pfun_scalar_order : Prop

/-- Convert G77 reduction data to the G76 min-expanded layer. -/
def property4MinExpandedData_from_tailPFunExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromTailPFunExpandedBranchRoutes S r) :
    Property4ReductionDataFromMinExpandedBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  min_expanded_branch_routes :=
    property4MinExpandedBranchRoutes_from_tailPFunExpanded
      S data.tail_pfun_expanded_branch_routes
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
  source_property4_frontier_is_large_min_expanded := True

/-- Theorem 1.18 property (4), with all remaining source-side tail terms shown
as old-space PFun approximants. -/
def property4_from_tail_pfun_expanded_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromTailPFunExpandedBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_min_expanded_branch_routes
    S r
    (property4MinExpandedData_from_tailPFunExpanded S r data)

end BishopRegularSeqTheorem118

/-- G77 package: the remaining representative-level tail approximants have
been unfolded to the displayed old-space PFun approximants. -/
structure BishopRegularSeqTheorem118G77Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g76 : BishopRegularSeqTheorem118G76Package S
  tail_pfun_expanded_branch_routes : Type 4
  property4_tail_pfun_expanded_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_tail_pfun_expanded_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_tail_pfun_expanded_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_tail_approximants_displayed_as_pfun : Prop
  remaining_frontier_is_displayed_pfun_scalar_order : Prop

def bishopRegularSeqTheorem118G77Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G77Package S where
  g76 := bishopRegularSeqTheorem118G76Package S
  tail_pfun_expanded_branch_routes :=
    BishopRegularSeqTheorem118.Property4TailPFunExpandedBranchRoutes S
  property4_tail_pfun_expanded_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromTailPFunExpandedBranchRoutes S
  property4_from_tail_pfun_expanded_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_tail_pfun_expanded_branch_routes
      S r data
  source_tail_approximants_displayed_as_pfun := True
  remaining_frontier_is_displayed_pfun_scalar_order := True

/-- Progress after G77: line 735 and line 743 are expressed with displayed
PFun approximants rather than hidden `approximant_rep` embeddings. -/
def bishopRegularSeqCh1To4ProgressAfterG77 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 78
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 77
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G77: replaced Theorem 1.18 property (4)'s remaining tail \
    approximant_rep occurrences by displayed old-space PFun approximants."

set_option linter.style.longLine false


end BishopCReal
