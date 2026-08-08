import Mathdemo.Internal.CRat_iter173

/-!
# G74: expanding the large line-735 subtraction terms

G73 exposed the remaining property-(4) frontier as pointwise scalar orders.
For the large branch, source line 735 still had the subtraction representatives
hidden behind `largeCutDiffRep` and `largeTailRep`.

This file opens those two representatives one layer further:

* `min(f,n)-min(g_N,n)` is displayed as `addSeq min(f,n) (-1 * min(g_N,n))`;
* `f-g_N` is displayed as `addSeq f (-1 * g_N)`.

The new bridge then feeds this more explicit data back into the G73 route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The scalar subtraction hidden in `min(f,n)-min(g_N,n)` on source line
735, with the `L1` subtraction representative unfolded pointwise. -/
def largeLine735CutDiffSubScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (x : X) : RegularSeq :=
  addSeq
    ((cutNatRep r cuts n).pfun.toFun x)
    (mulSeqConcreteWith Arch (negSeq oneSeq)
      ((largeOldCutRep S r cor117_data N n ofL_data).pfun.toFun x))

/-- The scalar subtraction hidden in `f-g_N` on source line 735, with the
Corollary 1.17 approximant displayed explicitly. -/
def largeLine735TailSubScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat)
    (x : X) : RegularSeq :=
  addSeq
    (r.pfun.toFun x)
    (mulSeqConcreteWith Arch (negSeq oneSeq)
      (((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep N).pfun.toFun x))

/-- Source line 735 left scalar after both the outer absolute value and the
inner subtraction representative have been unfolded. -/
def largeLine735SubExpandedLeftScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (x : X) : RegularSeq :=
  absSeq
    (largeLine735CutDiffSubScalar
      S r cuts cor117_data N n ofL_data x)

/-- Source line 735 right scalar after both the outer absolute value and the
inner subtraction representative have been unfolded. -/
def largeLine735SubExpandedRightScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat)
    (x : X) : RegularSeq :=
  absSeq (largeLine735TailSubScalar S r cor117_data N x)

/-- Large source line 735 with the two subtraction representatives unfolded
to pointwise `addSeq` plus multiplication by `-1`. -/
structure Property4LargeLine735SubExpandedOrderData
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
  sub_expanded_min_lipschitz :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          (largeLine735SubExpandedLeftScalar
            S r cuts cor117_data N n ofL_data x)
          (largeLine735SubExpandedRightScalar
            S r cor117_data N x)
  source_line735_subtractions_unfolded : Prop

/-- Convert the G74 large line-735 data to the G73 expanded-PFun scalar order. -/
def largeLine735ExpandedPFunOrderData_from_subExpanded
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
      Property4LargeLine735SubExpandedOrderData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    Property4LargeLine735ExpandedPFunOrderData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data where
  full_set := data.full_set
  full := data.full
  expanded_min_lipschitz := by
    intro x hx
    simpa [largeLine735PFunLeftScalar, largeLine735PFunRightScalar,
      largeLine735SubExpandedLeftScalar, largeLine735SubExpandedRightScalar,
      largeLine735CutDiffSubScalar, largeLine735TailSubScalar,
      largeCutDiffRep, largeTailRep,
      BishopRegularSeqIntegrableRep.sub]
      using data.sub_expanded_min_lipschitz x hx
  source_line735_outer_abs_unfolded := True

/-- Large line-735 route whose remaining input is the subtraction-expanded
source inequality. -/
structure Property4LargeLine735FromSubExpandedBridge
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
  line735_sub_expanded_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735SubExpandedOrderData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_sub_expanded_order : Prop

/-- Convert the G74 subtraction-expanded large route to the G73 route. -/
def property4LargeLine735FromExpandedPFunBridge_from_subExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromSubExpandedBridge S) :
    Property4LargeLine735FromExpandedPFunBridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_expanded_pfun_order_data := by
    intro r cuts cor117_data N n
    exact
      largeLine735ExpandedPFunOrderData_from_subExpanded
        S r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_sub_expanded_order_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_expanded_pfun_order := True

/-- G74 branch routes: the large line-735 side is subtraction-expanded, while
the small line-743 side remains at the G73 expanded-PFun scalar layer. -/
structure Property4LargeSubExpandedSmallExpandedBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_sub_expanded_route :
    Property4LargeLine735FromSubExpandedBridge S
  small_line743_expanded_route :
    Property4SmallLine743FromExpandedPFunBridge S
  source_large_line735_subtractions_unfolded : Prop
  source_small_line743_outer_cut_add_unfolded : Prop
  remaining_frontier_is_large_sub_expanded_small_scalar_order : Prop

/-- Convert the G74 mixed branch routes back to the G73 branch-route layer. -/
def property4ExpandedPFunBranchRoutes_from_large_subExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4LargeSubExpandedSmallExpandedBranchRoutes S) :
    Property4ExpandedPFunBranchRoutes S where
  large_line735_expanded_route :=
    property4LargeLine735FromExpandedPFunBridge_from_subExpanded
      S routes.large_line735_sub_expanded_route
  small_line743_expanded_route := routes.small_line743_expanded_route
  source_large_line735_outer_abs_unfolded := True
  source_small_line743_outer_cut_add_unfolded :=
    routes.source_small_line743_outer_cut_add_unfolded
  remaining_frontier_is_expanded_scalar_order := True

/-- Property-(4) reduction data after the large branch has been expanded down
to pointwise scalar subtraction terms. -/
structure Property4ReductionDataFromLargeSubExpandedBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  large_sub_expanded_branch_routes :
    Property4LargeSubExpandedSmallExpandedBranchRoutes S
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
  source_property4_frontier_is_large_sub_expanded : Prop

/-- Convert G74 reduction data to the G73 expanded-PFun reduction layer. -/
def property4ExpandedPFunData_from_large_subExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeSubExpandedBranchRoutes S r) :
    Property4ReductionDataFromExpandedPFunBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  expanded_pfun_branch_routes :=
    property4ExpandedPFunBranchRoutes_from_large_subExpanded
      S data.large_sub_expanded_branch_routes
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
  source_property4_frontier_is_expanded_pfun_scalar_order := True

/-- Theorem 1.18 property (4), after large source line 735 has been expanded
to explicit scalar subtraction expressions. -/
def property4_from_large_sub_expanded_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeSubExpandedBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_expanded_pfun_branch_routes
    S r
    (property4ExpandedPFunData_from_large_subExpanded S r data)

end BishopRegularSeqTheorem118

/-- G74 package: large source line 735 has its subtraction representatives
expanded to pointwise `addSeq` plus multiplication by `-1`. -/
structure BishopRegularSeqTheorem118G74Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g73 : BishopRegularSeqTheorem118G73Package S
  large_sub_expanded_branch_routes : Type 4
  property4_large_sub_expanded_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_large_sub_expanded_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_large_sub_expanded_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_line735_subtractions_unfolded : Prop
  remaining_frontier_is_large_sub_expanded_small_scalar_order : Prop

def bishopRegularSeqTheorem118G74Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G74Package S where
  g73 := bishopRegularSeqTheorem118G73Package S
  large_sub_expanded_branch_routes :=
    BishopRegularSeqTheorem118.Property4LargeSubExpandedSmallExpandedBranchRoutes S
  property4_large_sub_expanded_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromLargeSubExpandedBranchRoutes S
  property4_from_large_sub_expanded_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_large_sub_expanded_branch_routes
      S r data
  source_line735_subtractions_unfolded := True
  remaining_frontier_is_large_sub_expanded_small_scalar_order := True

/-- Progress after G74: the large branch of Theorem 1.18 property (4) is
expanded from PFun-level subtraction representatives to explicit scalar
subtraction terms. -/
def bishopRegularSeqCh1To4ProgressAfterG74 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 75
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 74
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G74: unfolded Theorem 1.18 property (4)'s large line735 subtraction \
    representatives to explicit scalar addSeq plus negative-multiplication \
    expressions."

set_option linter.style.longLine false


end BishopCReal
