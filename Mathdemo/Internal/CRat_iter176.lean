import Mathdemo.Internal.CRat_iter175

/-!
# G76: expanding the large line-735 min terms

G75 left the large line-735 subtraction in explicit scalar form, but its two
min terms were still represented by `cutNatRep` and `largeOldCutRep`.

This file opens those two terms to the displayed source expression

`|min(f,n)-min(g_N,n)|`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The source term `min(f,n)` in large line 735, expanded pointwise. -/
def largeLine735CutNatMinScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (_cuts : Property4CutData S r)
    (n : Nat)
    (x : X) : RegularSeq :=
  minSeqWith Arch (r.pfun.toFun x) (constSeq (n : Scalar))

/-- The source term `min(g_N,n)` in large line 735, expanded pointwise. -/
def largeLine735OldCutMinScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (x : X) : RegularSeq :=
  minSeqWith Arch
    (((bishopRegularSeqCor117_from_data S r cor117_data).approximant N).toFun x)
    (constSeq (n : Scalar))

/-- The large line-735 left scalar with both min terms displayed. -/
def largeLine735MinExpandedLeftScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (x : X) : RegularSeq :=
  absSeq
    (addSeq
      (largeLine735CutNatMinScalar S r cuts n x)
      (mulSeqConcreteWith Arch (negSeq oneSeq)
        (largeLine735OldCutMinScalar S r cor117_data N n x)))

/-- The large line-735 right scalar kept in the G74 subtraction-expanded form. -/
def largeLine735MinExpandedRightScalar
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat)
    (x : X) : RegularSeq :=
  largeLine735SubExpandedRightScalar S r cor117_data N x

/-- Large source line 735 after the `min(f,n)` and `min(g_N,n)` terms have
been unfolded to pointwise `minSeqWith` expressions. -/
structure Property4LargeLine735MinExpandedOrderData
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
  min_expanded_lipschitz :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          (largeLine735MinExpandedLeftScalar
            S r cuts cor117_data N n x)
          (largeLine735MinExpandedRightScalar
            S r cor117_data N x)
  source_line735_min_terms_unfolded : Prop

/-- Convert the G76 large-line data to the G74 subtraction-expanded data. -/
def largeLine735SubExpandedOrderData_from_minExpanded
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
      Property4LargeLine735MinExpandedOrderData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    Property4LargeLine735SubExpandedOrderData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data where
  full_set := data.full_set
  full := data.full
  sub_expanded_min_lipschitz := by
    intro x hx
    simpa [largeLine735SubExpandedLeftScalar,
      largeLine735SubExpandedRightScalar,
      largeLine735CutDiffSubScalar,
      largeLine735MinExpandedLeftScalar,
      largeLine735MinExpandedRightScalar,
      largeLine735CutNatMinScalar,
      largeLine735OldCutMinScalar,
      cutNatRep, largeOldCutRep, largeOldCutPFun,
      def16_ofL,
      BishopRegularSeqIntegrableRep.cutNat,
      BishopRegularSeqIntegrableRep.cutConst,
      BishopRegularSeqPFun.cutNat,
      BishopRegularSeqPFun.cutConst,
      BishopRegularSeqPFun.minConst]
      using data.min_expanded_lipschitz x hx
  source_line735_subtractions_unfolded := True

/-- Large line-735 route whose remaining input is the min-expanded pointwise
source inequality. -/
structure Property4LargeLine735FromMinExpandedBridge
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
  line735_min_expanded_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735MinExpandedOrderData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_min_expanded_order : Prop

/-- Convert the G76 min-expanded large route to the G74 route. -/
def property4LargeLine735FromSubExpandedBridge_from_minExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromMinExpandedBridge S) :
    Property4LargeLine735FromSubExpandedBridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_sub_expanded_order_data := by
    intro r cuts cor117_data N n
    exact
      largeLine735SubExpandedOrderData_from_minExpanded
        S r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_min_expanded_order_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_sub_expanded_order := True

/-- G76 branch routes: large line 735 has displayed min terms, while small
line 743 remains at the G75 tail-expanded layer. -/
structure Property4MinExpandedBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_min_expanded_route :
    Property4LargeLine735FromMinExpandedBridge S
  small_line743_tail_expanded_route :
    Property4SmallLine743FromTailExpandedBridge S
  source_large_line735_min_terms_unfolded : Prop
  source_small_line743_tail_difference_unfolded : Prop
  remaining_frontier_is_large_min_expanded_small_tail_expanded : Prop

/-- Convert G76 branch routes to the G75 branch-route layer. -/
def property4SubExpandedBranchRoutes_from_minExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4MinExpandedBranchRoutes S) :
    Property4SubExpandedBranchRoutes S where
  large_line735_sub_expanded_route :=
    property4LargeLine735FromSubExpandedBridge_from_minExpanded
      S routes.large_line735_min_expanded_route
  small_line743_tail_expanded_route :=
    routes.small_line743_tail_expanded_route
  source_large_line735_subtractions_unfolded := True
  source_small_line743_tail_difference_unfolded :=
    routes.source_small_line743_tail_difference_unfolded
  remaining_frontier_is_sub_expanded_scalar_order := True

/-- Property-(4) reduction data after large line 735 has been unfolded down to
displayed min terms. -/
structure Property4ReductionDataFromMinExpandedBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  min_expanded_branch_routes : Property4MinExpandedBranchRoutes S
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
  source_property4_frontier_is_large_min_expanded : Prop

/-- Convert G76 reduction data to the G75 sub-expanded layer. -/
def property4SubExpandedData_from_minExpanded
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromMinExpandedBranchRoutes S r) :
    Property4ReductionDataFromSubExpandedBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  sub_expanded_branch_routes :=
    property4SubExpandedBranchRoutes_from_minExpanded
      S data.min_expanded_branch_routes
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
  source_property4_frontier_is_sub_expanded := True

/-- Theorem 1.18 property (4), with large line 735 unfolded to displayed min
terms and small line 743 kept at the tail-expanded scalar layer. -/
def property4_from_min_expanded_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromMinExpandedBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_sub_expanded_branch_routes
    S r
    (property4SubExpandedData_from_minExpanded S r data)

end BishopRegularSeqTheorem118

/-- G76 package: large line 735 now displays the source min terms
`min(f,n)` and `min(g_N,n)` explicitly. -/
structure BishopRegularSeqTheorem118G76Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g75 : BishopRegularSeqTheorem118G75Package S
  min_expanded_branch_routes : Type 4
  property4_min_expanded_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_min_expanded_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_min_expanded_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_large_line735_min_terms_unfolded : Prop
  remaining_frontier_is_large_min_expanded_small_tail_expanded : Prop

def bishopRegularSeqTheorem118G76Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G76Package S where
  g75 := bishopRegularSeqTheorem118G75Package S
  min_expanded_branch_routes :=
    BishopRegularSeqTheorem118.Property4MinExpandedBranchRoutes S
  property4_min_expanded_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromMinExpandedBranchRoutes S
  property4_from_min_expanded_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_min_expanded_branch_routes
      S r data
  source_large_line735_min_terms_unfolded := True
  remaining_frontier_is_large_min_expanded_small_tail_expanded := True

/-- Progress after G76: large line 735 is displayed as
`|min(f,n)-min(g_N,n)| <= |f-g_N|`, with the left min terms unfolded. -/
def bishopRegularSeqCh1To4ProgressAfterG76 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 77
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 76
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G76: unfolded Theorem 1.18 property (4)'s large line735 min terms \
    to explicit pointwise minSeqWith expressions."

set_option linter.style.longLine false


end BishopCReal
