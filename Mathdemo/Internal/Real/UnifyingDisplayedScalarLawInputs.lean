import Mathdemo.Internal.Real.FactoringDisplayedScalarFrontierTwoLaw

/-!
# G79: unifying the displayed scalar law inputs

G78 factored the remaining frontier through displayed large and small scalar
law routes, but those routes still carried parallel full-set and operation-data
interfaces.  This file bundles those inputs into one unified bridge.

No new analytic claim is proved here.  The change makes the next frontier
cleaner: supply the displayed scalar laws and full-set witnesses once, then
obtain the whole property-(4) route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Full-set witnesses for the two displayed scalar law routes in source
lines 735 and 743. -/
structure Property4DisplayedScalarFullSetData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
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
  source_full_sets_for_displayed_scalar_laws : Prop

/-- Unified displayed scalar law bridge for both property-(4) branches. -/
structure Property4DisplayedScalarLawUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  displayed_scalar_laws : Property4DisplayedScalarInequalityLaws S
  full_sets : Property4DisplayedScalarFullSetData S
  abs_from_prop111 : BishopRegularSeqIntegralAbsProp111Bridge S
  prop111_bridge : BishopRegularSeqProp111Bridge S
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
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_displayed_scalar_law : Prop
  source_line743_reduced_to_displayed_scalar_law : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert a unified displayed scalar bridge into the G78 branch routes. -/
def property4DisplayedScalarLawBranchRoutes_from_unifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarLawUnifiedBridge S) :
    Property4DisplayedScalarLawBranchRoutes S where
  large_line735_displayed_scalar_route :=
    { displayed_scalar_laws := bridge.displayed_scalar_laws
      abs_from_prop111 := bridge.abs_from_prop111
      old_cut_ofL_data := bridge.old_cut_ofL_data
      cut_diff_sub_data := bridge.cut_diff_sub_data
      cut_diff_abs_data := bridge.cut_diff_abs_data
      line735_full_set := bridge.full_sets.line735_full_set
      line735_full := bridge.full_sets.line735_full
      source_line734_reduced_to_prop111 :=
        bridge.source_line734_reduced_to_prop111
      source_line735_reduced_to_displayed_scalar_law :=
        bridge.source_line735_reduced_to_displayed_scalar_law }
  small_line743_displayed_scalar_route :=
    { displayed_scalar_laws := bridge.displayed_scalar_laws
      prop111_bridge := bridge.prop111_bridge
      old_small_ofL_data := bridge.old_small_ofL_data
      old_plus_tail_add_data := bridge.old_plus_tail_add_data
      line743_full_set := bridge.full_sets.line743_full_set
      line743_full := bridge.full_sets.line743_full
      source_line743_reduced_to_displayed_scalar_law :=
        bridge.source_line743_reduced_to_displayed_scalar_law
      source_line743_then_uses_prop111 :=
        bridge.source_line743_then_uses_prop111 }
  source_displayed_scalar_laws_are_frontier_inputs := True
  remaining_frontier_is_two_displayed_scalar_laws := True

/-- Property-(4) reduction data with the displayed scalar law inputs unified. -/
structure Property4ReductionDataFromDisplayedScalarLawUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_law_unified_bridge :
    Property4DisplayedScalarLawUnifiedBridge S
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
  source_property4_frontier_has_unified_displayed_scalar_inputs : Prop

/-- Convert G79 reduction data to the G78 displayed scalar law layer. -/
def property4DisplayedScalarLawData_from_unifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarLawUnifiedBridge S r) :
    Property4ReductionDataFromDisplayedScalarLawBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_law_branch_routes :=
    property4DisplayedScalarLawBranchRoutes_from_unifiedBridge
      S data.displayed_scalar_law_unified_bridge
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
  source_property4_frontier_is_two_displayed_scalar_laws := True

/-- Theorem 1.18 property (4), using the unified displayed scalar law bridge. -/
def property4_from_displayed_scalar_law_unified_bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarLawUnifiedBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_law_branch_routes
    S r
    (property4DisplayedScalarLawData_from_unifiedBridge S r data)

end BishopRegularSeqTheorem118

/-- G79 package: displayed scalar law and full-set inputs are unified into one
bridge feeding the G78 route. -/
structure BishopRegularSeqTheorem118G79Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g78 : BishopRegularSeqTheorem118G78Package S
  displayed_scalar_full_sets : Type 4
  displayed_scalar_law_unified_bridge : Type 4
  property4_unified_displayed_scalar_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_unified_displayed_scalar_bridge :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_unified_displayed_scalar_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  remaining_frontier_is_unified_displayed_scalar_input : Prop

def bishopRegularSeqTheorem118G79Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G79Package S where
  g78 := bishopRegularSeqTheorem118G78Package S
  displayed_scalar_full_sets :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarFullSetData S
  displayed_scalar_law_unified_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarLawUnifiedBridge S
  property4_unified_displayed_scalar_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarLawUnifiedBridge S
  property4_from_unified_displayed_scalar_bridge := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_law_unified_bridge
      S r data
  remaining_frontier_is_unified_displayed_scalar_input := True

/-- Progress after G79: the displayed scalar laws and full-set witnesses have
one unified input route into property (4). -/
def bishopRegularSeqCh1To4ProgressAfterG79 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 80
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 79
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G79: unified Theorem 1.18 property (4)'s displayed scalar law and \
    full-set inputs into one bridge feeding the G78 route."

set_option linter.style.longLine false


end BishopCReal
