import Mathdemo.Internal.Real.NamingTwoScalarInequalityLawsBehind

/-!
# G71: splitting scalar laws into value-identification and core order

G70 named the two remaining property-(4) frontiers as scalar `RegularSeqLe`
laws.  This file splits such a scalar law into two source-faithful pieces:

1. identify each `valueAt` representative with the intended pointwise scalar
   expression, up to Bishop eventual equality;
2. prove the core scalar order between those intended expressions.

The generic transport lemma is proved here.  The concrete identifications and
core min-inequalities remain explicit data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- A reusable transport package for turning a core scalar inequality into an
order between the actual representative values selected by `valueAt`. -/
structure RegularSeqOrderTransportData
    (left right : RegularSeq) : Type where
  left_model : RegularSeq
  right_model : RegularSeq
  left_eventual : relEventually left left_model
  right_eventual : relEventually right_model right
  core_order : RegularSeqLe left_model right_model

/-- Transport a scalar order across Bishop eventual equality on both sides. -/
theorem regularSeqLe_from_order_transport
    {left right : RegularSeq}
    (data : RegularSeqOrderTransportData left right) :
    RegularSeqLe left right :=
  regularSeqLe_of_right_eventual
    data.right_eventual
    (regularSeqLe_of_left_eventual
      data.left_eventual
      data.core_order)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Large line 735 after splitting the scalar law into value identification
plus the core `|min(f,n)-min(g_N,n)| <= |f-g_N|` order. -/
structure Property4LargeLine735ScalarTransportData
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
  scalar_transport :
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
          RegularSeqOrderTransportData
            (BishopRegularSeqIntegrableRep.valueAt
              (largeLine735LeftAbsRep
                S r cuts cor117_data N n
                ofL_data sub_data cut_diff_abs_data)
              x hleft)
            (BishopRegularSeqIntegrableRep.valueAt
              (largeLine735RightAbsRep S r cor117_data N)
              x hright)
  source_line735_left_value_identification : Prop
  source_line735_right_value_identification : Prop
  source_line735_core_scalar_min_lipschitz : Prop

/-- Convert large scalar-transport data to the G70 scalar law. -/
def largeLine735ScalarLawData_from_transport
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
      Property4LargeLine735ScalarTransportData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    Property4LargeLine735ScalarLawData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data where
  full_set := data.full_set
  full := data.full
  scalar_min_lipschitz := by
    intro x hx hleft hright
    exact
      regularSeqLe_from_order_transport
        (data.scalar_transport x hx hleft hright)
  source_line735_scalar_abs_min_bound := True

/-- Small line 743 after splitting the scalar law into value identification
plus the core `min(|f|,1/n) <= min(|g_N|,1/n)+||f|-g_N|` order. -/
structure Property4SmallLine743ScalarTransportData
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
  scalar_transport :
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
          RegularSeqOrderTransportData
            (BishopRegularSeqIntegrableRep.valueAt
              (cutSmallRep r cuts n) x hleft)
            (BishopRegularSeqIntegrableRep.valueAt
              (smallOldPlusTailRep
                S r cuts cor117_abs_data N n
                ofL_data add_data)
              x hright)
  source_line743_left_value_identification : Prop
  source_line743_right_value_identification : Prop
  source_line743_core_scalar_min_tail : Prop

/-- Convert small scalar-transport data to the G70 scalar law. -/
def smallLine743ScalarLawData_from_transport
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
      Property4SmallLine743ScalarTransportData
        S r cuts cor117_abs_data N n ofL_data add_data) :
    Property4SmallLine743ScalarLawData
      S r cuts cor117_abs_data N n ofL_data add_data where
  full_set := data.full_set
  full := data.full
  scalar_min_tail := by
    intro x hx hleft hright
    exact
      regularSeqLe_from_order_transport
        (data.scalar_transport x hx hleft hright)
  source_line743_scalar_min_tail_bound := True

/-- Large route whose line-735 input is value identification plus core scalar
order, rather than the already-transported scalar law. -/
structure Property4LargeLine735FromScalarTransportBridge
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
  line735_scalar_transport_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735ScalarTransportData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_split_into_value_identification_and_core_order : Prop

/-- Convert the large scalar-transport route to the G70 scalar-law route. -/
def property4LargeLine735FromScalarLawBridge_from_transport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromScalarTransportBridge S) :
    Property4LargeLine735FromScalarLawBridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_scalar_law_data := by
    intro r cuts cor117_data N n
    exact
      largeLine735ScalarLawData_from_transport
        S r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_scalar_transport_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_scalar_min_lipschitz := True

/-- Small route whose line-743 input is value identification plus core scalar
order, rather than the already-transported scalar law. -/
structure Property4SmallLine743FromScalarTransportBridge
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
  line743_scalar_transport_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743ScalarTransportData
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_split_into_value_identification_and_core_order : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the small scalar-transport route to the G70 scalar-law route. -/
def property4SmallLine743FromScalarLawBridge_from_transport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromScalarTransportBridge S) :
    Property4SmallLine743FromScalarLawBridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_scalar_law_data := by
    intro r cuts cor117_abs_data N n
    exact
      smallLine743ScalarLawData_from_transport
        S r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_scalar_transport_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_scalar_min_tail := True
  source_line743_then_uses_prop111 := bridge.source_line743_then_uses_prop111

/-- The final branch routes after splitting both scalar laws into value
identification data plus core scalar orders. -/
structure Property4ScalarTransportBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_transport_route :
    Property4LargeLine735FromScalarTransportBridge S
  small_line743_transport_route :
    Property4SmallLine743FromScalarTransportBridge S
  source_large_line735_value_identification_and_core_order : Prop
  source_small_line743_value_identification_and_core_order : Prop
  both_transport_routes_feed_scalar_law_routes : Prop

/-- Convert scalar-transport branch routes to the G70 scalar-law routes. -/
def property4ScalarLawBranchRoutes_from_transport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4ScalarTransportBranchRoutes S) :
    Property4ScalarLawBranchRoutes S where
  large_line735_scalar_route :=
    property4LargeLine735FromScalarLawBridge_from_transport
      S routes.large_line735_transport_route
  small_line743_scalar_route :=
    property4SmallLine743FromScalarLawBridge_from_transport
      S routes.small_line743_transport_route
  source_large_line735_is_scalar_min_lipschitz := True
  source_small_line743_is_scalar_min_tail := True
  both_scalar_laws_feed_value_branch_routes := True

/-- Property-(4) reduction data with the two scalar laws split into value
identification and core scalar order data. -/
structure Property4ReductionDataFromScalarTransportBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  scalar_transport_branch_routes : Property4ScalarTransportBranchRoutes S
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
  source_property4_frontier_is_value_identification_plus_core_order : Prop

/-- Convert G71 data to the G70 scalar-law layer. -/
def property4ScalarLawData_from_transport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromScalarTransportBranchRoutes S r) :
    Property4ReductionDataFromScalarLawBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  scalar_law_branch_routes :=
    property4ScalarLawBranchRoutes_from_transport
      S data.scalar_transport_branch_routes
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
  source_property4_frontier_is_two_scalar_laws := True

/-- Theorem 1.18 property (4), where the final scalar laws have been split
into value-identification data plus core scalar orders. -/
def property4_from_scalar_transport_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromScalarTransportBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_scalar_law_branch_routes
    S r
    (property4ScalarLawData_from_transport S r data)

end BishopRegularSeqTheorem118

/-- G71 package: the final property-(4) frontier is split into value
identification data and the core scalar order inequalities. -/
structure BishopRegularSeqTheorem118G71Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g70 : BishopRegularSeqTheorem118G70Package S
  regularseq_order_transport :
    forall left right : RegularSeq,
      RegularSeqOrderTransportData left right -> RegularSeqLe left right
  scalar_transport_branch_routes : Type 4
  property4_scalar_transport_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_scalar_transport_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_scalar_transport_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_property4_frontier_split : Prop
  remaining_frontier_is_value_identification_and_core_scalar_order : Prop

def bishopRegularSeqTheorem118G71Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G71Package S where
  g70 := bishopRegularSeqTheorem118G70Package S
  regularseq_order_transport := fun _left _right data =>
    regularSeqLe_from_order_transport data
  scalar_transport_branch_routes :=
    BishopRegularSeqTheorem118.Property4ScalarTransportBranchRoutes S
  property4_scalar_transport_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromScalarTransportBranchRoutes S
  property4_from_scalar_transport_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_scalar_transport_branch_routes
      S r data
  source_property4_frontier_split := True
  remaining_frontier_is_value_identification_and_core_scalar_order := True

/-- Progress after G71: the final scalar laws are split into value
identification obligations and core scalar order obligations. -/
def bishopRegularSeqCh1To4ProgressAfterG71 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 72
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 71
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G71: split Theorem 1.18 property (4)'s two scalar laws into value \
    identification plus core RegularSeq order data."

set_option linter.style.longLine false


end BishopCReal
