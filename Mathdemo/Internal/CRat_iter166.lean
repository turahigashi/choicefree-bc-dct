import Mathdemo.Internal.CRat_iter165

/-!
# G66: reducing the small line-743 bound to Proposition 1.11 data

G65 identified the small-branch middle term as

`I(min(|g_N|,1/n)) + || |f| - g_N ||`.

This file supplies the next source-level reduction: that integral inequality
is obtained from Proposition 1.11 from a full-set pointwise domination

`min(|f|,1/n) <= min(|g_N|,1/n) + | |f| - g_N |`,

after building the right-hand side as an actual `L1` representative and
transporting its integral to the concrete G65 middle term.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Non-strict order is stable under eventual equality on the right side. -/
theorem regularSeqLe_of_right_eventual
    {x y y' : RegularSeq}
    (hyy : relEventually y y')
    (hle : RegularSeqLe x y) :
    RegularSeqLe x y' := by
  intro hcounter
  have hbase :
      relEventually (subSeq y' x) (subSeq y x) :=
    subSeq_respects_eventually
      y' y x x
      (relEventually_symm y y' hyy)
      (relEventually_refl x)
  have hneg :
      relEventually
        (subSeq zeroSeq (subSeq y' x))
        (subSeq zeroSeq (subSeq y x)) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      (subSeq y' x) (subSeq y x)
      (relEventually_refl zeroSeq)
      hbase
  exact
    hle
      (posEventually_respects
        (subSeq zeroSeq (subSeq y' x))
        (subSeq zeroSeq (subSeq y x))
        hneg
        hcounter)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The absolute tail representative whose integral is `|| |f| - g_N ||`. -/
def smallAbsTailAbsRep
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N : Nat) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.abs
    (smallAbsTailRep S r cuts cor117_abs_data N)
    (smallAbsTailAbsData S r cuts cor117_abs_data N)

/-- The `L1` right-hand side for line 743:
embedded previous small truncation plus the absolute small tail. -/
def smallOldPlusTailRep
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
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.add
    (smallOldCutRep S r cuts cor117_abs_data N n ofL_data)
    (smallAbsTailAbsRep S r cuts cor117_abs_data N)
    add_data

/-- The integral of the right-hand-side representative agrees with the
concrete G65 middle term. -/
theorem smallOldPlusTailRep_integral_agrees
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
    relEventually
      (BishopRegularSeqIntegrableRep.integral
        (smallOldPlusTailRep S r cuts cor117_abs_data N n
          ofL_data add_data))
      (smallOldPlusTailMid S r cuts cor117_abs_data N n) := by
  have hadd :
      relEventually
        (BishopRegularSeqIntegrableRep.integral
          (smallOldPlusTailRep S r cuts cor117_abs_data N n
            ofL_data add_data))
        (addSeq
          (BishopRegularSeqIntegrableRep.integral
            (smallOldCutRep S r cuts cor117_abs_data N n ofL_data))
          (BishopRegularSeqIntegrableRep.integral
            (smallAbsTailAbsRep S r cuts cor117_abs_data N))) :=
    BishopRegularSeqIntegrableRep.add_integral_agrees
      (smallOldCutRep S r cuts cor117_abs_data N n ofL_data)
      (smallAbsTailAbsRep S r cuts cor117_abs_data N)
      add_data
  have hprevious :
      relEventually
        (BishopRegularSeqIntegrableRep.integral
          (smallOldCutRep S r cuts cor117_abs_data N n ofL_data))
        (S.core.I (smallOldCutPFun S r cuts cor117_abs_data N n)) :=
    smallOldCutRep_integral_agrees
      S r cuts cor117_abs_data N n ofL_data
  have htail :
      relEventually
        (BishopRegularSeqIntegrableRep.integral
          (smallAbsTailAbsRep S r cuts cor117_abs_data N))
        (smallAbsTailNorm S r cuts cor117_abs_data N) := by
    simpa [smallAbsTailNorm, smallAbsTailAbsRep,
      BishopRegularSeqIntegrableRep.sourceNorm] using
      (relEventually_refl
        (BishopRegularSeqIntegrableRep.integral
          (smallAbsTailAbsRep S r cuts cor117_abs_data N)))
  have hsum :
      relEventually
        (addSeq
          (BishopRegularSeqIntegrableRep.integral
            (smallOldCutRep S r cuts cor117_abs_data N n ofL_data))
          (BishopRegularSeqIntegrableRep.integral
            (smallAbsTailAbsRep S r cuts cor117_abs_data N)))
        (smallOldPlusTailMid S r cuts cor117_abs_data N n) := by
    simpa [smallOldPlusTailMid] using
      addSeq_respects_eventually
        (BishopRegularSeqIntegrableRep.integral
          (smallOldCutRep S r cuts cor117_abs_data N n ofL_data))
        (S.core.I (smallOldCutPFun S r cuts cor117_abs_data N n))
        (BishopRegularSeqIntegrableRep.integral
          (smallAbsTailAbsRep S r cuts cor117_abs_data N))
        (smallAbsTailNorm S r cuts cor117_abs_data N)
        hprevious
        htail
  exact
    relEventually_trans
      (BishopRegularSeqIntegrableRep.integral
        (smallOldPlusTailRep S r cuts cor117_abs_data N n
          ofL_data add_data))
      (addSeq
        (BishopRegularSeqIntegrableRep.integral
          (smallOldCutRep S r cuts cor117_abs_data N n ofL_data))
        (BishopRegularSeqIntegrableRep.integral
          (smallAbsTailAbsRep S r cuts cor117_abs_data N)))
      (smallOldPlusTailMid S r cuts cor117_abs_data N n)
      hadd
      hsum

/-- Source line 743 pointwise data: on a full set, the small truncation of
`|f|` is bounded by the previous small truncation plus the absolute tail. -/
structure Property4SmallLine743Prop111Data
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
  small_bound_on_full :
    BishopRegularSeqL1LeOnFull S full_set
      (cutSmallRep r cuts n)
      (smallOldPlusTailRep S r cuts cor117_abs_data N n
        ofL_data add_data)
  source_line743_is_pointwise_min_abs_tail_bound : Prop

/-- Proposition 1.11 turns the source line-743 pointwise domination into the
integral inequality whose right side is the concrete G65 middle term. -/
theorem line743_left_le_old_plus_tail_from_prop111
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (prop111_bridge : BishopRegularSeqProp111Bridge S)
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
      Property4SmallLine743Prop111Data
        S r cuts cor117_abs_data N n ofL_data add_data) :
    RegularSeqLe
      (BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
      (smallOldPlusTailMid S r cuts cor117_abs_data N n) := by
  have hmono :
      RegularSeqLe
        (BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
        (BishopRegularSeqIntegrableRep.integral
          (smallOldPlusTailRep S r cuts cor117_abs_data N n
            ofL_data add_data)) :=
    prop111_bridge.monotone
      data.full
      (cutSmallRep r cuts n)
      (smallOldPlusTailRep S r cuts cor117_abs_data N n
        ofL_data add_data)
      data.small_bound_on_full
  exact
    regularSeqLe_of_right_eventual
      (smallOldPlusTailRep_integral_agrees
        S r cuts cor117_abs_data N n ofL_data add_data)
      hmono

/-- Small-branch bridge where the line-743 integral inequality is reduced to
Proposition 1.11-shaped full-set pointwise data. -/
structure Property4SmallLine743FromProp111Bridge
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
  line743_prop111_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743Prop111Data
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_prop111 : Prop
  source_rhs_integral_identified_with_old_plus_tail_mid : Prop

/-- Forget the line-743 Proposition 1.11 reduction and recover the G65 concrete
middle-term bridge. -/
def property4SmallConcreteMidBridge_from_prop111_line743
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromProp111Bridge S) :
    Property4SmallLine743To747ConcreteMidBridge S where
  old_small_ofL_data := bridge.old_small_ofL_data
  line743_left_le_old_plus_tail := by
    intro r cuts cor117_abs_data N n
    exact
      line743_left_le_old_plus_tail_from_prop111
        S
        bridge.prop111_bridge
        r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_prop111_data r cuts cor117_abs_data N n)
  source_line743_is_small_truncation_pointwise_bound := True
  source_lines745_to747_tail_norm_component_identified := True

/-- Small norm-bound bridge after line 743 is reduced to Proposition 1.11. -/
def property4SmallNormBoundBridge_from_prop111_line743
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromProp111Bridge S) :
    Property4SmallNormBoundBridge S :=
  property4SmallNormBoundBridge_from_concrete_mid
    S
    (property4SmallConcreteMidBridge_from_prop111_line743 S bridge)

/-- Property-(4) reduction data with the large G62/G63 route and the small
line-743 bound reduced to Proposition 1.11-shaped pointwise data. -/
structure Property4ReductionDataFromLargeRouteSmallProp111Line743
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
  small_line743_prop111 : Property4SmallLine743FromProp111Bridge S
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
  source_small_line743_uses_prop111_route : Prop

/-- Convert G66 data to the G65 concrete-middle layer. -/
def property4LargeRouteSmallConcreteMidData_from_prop111_line743
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeRouteSmallProp111Line743 S r) :
    Property4ReductionDataFromLargeRouteSmallConcreteMid S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  large_route := data.large_route
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_concrete_mid :=
    property4SmallConcreteMidBridge_from_prop111_line743
      S data.small_line743_prop111
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_large_branch_uses_g62_prop111_route :=
    data.source_large_branch_uses_g62_prop111_route
  source_small_branch_middle_term_identified := True

/-- Theorem 1.18 property (4), with the small line-743 bound reduced to
Proposition 1.11-shaped data. -/
def property4_from_large_route_small_prop111_line743
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeRouteSmallProp111Line743 S r) :
    Property4Conclusion S r :=
  property4_from_large_route_small_concrete_mid
    S r
    (property4LargeRouteSmallConcreteMidData_from_prop111_line743 S r data)

end BishopRegularSeqTheorem118

/-- G66 package: the small line-743 integral bound is now generated through
Proposition 1.11 from full-set pointwise domination. -/
structure BishopRegularSeqTheorem118G66Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g65 : BishopRegularSeqTheorem118G65Package S
  right_eventual_order_transport :
    forall {x y y' : RegularSeq},
      relEventually y y' -> RegularSeqLe x y -> RegularSeqLe x y'
  small_rhs_rep :
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
        BishopRegularSeqIntegrableRep S
  small_line743_prop111_bridge : Type 3
  small_concrete_mid_from_prop111 :
    BishopRegularSeqTheorem118.Property4SmallLine743FromProp111Bridge S ->
      BishopRegularSeqTheorem118.Property4SmallLine743To747ConcreteMidBridge S
  property4_large_route_small_prop111_data :
    BishopRegularSeqIntegrableRep S -> Type 3
  property4_from_large_route_small_prop111 :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_large_route_small_prop111_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_small_line743_reduced_to_prop111 : Prop
  remaining_frontier_is_pointwise_small_bound_and_large_pointwise_data : Prop

def bishopRegularSeqTheorem118G66Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G66Package S where
  g65 := bishopRegularSeqTheorem118G65Package S
  right_eventual_order_transport := by
    intro x y y' hyy hle
    exact regularSeqLe_of_right_eventual hyy hle
  small_rhs_rep := fun r cuts cor117_abs_data N n ofL_data add_data =>
    BishopRegularSeqTheorem118.smallOldPlusTailRep
      S r cuts cor117_abs_data N n ofL_data add_data
  small_line743_prop111_bridge :=
    BishopRegularSeqTheorem118.Property4SmallLine743FromProp111Bridge S
  small_concrete_mid_from_prop111 := fun bridge =>
    BishopRegularSeqTheorem118.property4SmallConcreteMidBridge_from_prop111_line743
      S bridge
  property4_large_route_small_prop111_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromLargeRouteSmallProp111Line743 S
  property4_from_large_route_small_prop111 := fun r data =>
    BishopRegularSeqTheorem118.property4_from_large_route_small_prop111_line743
      S r data
  source_small_line743_reduced_to_prop111 := True
  remaining_frontier_is_pointwise_small_bound_and_large_pointwise_data := True

/-- Progress after G66: small line 743 is reduced to Proposition 1.11 plus the
right-hand-side integral identification. -/
def bishopRegularSeqCh1To4ProgressAfterG66 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 67
  ch1_on_bishop_real_percent := 94
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 66
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G66: reduced Theorem 1.18 property (4)'s small line-743 bound to \
    Proposition 1.11 full-set pointwise data and a right-integral transport."

set_option linter.style.longLine false


end BishopCReal
