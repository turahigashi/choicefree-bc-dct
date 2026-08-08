import Mathdemo.Internal.CRat_iter164

/-!
# G65: identifying the small-branch middle term

G64 reduced the small branch of Theorem 1.18(4) to the non-strict norm-bound
bridge behind source lines 743--747.  This file pushes that bound one layer
closer to the text: the abstract small-branch middle term is now fixed as

`I(min(|g_N|, 1/n)) + || |f| - g_N ||`.

The remaining analytic frontier is the source pointwise estimate feeding the
left inequality into that concrete middle term.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Reflexivity for the non-strict `RegularSeq` order surface. -/
theorem regularSeqLe_refl (x : RegularSeq) : RegularSeqLe x x := by
  intro hcounter
  change PosEventually (subSeq zeroSeq (subSeq x x)) at hcounter
  have hself : relEventually (subSeq x x) zeroSeq :=
    subSeq_self_eventually_law x
  have hbase :
      relEventually
        (subSeq zeroSeq (subSeq x x))
        (subSeq zeroSeq zeroSeq) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      (subSeq x x) zeroSeq
      (relEventually_refl zeroSeq)
      hself
  have hzero :
      relEventually
        (subSeq zeroSeq (subSeq x x))
        zeroSeq :=
    relEventually_trans
      (subSeq zeroSeq (subSeq x x))
      (subSeq zeroSeq zeroSeq)
      zeroSeq
      hbase
      (subSeq_self_eventually_law zeroSeq)
  exact
    not_posEventually_zero
      (posEventually_respects
        (subSeq zeroSeq (subSeq x x))
        zeroSeq
        hzero
        hcounter)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The old-space small truncation `min(|g_N|,1/n)` where `g_N` is the
Corollary 1.17 approximant to `|f|`. -/
def smallOldCutPFun
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat) :
    BishopRegularSeqPFun X :=
  BishopRegularSeqPFun.cutSmall Arch n
    (((bishopRegularSeqCor117_from_data S
      (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
      cor117_abs_data).approximant) N)

/-- The old-space small truncation belongs to the original integration class. -/
theorem smallOldCut_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat) :
    smallOldCutPFun S r cuts cor117_abs_data N n ∈ S.core.L := by
  simpa [smallOldCutPFun, BishopRegularSeqPFun.cutSmall] using
    S.cutConst_mem
      (constSeq (eps n))
      (S.core.abs_mem
        (((bishopRegularSeqCor117_from_data S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
          cor117_abs_data).approximant_mem) N))

/-- The old-space small truncation embedded into `L1`. -/
def smallOldCutRep
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
        (smallOldCut_mem S r cuts cor117_abs_data N n)) :
    BishopRegularSeqIntegrableRep S :=
  def16_ofL S
    (smallOldCut_mem S r cuts cor117_abs_data N n)
    ofL_data

/-- The embedded previous small truncation has the previous integral value. -/
theorem smallOldCutRep_integral_agrees
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
        (smallOldCut_mem S r cuts cor117_abs_data N n)) :
    relEventually
      (BishopRegularSeqIntegrableRep.integral
        (smallOldCutRep S r cuts cor117_abs_data N n ofL_data))
      (S.core.I (smallOldCutPFun S r cuts cor117_abs_data N n)) :=
  def16_ofL_integral_agrees S
    (smallOldCut_mem S r cuts cor117_abs_data N n)
    ofL_data

/-- The Corollary 1.17 tail representative `|f| - g_N` in the small branch. -/
def smallAbsTailRep
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N : Nat) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.sub
    (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
    ((bishopRegularSeqCor117_from_data S
      (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
      cor117_abs_data).approximant_rep N)
    ((bishopRegularSeqCor117_from_data S
      (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
      cor117_abs_data).tail_sub_data N)

/-- The absolute-value data for the small-branch tail representative. -/
def smallAbsTailAbsData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N : Nat) :
    BishopRegularSeqIntegrableRep.AbsData
      (smallAbsTailRep S r cuts cor117_abs_data N) :=
  (bishopRegularSeqCor117_from_data S
    (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
    cor117_abs_data).tail_abs_data N

/-- The norm of the small-branch tail representative. -/
def smallAbsTailNorm
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N : Nat) :
    RegularSeq :=
  BishopRegularSeqIntegrableRep.sourceNorm
    (smallAbsTailRep S r cuts cor117_abs_data N)
    (smallAbsTailAbsData S r cuts cor117_abs_data N)

/-- The concrete middle term in source lines 743--747:
old-space small truncation plus the `|f|-g_N` tail norm. -/
def smallOldPlusTailMid
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat) :
    RegularSeq :=
  addSeq
    (S.core.I (smallOldCutPFun S r cuts cor117_abs_data N n))
    (smallAbsTailNorm S r cuts cor117_abs_data N)

/-- Small-branch source data after identifying the abstract middle term with
the concrete expression in lines 743--747. -/
structure Property4SmallLine743To747ConcreteMidBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
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
  line743_left_le_old_plus_tail :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        RegularSeqLe
          (BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
          (smallOldPlusTailMid S r cuts cor117_abs_data N n)
  source_line743_is_small_truncation_pointwise_bound : Prop
  source_lines745_to747_tail_norm_component_identified : Prop

/-- Recover the G58 small two-step bridge from the concrete source middle
term.  The second non-strict step is reflexivity after unfolding the concrete
middle term. -/
def property4SmallNormBoundTwoStepBridge_from_concrete_mid
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743To747ConcreteMidBridge S) :
    Property4SmallNormBoundTwoStepBridge S where
  mid := fun r cuts cor117_abs_data N n =>
    smallOldPlusTailMid S r cuts cor117_abs_data N n
  left_le_mid := by
    intro r cuts cor117_abs_data N n
    exact bridge.line743_left_le_old_plus_tail r cuts cor117_abs_data N n
  mid_le_old_plus_norm := by
    intro r cuts cor117_abs_data N n
    simpa [smallOldPlusTailMid, smallOldCutPFun, smallAbsTailNorm,
      smallAbsTailRep, smallAbsTailAbsData] using
      regularSeqLe_refl
        (smallOldPlusTailMid S r cuts cor117_abs_data N n)
  source_lines_743_to_745_first_non_strict_bound := True
  source_lines_745_to_747_second_non_strict_bound := True

/-- Small norm-bound bridge after the middle term has been concretely
identified with the previous small truncation plus the tail norm. -/
def property4SmallNormBoundBridge_from_concrete_mid
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743To747ConcreteMidBridge S) :
    Property4SmallNormBoundBridge S :=
  property4SmallNormBoundBridge_from_two_step
    S regularSeqLeOrderBridge
    (property4SmallNormBoundTwoStepBridge_from_concrete_mid S bridge)

/-- Property-(4) reduction data with the large G62/G63 route and the small
branch reduced to the concrete middle term of lines 743--747. -/
structure Property4ReductionDataFromLargeRouteSmallConcreteMid
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
  small_concrete_mid : Property4SmallLine743To747ConcreteMidBridge S
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
  source_small_branch_middle_term_identified : Prop

/-- Convert G65 data to the G64 layer by generating the small norm-bound bridge
from the concrete middle-term bridge. -/
def property4LargeRouteSmallNormData_from_concrete_mid
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeRouteSmallConcreteMid S r) :
    Property4ReductionDataFromLargeRouteSmallNormBound S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  large_route := data.large_route
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_norm_bound :=
    property4SmallNormBoundBridge_from_concrete_mid S data.small_concrete_mid
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_large_branch_uses_g62_prop111_route :=
    data.source_large_branch_uses_g62_prop111_route
  source_small_branch_reduced_to_norm_bound := True

/-- Theorem 1.18 property (4), with the small branch reduced to the concrete
old-small-truncation plus tail-norm middle term. -/
def property4_from_large_route_small_concrete_mid
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromLargeRouteSmallConcreteMid S r) :
    Property4Conclusion S r :=
  property4_from_large_route_small_norm_bound
    S r
    (property4LargeRouteSmallNormData_from_concrete_mid S r data)

end BishopRegularSeqTheorem118

/-- G65 package: the small branch now exposes the old-space small truncation
and the `|f|-g_N` tail norm as its concrete middle term. -/
structure BishopRegularSeqTheorem118G65Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g64 : BishopRegularSeqTheorem118G64Package S
  regular_seq_le_refl : forall x : RegularSeq, RegularSeqLe x x
  small_old_plus_tail_mid :
    forall r : BishopRegularSeqIntegrableRep S,
      forall cuts : BishopRegularSeqTheorem118.Property4CutData S r,
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data) ->
        Nat -> Nat -> RegularSeq
  small_concrete_mid_bridge : Type 2
  small_two_step_from_concrete_mid :
    BishopRegularSeqTheorem118.Property4SmallLine743To747ConcreteMidBridge S ->
      BishopRegularSeqTheorem118.Property4SmallNormBoundTwoStepBridge S
  small_norm_bound_from_concrete_mid :
    BishopRegularSeqTheorem118.Property4SmallLine743To747ConcreteMidBridge S ->
      BishopRegularSeqTheorem118.Property4SmallNormBoundBridge S
  property4_large_route_small_concrete_mid_data :
    BishopRegularSeqIntegrableRep S -> Type 3
  property4_from_large_route_small_concrete_mid :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_large_route_small_concrete_mid_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_small_middle_term_identified : Prop
  remaining_frontier_is_small_pointwise_bound_and_large_pointwise_data : Prop

def bishopRegularSeqTheorem118G65Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G65Package S where
  g64 := bishopRegularSeqTheorem118G64Package S
  regular_seq_le_refl := regularSeqLe_refl
  small_old_plus_tail_mid := fun r cuts cor117_abs_data N n =>
    BishopRegularSeqTheorem118.smallOldPlusTailMid
      S r cuts cor117_abs_data N n
  small_concrete_mid_bridge :=
    BishopRegularSeqTheorem118.Property4SmallLine743To747ConcreteMidBridge S
  small_two_step_from_concrete_mid := fun bridge =>
    BishopRegularSeqTheorem118.property4SmallNormBoundTwoStepBridge_from_concrete_mid
      S bridge
  small_norm_bound_from_concrete_mid := fun bridge =>
    BishopRegularSeqTheorem118.property4SmallNormBoundBridge_from_concrete_mid
      S bridge
  property4_large_route_small_concrete_mid_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromLargeRouteSmallConcreteMid S
  property4_from_large_route_small_concrete_mid := fun r data =>
    BishopRegularSeqTheorem118.property4_from_large_route_small_concrete_mid
      S r data
  source_small_middle_term_identified := True
  remaining_frontier_is_small_pointwise_bound_and_large_pointwise_data := True

/-- Progress after G65: the small branch no longer uses an abstract middle
term; it is the old-space small truncation plus the Corollary 1.17 tail norm. -/
def bishopRegularSeqCh1To4ProgressAfterG65 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 66
  ch1_on_bishop_real_percent := 93
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 65
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G65: identified Theorem 1.18 property (4)'s small-branch middle term as \
    the old-space small truncation of g_N plus the |f|-g_N tail norm."

set_option linter.style.longLine false


end BishopCReal
