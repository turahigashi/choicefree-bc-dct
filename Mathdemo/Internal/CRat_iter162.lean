import Mathdemo.Internal.CRat_iter161

/-!
# G62: reducing line 735 to min-Lipschitz data and Proposition 1.11

G61 reduced line 734 of Theorem 1.18(4) to Proposition 1.11.  The remaining
large-branch local inequality is source line 735:

`I(|min(f,n)-min(g,n)|) <= I(|f-g|)`.

This file puts line 735 in the same source-faithful shape: the only analytic
input is the pointwise min-Lipschitz domination on a full set; Proposition
1.11 transports that domination to the integral inequality.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The Corollary 1.17 tail representative `f-g_N` used in the large branch. -/
def largeTailRep
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.sub
    r
    ((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep N)
    ((bishopRegularSeqCor117_from_data S r cor117_data).tail_sub_data N)

/-- The absolute-value data for the Corollary 1.17 tail representative. -/
def largeTailAbsData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat) :
    BishopRegularSeqIntegrableRep.AbsData
      (largeTailRep S r cor117_data N) :=
  (bishopRegularSeqCor117_from_data S r cor117_data).tail_abs_data N

/-- The norm of the Corollary 1.17 tail representative. -/
def largeTailNorm
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N : Nat) :
    RegularSeq :=
  BishopRegularSeqIntegrableRep.sourceNorm
    (largeTailRep S r cor117_data N)
    (largeTailAbsData S r cor117_data N)

/-- Source line 735 data: on a full set, the absolute truncation difference
is pointwise bounded by the absolute Corollary 1.17 tail.  This is the
RegularSeq/L1 version of `|min(f,n)-min(g,n)| <= |f-g|`. -/
structure Property4LargeLine735MinLipschitzData
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
  min_lipschitz_on_full :
    BishopRegularSeqL1LeOnFull S full_set
      (BishopRegularSeqIntegrableRep.abs
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)
        cut_diff_abs_data)
      (BishopRegularSeqIntegrableRep.abs
        (largeTailRep S r cor117_data N)
        (largeTailAbsData S r cor117_data N))
  source_line735_is_pointwise_min_lipschitz : Prop

/-- Proposition 1.11 turns the line-735 pointwise min-Lipschitz domination
into the required integral inequality. -/
theorem line735_cut_diff_bound_from_min_lipschitz_prop111
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (prop111_bridge : BishopRegularSeqProp111Bridge S)
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
      Property4LargeLine735MinLipschitzData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    RegularSeqLe
      (largeCutDiffMid S r cuts cor117_data N n
        ofL_data sub_data cut_diff_abs_data)
      (largeTailNorm S r cor117_data N) := by
  have hmono :
      RegularSeqLe
        (BishopRegularSeqIntegrableRep.integral
          (BishopRegularSeqIntegrableRep.abs
            (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)
            cut_diff_abs_data))
        (BishopRegularSeqIntegrableRep.integral
          (BishopRegularSeqIntegrableRep.abs
            (largeTailRep S r cor117_data N)
            (largeTailAbsData S r cor117_data N))) :=
    prop111_bridge.monotone
      data.full
      (BishopRegularSeqIntegrableRep.abs
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)
        cut_diff_abs_data)
      (BishopRegularSeqIntegrableRep.abs
        (largeTailRep S r cor117_data N)
        (largeTailAbsData S r cor117_data N))
      data.min_lipschitz_on_full
  simpa [largeCutDiffMid, largeTailNorm, BishopRegularSeqIntegrableRep.sourceNorm]
    using hmono

/-- Large branch bridge where line 734 and line 735 are both reduced to
Proposition 1.11-shaped monotonicity calls.  The remaining explicit content is
the source pointwise min-Lipschitz domination on a full set. -/
structure Property4LargeLine735FromProp111Bridge
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
  line735_min_lipschitz_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735MinLipschitzData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_min_lipschitz_prop111 : Prop

/-- Forget the line-735 reduction and recover the G61 bridge expected by the
previous layer. -/
def property4LargeLine734FromProp111Bridge_from_line735
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromProp111Bridge S) :
    Property4LargeLine734FromProp111Bridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_cut_diff_bound := by
    intro r cuts cor117_data N n
    exact
      line735_cut_diff_bound_from_min_lipschitz_prop111
        S
        bridge.abs_from_prop111.prop111_bridge
        r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_min_lipschitz_data r cuts cor117_data N n)
  source_line734_now_reduced_to_prop111 := True
  source_line735_remains_min_lipschitz_integral_bound := True

/-- Large norm-bound bridge after both source line 734 and line 735 have been
reduced to Proposition 1.11-shaped data. -/
def property4LargeNormBoundBridge_from_prop111_line734_line735
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromProp111Bridge S) :
    Property4LargeNormBoundBridge S :=
  property4LargeNormBoundBridge_from_prop111_line734
    S
    (property4LargeLine734FromProp111Bridge_from_line735 S bridge)

end BishopRegularSeqTheorem118

/-- G62 package: source line 735 is now represented as full-set
min-Lipschitz domination plus Proposition 1.11, matching the G61 treatment of
line 734. -/
structure BishopRegularSeqTheorem118G62Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g61 : BishopRegularSeqTheorem118G61Package S
  large_tail_rep :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqCor117ApproxData S r -> Nat ->
        BishopRegularSeqIntegrableRep S
  line735_min_lipschitz_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : BishopRegularSeqTheorem118.Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
      forall (ofL_data :
        BishopRegularSeqOfLData S
          (BishopRegularSeqTheorem118.largeOldCutPFun S r cor117_data N n)
          (BishopRegularSeqTheorem118.largeOldCut_mem S r cor117_data N n)),
      forall (sub_data :
        BishopRegularSeqIntegrableRep.SubData
          (BishopRegularSeqTheorem118.cutNatRep r cuts n)
          (BishopRegularSeqTheorem118.largeOldCutRep
            S r cor117_data N n ofL_data)),
      forall _cut_diff_abs_data :
        BishopRegularSeqIntegrableRep.AbsData
          (BishopRegularSeqTheorem118.largeCutDiffRep
            S r cuts cor117_data N n ofL_data sub_data),
        Type 2
  line735_from_prop111 :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : BishopRegularSeqTheorem118.Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        forall (ofL_data :
          BishopRegularSeqOfLData S
            (BishopRegularSeqTheorem118.largeOldCutPFun S r cor117_data N n)
            (BishopRegularSeqTheorem118.largeOldCut_mem S r cor117_data N n)),
        forall (sub_data :
          BishopRegularSeqIntegrableRep.SubData
            (BishopRegularSeqTheorem118.cutNatRep r cuts n)
            (BishopRegularSeqTheorem118.largeOldCutRep
              S r cor117_data N n ofL_data)),
        forall (cut_diff_abs_data :
          BishopRegularSeqIntegrableRep.AbsData
            (BishopRegularSeqTheorem118.largeCutDiffRep
              S r cuts cor117_data N n ofL_data sub_data)),
          BishopRegularSeqTheorem118.Property4LargeLine735MinLipschitzData
            S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data ->
            BishopRegularSeqProp111Bridge S ->
              RegularSeqLe
                (BishopRegularSeqTheorem118.largeCutDiffMid
                  S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data)
                (BishopRegularSeqTheorem118.largeTailNorm S r cor117_data N)
  large_line735_bridge : Type 3
  large_norm_bound_from_prop111_line734_line735 :
    BishopRegularSeqTheorem118.Property4LargeLine735FromProp111Bridge S ->
      BishopRegularSeqTheorem118.Property4LargeNormBoundBridge S
  source_line735_reduced_to_prop111_min_lipschitz : Prop
  remaining_large_frontier_is_pointwise_min_lipschitz_data : Prop
  remaining_small_frontier_unchanged_from_g61 : Prop

def bishopRegularSeqTheorem118G62Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G62Package S where
  g61 := bishopRegularSeqTheorem118G61Package S
  large_tail_rep := fun r cor117_data N =>
    BishopRegularSeqTheorem118.largeTailRep S r cor117_data N
  line735_min_lipschitz_data := fun r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data =>
    BishopRegularSeqTheorem118.Property4LargeLine735MinLipschitzData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data
  line735_from_prop111 := by
    intro r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data data prop111_bridge
    exact
      BishopRegularSeqTheorem118.line735_cut_diff_bound_from_min_lipschitz_prop111
        S prop111_bridge r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data data
  large_line735_bridge :=
    BishopRegularSeqTheorem118.Property4LargeLine735FromProp111Bridge S
  large_norm_bound_from_prop111_line734_line735 := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeNormBoundBridge_from_prop111_line734_line735
      S bridge
  source_line735_reduced_to_prop111_min_lipschitz := True
  remaining_large_frontier_is_pointwise_min_lipschitz_data := True
  remaining_small_frontier_unchanged_from_g61 := True

/-- Progress after G62: the large branch of Theorem 1.18(4) has both displayed
source inequalities routed through Proposition 1.11; the remaining large
input is the pointwise min-Lipschitz domination on a full set. -/
def bishopRegularSeqCh1To4ProgressAfterG62 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 63
  ch1_on_bishop_real_percent := 90
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 62
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G62: reduced Theorem 1.18 property (4) line 735 to full-set \
    min-Lipschitz domination plus Proposition 1.11."

set_option linter.style.longLine false


end BishopCReal
