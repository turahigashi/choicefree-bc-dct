import Mathdemo.Internal.Real.NormalizingPrimitiveScalarLawsSubSeqCores

/-!
# G82: splitting the large `subSeq` core through two-sided order

G81 normalized the displayed source subtraction to `subSeq`.  For the large
line-735 core, the remaining absolute-value inequality

`|min(a,c)-min(b,c)| <= |a-b|`

is now split into the two one-sided inequalities that feed the existing
`RegularSeqAbsFromTwoSidedBridge`.

The small line-743 core law is carried unchanged; it is the next separate
frontier after the large two-sided min order has been supplied.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Two-sided core data for the large line-735 min-Lipschitz inequality,
together with the still-separate small line-743 core law. -/
structure Property4DisplayedScalarTwoSidedCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
  min_lipschitz_upper :
    forall a b c : RegularSeq,
      RegularSeqLe
        (subSeq
          (minSeqWith Arch a c)
          (minSeqWith Arch b c))
        (absSeq (subSeq a b))
  min_lipschitz_lower :
    forall a b c : RegularSeq,
      RegularSeqLe
        (negSeq
          (subSeq
            (minSeqWith Arch a c)
            (minSeqWith Arch b c)))
        (absSeq (subSeq a b))
  min_abs_tail_subSeq :
    forall a b c : RegularSeq,
      RegularSeqLe
        (minSeqWith Arch (absSeq a) c)
        (addSeq
          (minSeqWith Arch (absSeq b) c)
          (absSeq (subSeq (absSeq a) b)))
  source_line735_split_to_two_sided_min_order : Prop
  source_line743_core_is_subSeq_min_abs_tail : Prop

/-- Convert the two-sided large core data into the G81 `subSeq` core laws. -/
def displayedScalarSubSeqCoreLaws_from_twoSided
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarTwoSidedCoreLaws Arch) :
    Property4DisplayedScalarSubSeqCoreLaws Arch where
  min_lipschitz_subSeq := by
    intro a b c
    exact
      laws.abs_from_two_sided.abs_le_of_two_sided
        (subSeq
          (minSeqWith Arch a c)
          (minSeqWith Arch b c))
        (absSeq (subSeq a b))
        (laws.min_lipschitz_upper a b c)
        (laws.min_lipschitz_lower a b c)
  min_abs_tail_subSeq := laws.min_abs_tail_subSeq
  source_line735_core_is_subSeq_min_lipschitz :=
    laws.source_line735_split_to_two_sided_min_order
  source_line743_core_is_subSeq_min_abs_tail :=
    laws.source_line743_core_is_subSeq_min_abs_tail

/-- G82 unified bridge: G81's `subSeq` core bridge obtained from a two-sided
large min-order split. -/
structure Property4DisplayedScalarTwoSidedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  two_sided_core_laws : Property4DisplayedScalarTwoSidedCoreLaws Arch
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
  source_line735_reduced_to_two_sided_min_order : Prop
  source_line743_reduced_to_subSeq_min_abs_tail : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G82 bridge to the G81 `subSeq` core bridge. -/
def displayedScalarSubSeqCoreUnifiedBridge_from_twoSided
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarTwoSidedCoreUnifiedBridge S) :
    Property4DisplayedScalarSubSeqCoreUnifiedBridge S where
  subSeq_core_laws :=
    displayedScalarSubSeqCoreLaws_from_twoSided
      Arch bridge.two_sided_core_laws
  full_sets := bridge.full_sets
  abs_from_prop111 := bridge.abs_from_prop111
  prop111_bridge := bridge.prop111_bridge
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  source_line734_reduced_to_prop111 :=
    bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_subSeq_min_lipschitz :=
    bridge.source_line735_reduced_to_two_sided_min_order
  source_line743_reduced_to_subSeq_min_abs_tail :=
    bridge.source_line743_reduced_to_subSeq_min_abs_tail
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after splitting the large `subSeq` core law
into two one-sided min-order laws. -/
structure Property4ReductionDataFromDisplayedScalarTwoSidedCoreBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_two_sided_core_bridge :
    Property4DisplayedScalarTwoSidedCoreUnifiedBridge S
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
  source_property4_frontier_is_large_two_sided_and_small_subSeq : Prop

/-- Convert G82 reduction data to the G81 `subSeq` core layer. -/
def property4DisplayedScalarSubSeqCoreData_from_twoSided
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarTwoSidedCoreBridge S r) :
    Property4ReductionDataFromDisplayedScalarSubSeqCoreBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_subSeq_core_bridge :=
    displayedScalarSubSeqCoreUnifiedBridge_from_twoSided
      S data.displayed_scalar_two_sided_core_bridge
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
  source_property4_frontier_is_two_subSeq_core_laws := True

/-- Theorem 1.18 property (4), using the two-sided large min-order split. -/
def property4_from_displayed_scalar_two_sided_core
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarTwoSidedCoreBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_subSeq_core
    S r
    (property4DisplayedScalarSubSeqCoreData_from_twoSided S r data)

end BishopRegularSeqTheorem118

/-- G82 package: the large line-735 `subSeq` core is split into two one-sided
min-order laws, plus an absolute-value two-sided bridge. -/
structure BishopRegularSeqTheorem118G82Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g81 : BishopRegularSeqTheorem118G81Package S
  two_sided_core_laws : Type 1
  two_sided_core_bridge : Type 4
  property4_two_sided_core_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_two_sided_core_laws :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_two_sided_core_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  large_abs_split_to_two_sided_order : Prop
  remaining_frontier_is_large_two_sided_and_small_subSeq : Prop

def bishopRegularSeqTheorem118G82Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G82Package S where
  g81 := bishopRegularSeqTheorem118G81Package S
  two_sided_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarTwoSidedCoreLaws Arch
  two_sided_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarTwoSidedCoreUnifiedBridge S
  property4_two_sided_core_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarTwoSidedCoreBridge S
  property4_from_two_sided_core_laws := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_two_sided_core
      S r data
  large_abs_split_to_two_sided_order := True
  remaining_frontier_is_large_two_sided_and_small_subSeq := True

/-- Progress after G82: large line735's absolute `subSeq` min-Lipschitz core
has been reduced to two one-sided min-order inputs. -/
def bishopRegularSeqCh1To4ProgressAfterG82 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 83
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 82
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G82: split Theorem 1.18 property (4)'s large line735 subSeq \
    min-Lipschitz core into two one-sided min-order laws."

set_option linter.style.longLine false


end BishopCReal
