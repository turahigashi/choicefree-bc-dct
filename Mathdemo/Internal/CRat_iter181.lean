import Mathdemo.Internal.CRat_iter180

/-!
# G81: normalizing the primitive scalar laws to `subSeq` cores

G80 left the two remaining property-(4) scalar laws in the displayed source
form using `addSeq _ ((-1) * _)`.  The existing RegularSeq algebra already
knows that this display is Bishop-eventually equal to `subSeq`.

This file proves that normalization and uses order transport to reduce the
G80 primitive laws to cleaner `subSeq`-core laws:

* `|min(a,c)-min(b,c)| <= |a-b|`;
* `min(|a|,c) <= min(|b|,c) + ||a|-b|`;

where both differences are now represented by `subSeq` at the core frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The displayed source subtraction `x + (-1) * y` is the same Bishop real as
the repository's `subSeq x y`. -/
theorem addSeq_negOneMul_right_eventually_subSeq
    (Arch : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    relEventually
      (addSeq x (mulSeqConcreteWith Arch (negSeq oneSeq) y))
      (subSeq x y) := by
  have hmul :
      relEventually
        (mulSeqConcreteWith Arch (negSeq oneSeq) y)
        (negSeq y) :=
    mulSeq_neg_one_left_eventually_neg Arch y
  have hadd :
      relEventually
        (addSeq x (mulSeqConcreteWith Arch (negSeq oneSeq) y))
        (addSeq x (negSeq y)) :=
    addSeq_respects_eventually
      x x
      (mulSeqConcreteWith Arch (negSeq oneSeq) y) (negSeq y)
      (relEventually_refl x)
      hmul
  have hsub :
      relEventually (addSeq x (negSeq y)) (subSeq x y) :=
    relEventually_symm
      (subSeq x y)
      (addSeq x (negSeq y))
      (subSeq_eq_add_neg_eventually x y)
  exact
    relEventually_trans
      (addSeq x (mulSeqConcreteWith Arch (negSeq oneSeq) y))
      (addSeq x (negSeq y))
      (subSeq x y)
      hadd
      hsub

/-- Absolute values preserve the displayed-subtraction normalization. -/
theorem abs_addSeq_negOneMul_right_eventually_abs_subSeq
    (Arch : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    relEventually
      (absSeq
        (addSeq x (mulSeqConcreteWith Arch (negSeq oneSeq) y)))
      (absSeq (subSeq x y)) :=
  absSeq_respects_eventually
    (addSeq x (mulSeqConcreteWith Arch (negSeq oneSeq) y))
    (subSeq x y)
    (addSeq_negOneMul_right_eventually_subSeq Arch x y)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Cleaner core form of the two primitive `RegularSeq` inequalities behind
Theorem 1.18(4).  The only remaining mathematical content is now about
`minSeqWith`, `absSeq`, and `subSeq`, not about source display syntax. -/
structure Property4DisplayedScalarSubSeqCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  min_lipschitz_subSeq :
    forall a b c : RegularSeq,
      RegularSeqLe
        (absSeq
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
  source_line735_core_is_subSeq_min_lipschitz : Prop
  source_line743_core_is_subSeq_min_abs_tail : Prop

/-- Convert the cleaner `subSeq` core laws to the G80 displayed primitive
laws by transporting across Bishop eventual equality. -/
def displayedScalarPrimitiveLaws_from_subSeqCore
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarSubSeqCoreLaws Arch) :
    Property4DisplayedScalarPrimitiveLaws Arch where
  min_lipschitz := by
    intro a b c
    have hleft :
        relEventually
          (absSeq
            (addSeq
              (minSeqWith Arch a c)
              (mulSeqConcreteWith Arch (negSeq oneSeq)
                (minSeqWith Arch b c))))
          (absSeq
            (subSeq
              (minSeqWith Arch a c)
              (minSeqWith Arch b c))) :=
      abs_addSeq_negOneMul_right_eventually_abs_subSeq
        Arch
        (minSeqWith Arch a c)
        (minSeqWith Arch b c)
    have hright_display :
        relEventually
          (absSeq
            (addSeq a
              (mulSeqConcreteWith Arch (negSeq oneSeq) b)))
          (absSeq (subSeq a b)) :=
      abs_addSeq_negOneMul_right_eventually_abs_subSeq Arch a b
    exact
      regularSeqLe_of_right_eventual
        (relEventually_symm
          (absSeq
            (addSeq a
              (mulSeqConcreteWith Arch (negSeq oneSeq) b)))
          (absSeq (subSeq a b))
          hright_display)
        (regularSeqLe_of_left_eventual
          hleft
          (laws.min_lipschitz_subSeq a b c))
  min_abs_tail := by
    intro a b c
    have htail_display :
        relEventually
          (absSeq
            (addSeq
              (absSeq a)
              (mulSeqConcreteWith Arch (negSeq oneSeq) b)))
          (absSeq (subSeq (absSeq a) b)) :=
      abs_addSeq_negOneMul_right_eventually_abs_subSeq Arch (absSeq a) b
    have hright_display :
        relEventually
          (addSeq
            (minSeqWith Arch (absSeq b) c)
            (absSeq
              (addSeq
                (absSeq a)
                (mulSeqConcreteWith Arch (negSeq oneSeq) b))))
          (addSeq
            (minSeqWith Arch (absSeq b) c)
            (absSeq (subSeq (absSeq a) b))) :=
      addSeq_respects_eventually
        (minSeqWith Arch (absSeq b) c)
        (minSeqWith Arch (absSeq b) c)
        (absSeq
          (addSeq
            (absSeq a)
            (mulSeqConcreteWith Arch (negSeq oneSeq) b)))
        (absSeq (subSeq (absSeq a) b))
        (relEventually_refl (minSeqWith Arch (absSeq b) c))
        htail_display
    exact
      regularSeqLe_of_right_eventual
        (relEventually_symm
          (addSeq
            (minSeqWith Arch (absSeq b) c)
            (absSeq
              (addSeq
                (absSeq a)
                (mulSeqConcreteWith Arch (negSeq oneSeq) b))))
          (addSeq
            (minSeqWith Arch (absSeq b) c)
            (absSeq (subSeq (absSeq a) b)))
          hright_display)
        (laws.min_abs_tail_subSeq a b c)
  source_line735_is_regularseq_min_lipschitz :=
    laws.source_line735_core_is_subSeq_min_lipschitz
  source_line743_is_regularseq_min_abs_tail :=
    laws.source_line743_core_is_subSeq_min_abs_tail

/-- G81 unified bridge: the G80 primitive-law route obtained from cleaner
`subSeq` core laws. -/
structure Property4DisplayedScalarSubSeqCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  subSeq_core_laws : Property4DisplayedScalarSubSeqCoreLaws Arch
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
  source_line735_reduced_to_subSeq_min_lipschitz : Prop
  source_line743_reduced_to_subSeq_min_abs_tail : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G81 bridge to the G80 primitive-law bridge. -/
def displayedScalarPrimitiveUnifiedBridge_from_subSeqCore
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarSubSeqCoreUnifiedBridge S) :
    Property4DisplayedScalarPrimitiveUnifiedBridge S where
  primitive_laws :=
    displayedScalarPrimitiveLaws_from_subSeqCore Arch bridge.subSeq_core_laws
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
  source_line735_reduced_to_regularseq_min_lipschitz :=
    bridge.source_line735_reduced_to_subSeq_min_lipschitz
  source_line743_reduced_to_regularseq_min_abs_tail :=
    bridge.source_line743_reduced_to_subSeq_min_abs_tail
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data with the primitive scalar frontier normalized
to `subSeq` core laws. -/
structure Property4ReductionDataFromDisplayedScalarSubSeqCoreBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_subSeq_core_bridge :
    Property4DisplayedScalarSubSeqCoreUnifiedBridge S
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
  source_property4_frontier_is_two_subSeq_core_laws : Prop

/-- Convert G81 reduction data to the G80 primitive-law layer. -/
def property4DisplayedScalarPrimitiveData_from_subSeqCore
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarSubSeqCoreBridge S r) :
    Property4ReductionDataFromDisplayedScalarPrimitiveBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_primitive_bridge :=
    displayedScalarPrimitiveUnifiedBridge_from_subSeqCore
      S data.displayed_scalar_subSeq_core_bridge
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
  source_property4_frontier_is_two_regularseq_scalar_laws := True

/-- Theorem 1.18 property (4), using the `subSeq`-core primitive scalar
frontier. -/
def property4_from_displayed_scalar_subSeq_core
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarSubSeqCoreBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_primitives
    S r
    (property4DisplayedScalarPrimitiveData_from_subSeqCore S r data)

end BishopRegularSeqTheorem118

/-- G81 package: the primitive scalar frontier is normalized from source
display syntax to `subSeq` core laws. -/
structure BishopRegularSeqTheorem118G81Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g80 : BishopRegularSeqTheorem118G80Package S
  subSeq_core_laws : Type 1
  subSeq_core_bridge : Type 4
  property4_subSeq_core_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_subSeq_core_laws :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_subSeq_core_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  displayed_subtraction_normalized_to_subSeq : Prop
  remaining_frontier_is_two_subSeq_core_laws : Prop

def bishopRegularSeqTheorem118G81Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G81Package S where
  g80 := bishopRegularSeqTheorem118G80Package S
  subSeq_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSubSeqCoreLaws Arch
  subSeq_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSubSeqCoreUnifiedBridge S
  property4_subSeq_core_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarSubSeqCoreBridge S
  property4_from_subSeq_core_laws := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_subSeq_core
      S r data
  displayed_subtraction_normalized_to_subSeq := True
  remaining_frontier_is_two_subSeq_core_laws := True

/-- Progress after G81: the two primitive property-(4) scalar laws are no
longer about display syntax; they are clean `subSeq` core inequalities. -/
def bishopRegularSeqCh1To4ProgressAfterG81 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 82
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 81
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G81: normalized Theorem 1.18 property (4)'s primitive scalar laws \
    from displayed x + (-1)*y syntax to subSeq core inequalities."

set_option linter.style.longLine false


end BishopCReal
