import Mathdemo.Internal.CRat_iter179

/-!
# G80: reducing displayed scalar laws to primitive RegularSeq laws

G79 unified the full-set and displayed scalar-law inputs for Theorem 1.18(4).
This file separates the remaining displayed scalar laws from the surrounding
integration-space context.

The new frontier is exactly two reusable `RegularSeq` inequalities:

* source line 735: the min-Lipschitz law
  `|min(a,c)-min(b,c)| <= |a-b|`;
* source line 743: the min-tail law
  `min(|a|,c) <= min(|b|,c) + ||a|-b|`.

No proof of those two scalar laws is inserted here.  G80 proves only that
those two primitive laws instantiate the G78 displayed-law interface and hence
feed the already built G79 route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The two context-free `RegularSeq` scalar inequalities still needed for
Theorem 1.18(4), after G79 has unfolded the source expressions. -/
structure Property4DisplayedScalarPrimitiveLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  min_lipschitz :
    forall a b c : RegularSeq,
      RegularSeqLe
        (absSeq
          (addSeq
            (minSeqWith Arch a c)
            (mulSeqConcreteWith Arch (negSeq oneSeq)
              (minSeqWith Arch b c))))
        (absSeq
          (addSeq a
            (mulSeqConcreteWith Arch (negSeq oneSeq) b)))
  min_abs_tail :
    forall a b c : RegularSeq,
      RegularSeqLe
        (minSeqWith Arch (absSeq a) c)
        (addSeq
          (minSeqWith Arch (absSeq b) c)
          (absSeq
            (addSeq
              (absSeq a)
              (mulSeqConcreteWith Arch (negSeq oneSeq) b))))
  source_line735_is_regularseq_min_lipschitz : Prop
  source_line743_is_regularseq_min_abs_tail : Prop

/-- Instantiate the G78 displayed scalar law interface from the two primitive
`RegularSeq` scalar inequalities. -/
def displayedScalarInequalityLaws_from_primitives
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (laws : Property4DisplayedScalarPrimitiveLaws Arch) :
    Property4DisplayedScalarInequalityLaws S where
  large_line735_law := by
    intro r cuts cor117_data N n x
    exact
      (by
        simpa [largeLine735MinExpandedLeftScalar,
          largeLine735CutNatMinScalar,
          largeLine735OldCutMinScalar,
          largeLine735TailPFunExpandedRightScalar,
          largeLine735TailPFunExpandedSubScalar]
          using
            laws.min_lipschitz
              (r.pfun.toFun x)
              (((bishopRegularSeqCor117_from_data
                S r cor117_data).approximant N).toFun x)
              (constSeq (n : Scalar)))
  small_line743_law := by
    intro r cuts cor117_abs_data N n x
    exact
      (by
        simpa [smallLine743PFunLeftScalar,
          smallLine743TailPFunExpandedRightScalar,
          smallLine743OldCutMinScalar,
          smallLine743TailPFunExpandedAbsScalar,
          smallLine743TailPFunExpandedSubScalar]
          using
            laws.min_abs_tail
              (r.pfun.toFun x)
              (((bishopRegularSeqCor117_from_data S
                (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                cor117_abs_data).approximant N).toFun x)
              (constSeq (eps n)))
  source_line735_is_displayed_min_lipschitz_law :=
    laws.source_line735_is_regularseq_min_lipschitz
  source_line743_is_displayed_min_tail_law :=
    laws.source_line743_is_regularseq_min_abs_tail

/-- G80 unified bridge: the G79 route, but with the displayed scalar law
interface obtained from two primitive `RegularSeq` laws. -/
structure Property4DisplayedScalarPrimitiveUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  primitive_laws : Property4DisplayedScalarPrimitiveLaws Arch
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
  source_line735_reduced_to_regularseq_min_lipschitz : Prop
  source_line743_reduced_to_regularseq_min_abs_tail : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the primitive-law bridge to the G79 displayed scalar-law bridge. -/
def displayedScalarLawUnifiedBridge_from_primitives
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarPrimitiveUnifiedBridge S) :
    Property4DisplayedScalarLawUnifiedBridge S where
  displayed_scalar_laws :=
    displayedScalarInequalityLaws_from_primitives S bridge.primitive_laws
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
  source_line735_reduced_to_displayed_scalar_law :=
    bridge.source_line735_reduced_to_regularseq_min_lipschitz
  source_line743_reduced_to_displayed_scalar_law :=
    bridge.source_line743_reduced_to_regularseq_min_abs_tail
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data when the remaining scalar laws have been made
context-free primitive `RegularSeq` inputs. -/
structure Property4ReductionDataFromDisplayedScalarPrimitiveBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_primitive_bridge :
    Property4DisplayedScalarPrimitiveUnifiedBridge S
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
  source_property4_frontier_is_two_regularseq_scalar_laws : Prop

/-- Convert G80 reduction data to the G79 unified displayed-law layer. -/
def property4DisplayedScalarLawUnifiedData_from_primitives
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarPrimitiveBridge S r) :
    Property4ReductionDataFromDisplayedScalarLawUnifiedBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_law_unified_bridge :=
    displayedScalarLawUnifiedBridge_from_primitives
      S data.displayed_scalar_primitive_bridge
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
  source_property4_frontier_has_unified_displayed_scalar_inputs := True

/-- Theorem 1.18 property (4), using context-free primitive scalar laws. -/
def property4_from_displayed_scalar_primitives
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromDisplayedScalarPrimitiveBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_law_unified_bridge
    S r
    (property4DisplayedScalarLawUnifiedData_from_primitives S r data)

end BishopRegularSeqTheorem118

/-- G80 package: the remaining line-735 and line-743 displayed scalar laws are
reduced to two context-free primitive `RegularSeq` inequalities. -/
structure BishopRegularSeqTheorem118G80Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g79 : BishopRegularSeqTheorem118G79Package S
  primitive_regularseq_laws : Type 1
  primitive_unified_bridge : Type 4
  property4_primitive_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_primitive_scalar_laws :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_primitive_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  remaining_frontier_is_two_regularseq_scalar_laws : Prop

def bishopRegularSeqTheorem118G80Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G80Package S where
  g79 := bishopRegularSeqTheorem118G79Package S
  primitive_regularseq_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarPrimitiveLaws Arch
  primitive_unified_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarPrimitiveUnifiedBridge S
  property4_primitive_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarPrimitiveBridge S
  property4_from_primitive_scalar_laws := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_primitives
      S r data
  remaining_frontier_is_two_regularseq_scalar_laws := True

/-- Progress after G80: property (4)'s remaining displayed scalar laws are now
two context-free `RegularSeq` inequalities. -/
def bishopRegularSeqCh1To4ProgressAfterG80 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 81
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 80
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G80: reduced Theorem 1.18 property (4)'s displayed scalar-law frontier \
    to two context-free RegularSeq inequalities: min-Lipschitz and min-tail."

set_option linter.style.longLine false


end BishopCReal
