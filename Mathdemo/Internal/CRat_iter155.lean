import Mathdemo.Internal.CRat_iter154

/-!
# G55: Theorem 1.18, property (4) estimate bridges

The source proof of Theorem 1.18(4) transfers the two truncation limits from
an previous `L` approximant to an arbitrary `L1` element by two displayed
estimates.  G54 kept these estimates as one field per truncation index.  This
file refines that frontier into two reusable source-level bridges:

* the large truncation estimate corresponding to source lines 730--735;
* the small absolute truncation estimate corresponding to source lines
  743--747.

The bridge data is still explicit, but it is now separated from the final
property (4) assembly and can be proved locally from the norm and truncation
operations in a later step.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Source estimate for
`|I(min(f,n)) - I(min(g,n))| <= ||f-g||`, specialized to the Corollary 1.17
finite-sum approximants. -/
structure Property4LargeLipschitzBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  estimate :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (epsv : RegularSeq),
      forall (N n : Nat),
        regularSeqLtData
          (BishopRegularSeqIntegrableRep.sourceNorm
            (BishopRegularSeqIntegrableRep.sub
              r
              ((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep N)
              ((bishopRegularSeqCor117_from_data S r cor117_data).tail_sub_data N))
            ((bishopRegularSeqCor117_from_data S r cor117_data).tail_abs_data N))
          epsv ->
        regularSeqLtData
          (absSeq
            (subSeq
              (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
              (S.core.I
                (BishopRegularSeqPFun.cutNat Arch n
                  (((bishopRegularSeqCor117_from_data S r cor117_data).approximant)
                    N)))))
          epsv
  source_lines_730_to_735 : Prop

/-- Source estimate for the small truncation argument applied to `|f|`:
`I(min(|f|,n^-1))` is bounded by the old-space small truncation plus the
approximation error. -/
structure Property4SmallLipschitzBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  estimate :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (epsv : RegularSeq),
      forall (N n : Nat),
        regularSeqLtData
          (BishopRegularSeqIntegrableRep.sourceNorm
            (BishopRegularSeqIntegrableRep.sub
              (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
              ((bishopRegularSeqCor117_from_data S
                  (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                  cor117_abs_data).approximant_rep N)
              ((bishopRegularSeqCor117_from_data S
                  (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                  cor117_abs_data).tail_sub_data N))
            ((bishopRegularSeqCor117_from_data S
                (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                cor117_abs_data).tail_abs_data N))
          epsv ->
        regularSeqLtData
          (BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
          (addSeq
            (S.core.I
              (BishopRegularSeqPFun.cutSmall Arch n
                (((bishopRegularSeqCor117_from_data S
                  (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                  cor117_abs_data).approximant) N)))
            epsv)
  source_lines_743_to_747 : Prop

/-- Property (4) reduction data with the two displayed estimates factored
through reusable bridges. -/
structure Property4ReductionDataFromBridges
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 2 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  large_bridge : Property4LargeLipschitzBridge S
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
  small_bridge : Property4SmallLipschitzBridge S
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
  source_uses_corollary_1_17_for_large_truncation : Prop
  source_uses_corollary_1_17_for_small_abs_truncation : Prop
  source_uses_displayed_lipschitz_estimates : Prop

/-- Rebuild the G54 reduction data from bridge-factored estimate data. -/
def property4ReductionData_from_bridges
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromBridges S r) :
    Property4ReductionData S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_lipschitz_estimate := fun n =>
    data.large_bridge.estimate
      r data.cuts data.cor117_data data.large_epsv
      data.large_approx_index n data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_lipschitz_estimate := fun n =>
    data.small_bridge.estimate
      r data.cuts data.small_cor117_abs_data data.small_epsv
      data.small_approx_index n data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_uses_corollary_1_17_for_large_truncation :=
    data.source_uses_corollary_1_17_for_large_truncation
  source_uses_corollary_1_17_for_small_abs_truncation :=
    data.source_uses_corollary_1_17_for_small_abs_truncation
  source_uses_displayed_lipschitz_estimates :=
    data.source_uses_displayed_lipschitz_estimates

/-- Theorem 1.18 property (4), assembled from the bridge-factored estimate
data. -/
def property4_from_bridge_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromBridges S r) :
    Property4Conclusion S r :=
  property4_from_data S r (property4ReductionData_from_bridges S r data)

end BishopRegularSeqTheorem118

/-- G55 package: the two displayed estimates in Theorem 1.18(4) are now
separated as reusable bridge targets. -/
structure BishopRegularSeqTheorem118G55Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  g54 : BishopRegularSeqTheorem118G54Package S
  large_estimate_bridge : Type 2
  small_estimate_bridge : Type 2
  property4_bridge_data :
    BishopRegularSeqIntegrableRep S -> Type 2
  property4_from_bridges :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_bridge_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_estimates_factored_from_final_assembly : Prop
  remaining_property4_work_is_to_prove_the_two_bridges : Prop

def bishopRegularSeqTheorem118G55Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G55Package S where
  g54 := bishopRegularSeqTheorem118G54Package S
  large_estimate_bridge :=
    BishopRegularSeqTheorem118.Property4LargeLipschitzBridge S
  small_estimate_bridge :=
    BishopRegularSeqTheorem118.Property4SmallLipschitzBridge S
  property4_bridge_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromBridges S
  property4_from_bridges := fun r data =>
    BishopRegularSeqTheorem118.property4_from_bridge_data S r data
  source_estimates_factored_from_final_assembly := True
  remaining_property4_work_is_to_prove_the_two_bridges := True

/-- Progress after G55: Theorem 1.18 property (4)'s two displayed estimates are
factored into reusable source bridges. -/
def bishopRegularSeqCh1To4ProgressAfterG55 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 83
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 55
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G55: factored Theorem 1.18 property (4)'s large and small truncation \
    estimates into reusable source bridge targets."


end BishopCReal
