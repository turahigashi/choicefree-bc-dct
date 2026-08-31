import Mathdemo.Internal.Real.Theorem118Property4Estimate

/-!
# G56: Theorem 1.18(4) estimate bridges from order bounds

G55 separated the two displayed estimates in Theorem 1.18(4).  This file
refines the remaining target once more.  The source inequalities have the
shape

* a truncation error is bounded above by the norm error;
* the norm error is below the selected epsilon;
* therefore the truncation error is below the selected epsilon.

For the small truncation branch, the old-space small truncation is first added
to both sides.  The new package records exactly these two order-bound inputs
and the strict-upper-bound transfer needed to assemble the G55 bridges.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Generic order step used in the source estimates: a non-strict upper bound
followed by a strict upper bound yields the required strict upper bound. -/
structure RegularSeqStrictUpperTransfer : Type 1 where
  from_le_lt :
    forall {x y z : RegularSeq},
      RegularSeqLe x y -> regularSeqLtData y z -> regularSeqLtData x z
  source_order_step_for_epsilon_estimates : Prop

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Non-strict bound behind source lines 734--735:
the large truncation integral error is bounded by the approximation norm. -/
structure Property4LargeNormBoundBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  bound :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        RegularSeqLe
          (absSeq
            (subSeq
              (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
              (S.core.I
                (BishopRegularSeqPFun.cutNat Arch n
                  (((bishopRegularSeqCor117_from_data S r cor117_data).approximant)
                    N)))))
          (BishopRegularSeqIntegrableRep.sourceNorm
            (BishopRegularSeqIntegrableRep.sub
              r
              ((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep N)
              ((bishopRegularSeqCor117_from_data S r cor117_data).tail_sub_data N))
            ((bishopRegularSeqCor117_from_data S r cor117_data).tail_abs_data N))
  source_lines_734_to_735 : Prop

/-- Non-strict bound behind source lines 743--747:
the small truncation of `|f|` is bounded by the old-space small truncation
plus the norm error for `|f| - g`. -/
structure Property4SmallNormBoundBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  bound :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        RegularSeqLe
          (BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
          (addSeq
            (S.core.I
              (BishopRegularSeqPFun.cutSmall Arch n
                (((bishopRegularSeqCor117_from_data S
                  (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                  cor117_abs_data).approximant) N)))
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
                  cor117_abs_data).tail_abs_data N)))
  source_lines_743_to_747 : Prop

/-- Build the large Lipschitz estimate bridge from the non-strict norm bound
and the generic strict-upper-bound transfer. -/
def property4LargeLipschitzBridge_from_norm_bound
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (strict : RegularSeqStrictUpperTransfer)
    (bound_bridge : Property4LargeNormBoundBridge S) :
    Property4LargeLipschitzBridge S where
  estimate := by
    intro r cuts cor117_data epsv N n hnorm_lt
    exact
      strict.from_le_lt
        (bound_bridge.bound r cuts cor117_data N n)
        hnorm_lt
  source_lines_730_to_735 := True

/-- Build the small truncation estimate bridge from the non-strict bound,
left-additive strict-order transport, and strict-upper-bound transfer. -/
def property4SmallLipschitzBridge_from_norm_bound
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (strict : RegularSeqStrictUpperTransfer)
    (bound_bridge : Property4SmallNormBoundBridge S) :
    Property4SmallLipschitzBridge S where
  estimate := by
    intro r cuts cor117_abs_data epsv N n hnorm_lt
    let oldSmall : RegularSeq :=
      S.core.I
        (BishopRegularSeqPFun.cutSmall Arch n
          (((bishopRegularSeqCor117_from_data S
            (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
            cor117_abs_data).approximant) N))
    let normErr : RegularSeq :=
      BishopRegularSeqIntegrableRep.sourceNorm
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
            cor117_abs_data).tail_abs_data N)
    have hshift :
        regularSeqLtData
          (addSeq oldSmall normErr)
          (addSeq oldSmall epsv) :=
      regularSeqLtData_add_left oldSmall normErr epsv hnorm_lt
    exact
      strict.from_le_lt
        (bound_bridge.bound r cuts cor117_abs_data N n)
        hshift
  source_lines_743_to_747 := True

/-- Property (4) reduction data where the two G55 bridges are obtained from
non-strict norm bounds plus the generic strict-transfer step. -/
structure Property4ReductionDataFromNormBounds
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 2 where
  strict_transfer : RegularSeqStrictUpperTransfer
  large_norm_bound : Property4LargeNormBoundBridge S
  small_norm_bound : Property4SmallNormBoundBridge S
  base_data :
    Property4ReductionDataFromBridges S r
  base_large_bridge_is_generated :
    base_data.large_bridge =
      property4LargeLipschitzBridge_from_norm_bound
        S strict_transfer large_norm_bound
  base_small_bridge_is_generated :
    base_data.small_bridge =
      property4SmallLipschitzBridge_from_norm_bound
        S strict_transfer small_norm_bound

/-- Forget the norm-bound factory fields and recover the G55 bridge-factored
data. -/
def property4BridgeData_from_norm_bounds
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromNormBounds S r) :
    Property4ReductionDataFromBridges S r :=
  data.base_data

/-- Theorem 1.18 property (4), assembled through norm-bound bridges. -/
def property4_from_norm_bound_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromNormBounds S r) :
    Property4Conclusion S r :=
  property4_from_bridge_data S r
    (property4BridgeData_from_norm_bounds S r data)

end BishopRegularSeqTheorem118

/-- G56 package: the two G55 estimate bridges are obtained from non-strict
truncation/norm bounds plus a generic strict-transfer order step. -/
structure BishopRegularSeqTheorem118G56Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  g55 : BishopRegularSeqTheorem118G55Package S
  strict_transfer : Type 1
  large_norm_bound : Type 2
  small_norm_bound : Type 2
  property4_norm_bound_data :
    BishopRegularSeqIntegrableRep S -> Type 2
  property4_from_norm_bounds :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_norm_bound_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_estimates_reduced_to_norm_bounds_and_order_transfer : Prop
  remaining_work_is_to_prove_norm_bounds_and_order_convergence : Prop

def bishopRegularSeqTheorem118G56Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G56Package S where
  g55 := bishopRegularSeqTheorem118G55Package S
  strict_transfer := RegularSeqStrictUpperTransfer
  large_norm_bound :=
    BishopRegularSeqTheorem118.Property4LargeNormBoundBridge S
  small_norm_bound :=
    BishopRegularSeqTheorem118.Property4SmallNormBoundBridge S
  property4_norm_bound_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromNormBounds S
  property4_from_norm_bounds := fun r data =>
    BishopRegularSeqTheorem118.property4_from_norm_bound_data S r data
  source_estimates_reduced_to_norm_bounds_and_order_transfer := True
  remaining_work_is_to_prove_norm_bounds_and_order_convergence := True

/-- Progress after G56: Theorem 1.18(4)'s displayed estimates are reduced to
two non-strict norm bounds and a generic order-transfer bridge. -/
def bishopRegularSeqCh1To4ProgressAfterG56 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 84
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 56
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G56: reduced Theorem 1.18 property (4)'s estimate bridges to non-strict \
    truncation/norm bounds plus a strict upper-bound transfer step."


end BishopCReal
