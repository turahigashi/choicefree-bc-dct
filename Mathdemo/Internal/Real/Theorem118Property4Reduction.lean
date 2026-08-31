import Mathdemo.Internal.Real.Theorem118Property2Reduction

/-!
# G54: Theorem 1.18, property (4) reduction for `L1`

The final step of Theorem 1.18 proves the two truncation limits in
Definition 1.1(4) for `L1`.  The source uses Corollary 1.17 to approximate an
integrable function by an previous `L` function, then transfers the two old-space
truncation limits by the displayed estimates.

This file adds the general `min(f,a)` representation for `L1`, and records the
source reduction for the two limits.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Telescoping increment for the source representation of `min(f,a)`. -/
def cutConstDelta
    (Arch : ScalarMulArchimedeanData)
    (a : RegularSeq)
    (fn : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X
  | 0 => cutConst Arch (finSum fn 0) a
  | Nat.succ j =>
      sub Arch
        (cutConst Arch (finSum fn (Nat.succ j)) a)
        (cutConst Arch (finSum fn j) a)

/-- Source representation for `min((f,{f_n}),a)`. -/
def cutConstRepSeq
    (Arch : ScalarMulArchimedeanData)
    (a : RegularSeq)
    (fn : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X :=
  tripleMerge
    (cutConstDelta Arch a fn)
    fn
    (fun j => neg Arch (fn j))

end BishopRegularSeqPFun

/-- The telescoping `min(prefix,a)` increments belong to the previous space `L`. -/
theorem def16_cutConstDelta_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S) :
    forall j : Nat,
      BishopRegularSeqPFun.cutConstDelta Arch a r.fn j ∈ S.core.L
  | 0 =>
      S.cutConst_mem a (def11_finSum_mem S r.fn r.fn_mem 0)
  | Nat.succ j =>
      def11_sub_mem S
        (S.cutConst_mem a
          (def11_finSum_mem S r.fn r.fn_mem (Nat.succ j)))
        (S.cutConst_mem a
          (def11_finSum_mem S r.fn r.fn_mem j))

/-- Every term of the source `min(f,a)` representation belongs to `L`. -/
theorem def16_cutConstRepSeq_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S) :
    forall n : Nat,
      BishopRegularSeqPFun.cutConstRepSeq Arch a r.fn n ∈ S.core.L :=
  def16_tripleMerge_mem S
    (BishopRegularSeqPFun.cutConstDelta Arch a r.fn)
    r.fn
    (fun j => BishopRegularSeqPFun.neg Arch (r.fn j))
    (def16_cutConstDelta_mem S a r)
    r.fn_mem
    (fun j => def11_neg_mem S (r.fn_mem j))

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data required by the source `min(f,a)` operation on `L1`. -/
structure CutConstData
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.cutConstRepSeq Arch a r.fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.cutConstRepSeq Arch a r.fn n))
  value_law :
    BishopRegularSeqL1ValueLaw
      (BishopRegularSeqPFun.cutConst Arch r.pfun a)
      (BishopRegularSeqPFun.cutConstRepSeq Arch a r.fn)

/-- Source `min(f,a)` operation on `L1`. -/
def cutConst
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : CutConstData a r) :
    BishopRegularSeqIntegrableRep S where
  pfun := BishopRegularSeqPFun.cutConst Arch r.pfun a
  fn := BishopRegularSeqPFun.cutConstRepSeq Arch a r.fn
  fn_mem := def16_cutConstRepSeq_mem S a r
  abs_integral_sum := data.abs_integral_sum
  integral_sum := data.integral_sum
  value_law := data.value_law
  source_definition_1_6_regularseq := True

/-- The source truncation `min(f,n)` as an `L1` representation. -/
def cutNat
    (n : Nat)
    (r : BishopRegularSeqIntegrableRep S)
    (data : CutConstData (constSeq (n : Scalar)) r) :
    BishopRegularSeqIntegrableRep S :=
  cutConst (constSeq (n : Scalar)) r data

/-- The source truncation `min(|f|,eps_n)` as an `L1` representation. -/
def cutSmall
    (n : Nat)
    (r : BishopRegularSeqIntegrableRep S)
    (abs_data : AbsData r)
    (data :
      CutConstData (constSeq (eps n))
        (BishopRegularSeqIntegrableRep.abs r abs_data)) :
    BishopRegularSeqIntegrableRep S :=
  cutConst
    (constSeq (eps n))
    (BishopRegularSeqIntegrableRep.abs r abs_data)
    data

end BishopRegularSeqIntegrableRep

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- All `L1` truncation operation data needed for Definition 1.1(4). -/
structure Property4CutData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  cut_nat_data :
    forall n : Nat,
      BishopRegularSeqIntegrableRep.CutConstData
        (constSeq (n : Scalar)) r
  abs_data : BishopRegularSeqIntegrableRep.AbsData r
  cut_small_data :
    forall n : Nat,
      BishopRegularSeqIntegrableRep.CutConstData
        (constSeq (eps n))
        (BishopRegularSeqIntegrableRep.abs r abs_data)

/-- The `L1` representation of `min(f,n)`. -/
def cutNatRep
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (n : Nat) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.cutNat n r (cuts.cut_nat_data n)

/-- The `L1` representation of `min(|f|,eps_n)`. -/
def cutSmallRep
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (n : Nat) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.cutSmall
    n r cuts.abs_data (cuts.cut_small_data n)

/-- The old-space truncation limit for a Corollary 1.17 approximant. -/
def approximantCutNatTendsto
    (r : BishopRegularSeqIntegrableRep S)
    (N : Nat) :
    BishopRegularSeqTendsto
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.cutNat Arch n
            (BishopRegularSeqCor117.approxPFun r N)))
      (S.core.I (BishopRegularSeqCor117.approxPFun r N)) :=
  S.cutNat_tendsto (BishopRegularSeqCor117.approxPFun_mem r N)

/-- The old-space small absolute truncation limit for a Corollary 1.17
approximant. -/
def approximantCutSmallTendsto
    (r : BishopRegularSeqIntegrableRep S)
    (N : Nat) :
    BishopRegularSeqTendsto
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.cutSmall Arch n
            (BishopRegularSeqCor117.approxPFun r N)))
      zeroSeq :=
  S.cutSmall_tendsto (BishopRegularSeqCor117.approxPFun_mem r N)

/-- Reduction data for Theorem 1.18, property (4), following the source proof. -/
structure Property4ReductionData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
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
  large_lipschitz_estimate :
    forall n : Nat,
      regularSeqLtData
        (absSeq
          (subSeq
            (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
            (S.core.I
              (BishopRegularSeqPFun.cutNat Arch n
                (((bishopRegularSeqCor117_from_data S r cor117_data).approximant)
                  large_approx_index)))))
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
  small_lipschitz_estimate :
    forall n : Nat,
      regularSeqLtData
        (BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
        (addSeq
          (S.core.I
            (BishopRegularSeqPFun.cutSmall Arch n
              (((bishopRegularSeqCor117_from_data S
                (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                small_cor117_abs_data).approximant) small_approx_index)))
          small_epsv)
  small_trunc_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
      zeroSeq
  source_uses_corollary_1_17_for_large_truncation : Prop
  source_uses_corollary_1_17_for_small_abs_truncation : Prop
  source_uses_displayed_lipschitz_estimates : Prop

/-- Theorem 1.18, Definition 1.1(4) conclusion for `L1`. -/
structure Property4Conclusion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  cut_nat_rep : Nat -> BishopRegularSeqIntegrableRep S
  cut_small_rep : Nat -> BishopRegularSeqIntegrableRep S
  cut_nat_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cut_nat_rep n))
      (BishopRegularSeqIntegrableRep.integral r)
  cut_small_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cut_small_rep n))
      zeroSeq
  source_definition_1_1_property_4_for_L1 : Prop

/-- Assemble Theorem 1.18, property (4), from the source reduction data. -/
def property4_from_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionData S r) :
    Property4Conclusion S r where
  cut_nat_rep := cutNatRep r data.cuts
  cut_small_rep := cutSmallRep r data.cuts
  cut_nat_tendsto := data.large_trunc_tendsto
  cut_small_tendsto := data.small_trunc_tendsto
  source_definition_1_1_property_4_for_L1 := True

end BishopRegularSeqTheorem118

/-- Theorem 1.18 status after G54: all four Definition 1.1 properties are now
represented for `L1`; the remaining work is to refine the displayed estimate
data into smaller algebraic lemmas. -/
structure BishopRegularSeqTheorem118G54Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  g53 : BishopRegularSeqTheorem118G53Package S
  property4_data :
    BishopRegularSeqIntegrableRep S -> Type 1
  property4 :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_theorem_1_18_all_four_properties_represented : Prop
  displayed_estimates_remain_refinement_targets : Prop

def bishopRegularSeqTheorem118G54Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G54Package S where
  g53 := bishopRegularSeqTheorem118G53Package S
  property4_data := BishopRegularSeqTheorem118.Property4ReductionData S
  property4 := fun r data =>
    BishopRegularSeqTheorem118.property4_from_data S r data
  source_theorem_1_18_all_four_properties_represented := True
  displayed_estimates_remain_refinement_targets := True

/-- Progress after G54: Theorem 1.18 property (4) is represented over `L1`
using Corollary 1.17 approximation and truncation-transfer data. -/
def bishopRegularSeqCh1To4ProgressAfterG54 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 82
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 54
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G54: added the L1 min(f,a) representation and connected Theorem 1.18 \
    property (4) to Corollary 1.17 approximants and truncation-transfer data."


end BishopCReal
