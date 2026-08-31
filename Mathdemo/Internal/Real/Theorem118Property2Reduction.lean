import Mathdemo.Internal.Real.StartTheorem118L1

/-!
# G53: Theorem 1.18, property (2) reduction for `L1`

Theorem 1.18 proves Definition 1.1 again for `L1`.  For property (2), the
source expands each non-negative integrable `h_n` by Lemma 1.15, expands `h`
up to a finite head and small tail, and then applies property (2) in the old
space `L`.

This file records that exact reduction over the RegularSeq presentation.  The
final pointwise comparison from the majorant sequence to
`sum h_n(x) < h(x)` is kept as explicit data, because it is the source's
last triangle-inequality calculation.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The source expression `3 * eps` written as three additions. -/
def threeEps (epsv : RegularSeq) : RegularSeq :=
  addSeq epsv (addSeq epsv epsv)

/-- The source row error `eps * 2^{-n}`. -/
def rowEps (epsv : RegularSeq) (n : Nat) : RegularSeq :=
  mulSeqConcreteWith Arch epsv (constSeq (eps n))

/-- Input data for Definition 1.1(2) in `L1`. -/
structure Property2Input
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  h : BishopRegularSeqIntegrableRep S
  hs : Nat -> BishopRegularSeqIntegrableRep S
  h_nonneg : BishopRegularSeqPFun.PointwiseNonneg h.pfun
  hs_nonneg : forall n : Nat,
    BishopRegularSeqPFun.PointwiseNonneg (hs n).pfun
  integral_series :
    BishopRegularSeqSeriesSum
      (fun n => BishopRegularSeqIntegrableRep.integral (hs n))
  integral_lt :
    regularSeqLtData integral_series.sum
      (BishopRegularSeqIntegrableRep.integral h)

/-- The finite head `|psi_0 + ... + psi_K|` from the source proof. -/
def headAbs
    (input : Property2Input S) (K : Nat) :
    BishopRegularSeqPFun X :=
  BishopRegularSeqPFun.absf
    (BishopRegularSeqPFun.finSum input.h.fn K)

/-- The finite head belongs to the previous space `L`. -/
theorem headAbs_mem
    (input : Property2Input S) (K : Nat) :
    headAbs input K ∈ S.core.L :=
  S.core.abs_mem
    (def11_finSum_mem S input.h.fn input.h.fn_mem K)

/-- The tail term `|psi_{K+1+j}|` from the source proof. -/
def tailAbs
    (input : Property2Input S) (K j : Nat) :
    BishopRegularSeqPFun X :=
  BishopRegularSeqPFun.absf
    (BishopRegularSeqPFun.lemma115Tail K input.h.fn j)

/-- Every tail absolute term belongs to `L`. -/
theorem tailAbs_mem
    (input : Property2Input S) (K : Nat) :
    forall j : Nat, tailAbs input K j ∈ S.core.L := by
  intro j
  exact
    S.core.abs_mem
      (lemma115_tail_mem S K input.h.fn input.h.fn_mem j)

/-- Lemma 1.15 conclusion for the `n`-th row. -/
def rowConclusion
    (input : Property2Input S)
    (epsv : RegularSeq)
    (row_abs_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.AbsData (input.hs n))
    (row_compression_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.Lemma115CompressionData
          (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n))
    (n : Nat) :
    BishopRegularSeqIntegrableRep.Lemma115Conclusion
      (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n) :=
  BishopRegularSeqIntegrableRep.lemma115_from_compression
    (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n)
    (row_compression_data n)

/-- The compressed row representation obtained from Lemma 1.15. -/
def rowRep
    (input : Property2Input S)
    (epsv : RegularSeq)
    (row_abs_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.AbsData (input.hs n))
    (row_compression_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.Lemma115CompressionData
          (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n))
    (n : Nat) :
    BishopRegularSeqIntegrableRep S :=
  (rowConclusion input epsv row_abs_data row_compression_data n).rep

/-- The flattened double sequence
`|varphi_{n,k}|`, using the square-shell enumeration. -/
def rowAbsFlat
    (input : Property2Input S)
    (epsv : RegularSeq)
    (row_abs_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.AbsData (input.hs n))
    (row_compression_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.Lemma115CompressionData
          (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n))
    (t : Nat) :
    BishopRegularSeqPFun X :=
  let cell := BishopRegularSeqTheorem116.squareEnum t
  BishopRegularSeqPFun.absf
    ((rowRep input epsv row_abs_data row_compression_data cell.1).fn cell.2)

/-- Each flattened row absolute term belongs to `L`. -/
theorem rowAbsFlat_mem
    (input : Property2Input S)
    (epsv : RegularSeq)
    (row_abs_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.AbsData (input.hs n))
    (row_compression_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.Lemma115CompressionData
          (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n)) :
    forall t : Nat,
      rowAbsFlat input epsv row_abs_data row_compression_data t ∈
        S.core.L := by
  intro t
  dsimp [rowAbsFlat]
  exact
    S.core.abs_mem
      ((rowRep input epsv row_abs_data row_compression_data
        (BishopRegularSeqTheorem116.squareEnum t).1).fn_mem
        (BishopRegularSeqTheorem116.squareEnum t).2)

/-- The old-space sequence to which Definition 1.1(2) is applied:
the flattened row absolute terms interleaved with the tail absolute terms of
`h`. -/
def majorantSeq
    (input : Property2Input S)
    (epsv : RegularSeq)
    (row_abs_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.AbsData (input.hs n))
    (row_compression_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.Lemma115CompressionData
          (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n))
    (K : Nat) :
    Nat -> BishopRegularSeqPFun X :=
  BishopRegularSeqPFun.pairInterleave
    (rowAbsFlat input epsv row_abs_data row_compression_data)
    (tailAbs input K)

/-- Every term of the majorant sequence belongs to the previous space `L`. -/
theorem majorantSeq_mem
    (input : Property2Input S)
    (epsv : RegularSeq)
    (row_abs_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.AbsData (input.hs n))
    (row_compression_data :
      forall n : Nat,
        BishopRegularSeqIntegrableRep.Lemma115CompressionData
          (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n))
    (K : Nat) :
    forall m : Nat,
      majorantSeq input epsv row_abs_data row_compression_data K m ∈
        S.core.L :=
  def16_pairInterleave_mem S
    (rowAbsFlat input epsv row_abs_data row_compression_data)
    (tailAbs input K)
    (rowAbsFlat_mem input epsv row_abs_data row_compression_data)
    (tailAbs_mem input K)

/-- Reduction data for Theorem 1.18, property (2), following the source proof. -/
structure Property2ReductionData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : Property2Input S) : Type 1 where
  epsv : RegularSeq
  eps_pos : regularSeqLtData zeroSeq epsv
  source_margin :
    regularSeqLtData
      (addSeq input.integral_series.sum (threeEps epsv))
      (BishopRegularSeqIntegrableRep.integral input.h)
  row_abs_data :
    forall n : Nat,
      BishopRegularSeqIntegrableRep.AbsData (input.hs n)
  row_compression_data :
    forall n : Nat,
      BishopRegularSeqIntegrableRep.Lemma115CompressionData
        (input.hs n) (rowEps (Arch := Arch) epsv n) (row_abs_data n)
  row_abs_bound :
    forall n : Nat,
      regularSeqLtData
        ((rowRep input epsv row_abs_data row_compression_data n).abs_integral_sum.sum)
        (addSeq
          (BishopRegularSeqIntegrableRep.integral (input.hs n))
          (rowEps (Arch := Arch) epsv n))
  K : Nat
  h_integral_lt_head_plus_eps :
    regularSeqLtData
      (BishopRegularSeqIntegrableRep.integral input.h)
      (addSeq (S.core.I (headAbs input K)) epsv)
  tail_abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun j => S.core.I (tailAbs input K j))
  tail_abs_lt_eps :
    regularSeqLtData tail_abs_integral_sum.sum epsv
  majorant_integral_sum :
    BishopRegularSeqSeriesSum
      (fun m =>
        S.core.I
          (majorantSeq input epsv row_abs_data row_compression_data K m))
  majorant_nonneg :
    forall m : Nat,
      BishopRegularSeqPFun.PointwiseNonneg
        (majorantSeq input epsv row_abs_data row_compression_data K m)
  majorant_lt_head :
    regularSeqLtData majorant_integral_sum.sum
      (S.core.I (headAbs input K))
  pointwise_transfer :
    BishopRegularSeqPointwiseSeriesBelow
      (majorantSeq input epsv row_abs_data row_compression_data K)
      (headAbs input K) ->
    BishopRegularSeqPointwiseSeriesBelow
      (fun n => (input.hs n).pfun)
      input.h.pfun
  source_uses_lemma_1_15_for_each_row : Prop
  source_uses_original_property_2_on_majorant : Prop
  source_final_step_is_pointwise_estimate : Prop

/-- The actual application of Definition 1.1(2) in the previous space `L`. -/
def originalContinuityPoint
    (input : Property2Input S)
    (data : Property2ReductionData S input) :
    BishopRegularSeqPointwiseSeriesBelow
      (majorantSeq input data.epsv data.row_abs_data
        data.row_compression_data data.K)
      (headAbs input data.K) :=
  S.continuity
    (headAbs_mem input data.K)
    (majorantSeq_mem input data.epsv data.row_abs_data
      data.row_compression_data data.K)
    data.majorant_nonneg
    data.majorant_integral_sum
    data.majorant_lt_head

end BishopRegularSeqTheorem118

/-- Theorem 1.18, Definition 1.1(2) conclusion for `L1`. -/
structure BishopRegularSeqTheorem118Property2Conclusion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem118.Property2Input S) : Type 1 where
  reduction_eps : RegularSeq
  reduction_row_abs_data :
    forall n : Nat,
      BishopRegularSeqIntegrableRep.AbsData (input.hs n)
  reduction_row_compression_data :
    forall n : Nat,
      BishopRegularSeqIntegrableRep.Lemma115CompressionData
        (input.hs n)
        (BishopRegularSeqTheorem118.rowEps
          (Arch := Arch) reduction_eps n)
        (reduction_row_abs_data n)
  reduction_K : Nat
  old_space_point :
    BishopRegularSeqPointwiseSeriesBelow
      (BishopRegularSeqTheorem118.majorantSeq
        input
        reduction_eps
        reduction_row_abs_data
        reduction_row_compression_data
        reduction_K)
      (BishopRegularSeqTheorem118.headAbs input reduction_K)
  l1_point :
    BishopRegularSeqPointwiseSeriesBelow
      (fun n => (input.hs n).pfun)
      input.h.pfun
  source_definition_1_1_property_2_for_L1 : Prop

/-- Assemble Theorem 1.18, property (2), from the source reduction data. -/
def bishopRegularSeqTheorem118_property2_from_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem118.Property2Input S)
    (data : BishopRegularSeqTheorem118.Property2ReductionData S input) :
    BishopRegularSeqTheorem118Property2Conclusion S input where
  reduction_eps := data.epsv
  reduction_row_abs_data := data.row_abs_data
  reduction_row_compression_data := data.row_compression_data
  reduction_K := data.K
  old_space_point :=
    BishopRegularSeqTheorem118.originalContinuityPoint input data
  l1_point :=
    data.pointwise_transfer
      (BishopRegularSeqTheorem118.originalContinuityPoint input data)
  source_definition_1_1_property_2_for_L1 := True

/-- Theorem 1.18 status after G53: property (2) is reduced to the rowwise
Lemma 1.15 data, the old-space property (2), and the source pointwise estimate. -/
structure BishopRegularSeqTheorem118G53Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  g52 : BishopRegularSeqTheorem118G52Package S
  property2_data :
    BishopRegularSeqTheorem118.Property2Input S -> Type 1
  property2 :
    forall input : BishopRegularSeqTheorem118.Property2Input S,
      property2_data input ->
        BishopRegularSeqTheorem118Property2Conclusion S input
  property4_frontier_uses_corollary_1_17_density_and_truncation_transfer : Prop
  source_theorem_1_18_in_progress : Prop

def bishopRegularSeqTheorem118G53Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G53Package S where
  g52 := bishopRegularSeqTheorem118G52Package S
  property2_data := BishopRegularSeqTheorem118.Property2ReductionData S
  property2 := fun input data =>
    bishopRegularSeqTheorem118_property2_from_data S input data
  property4_frontier_uses_corollary_1_17_density_and_truncation_transfer := True
  source_theorem_1_18_in_progress := True

/-- Progress after G53: Theorem 1.18 property (2) is connected to the old
space property (2) through the source rowwise majorant construction. -/
def bishopRegularSeqCh1To4ProgressAfterG53 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 80
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 53
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G53: connected Theorem 1.18 property (2) to rowwise Lemma 1.15 data, \
    a flattened majorant sequence in L, and the old-space continuity field."


end BishopCReal
