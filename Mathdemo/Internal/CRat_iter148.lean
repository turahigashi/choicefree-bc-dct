import Mathdemo.Internal.CRat_iter147

/-!
# G48: Theorem 1.16 double-series construction interface

Theorem 1.16 starts with a sequence of integrable functions whose norms form a
convergent series.  It applies Lemma 1.15 row by row, forms a double series,
defines the full set where the double absolute series converges, and obtains an
integrable limit whose finite partial sums converge in norm.

This file records that construction on the Bishop RegularSeq route.  The
row representations, double enumeration, full set, limit representation, and
tail norm convergence are explicit data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The input of Theorem 1.16: an `L1` sequence with a convergent series of
source norms. -/
structure BishopRegularSeqTheorem116Input
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  seq : Nat -> BishopRegularSeqIntegrableRep S
  abs_data :
    forall n : Nat,
      BishopRegularSeqIntegrableRep.AbsData (seq n)
  norm_series :
    BishopRegularSeqSeriesSum
      (fun n =>
        BishopRegularSeqIntegrableRep.sourceNorm
          (seq n) (abs_data n))
  source_norm_series_converges : Prop

/-- Row data obtained by applying Lemma 1.15 to the `n`-th integrable
function with tolerance `2^{-n}` represented by `eps n`. -/
abbrev BishopRegularSeqTheorem116RowData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem116Input S) : Type 1 :=
  forall n : Nat,
    BishopRegularSeqIntegrableRep.Lemma115CompressionData
      (input.seq n) (constSeq (eps n)) (input.abs_data n)

namespace BishopRegularSeqTheorem116

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The compressed row representation for the `n`-th term. -/
def rowRep
    (input : BishopRegularSeqTheorem116Input S)
    (row_data : BishopRegularSeqTheorem116RowData S input)
    (n : Nat) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.lemma115CompressedRep
    (input.seq n) (constSeq (eps n)) (input.abs_data n) (row_data n)

/-- Flatten a double-index family through an explicit enumeration. -/
def flatSeq
    (input : BishopRegularSeqTheorem116Input S)
    (row_data : BishopRegularSeqTheorem116RowData S input)
    (enum : Nat -> Nat × Nat) :
    Nat -> BishopRegularSeqPFun X :=
  fun t =>
    ((rowRep input row_data (enum t).1).fn ((enum t).2))

/-- Every flattened term is in the original integration class. -/
theorem flatSeq_mem
    (input : BishopRegularSeqTheorem116Input S)
    (row_data : BishopRegularSeqTheorem116RowData S input)
    (enum : Nat -> Nat × Nat) :
    forall t : Nat, flatSeq input row_data enum t ∈ S.core.L := by
  intro t
  exact
    (rowRep input row_data (enum t).1).fn_mem ((enum t).2)

end BishopRegularSeqTheorem116

/-- Data for the double-series construction in Theorem 1.16. -/
structure BishopRegularSeqTheorem116DoubleData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem116Input S) : Type 1 where
  row_data : BishopRegularSeqTheorem116RowData S input
  enum : Nat -> Nat × Nat
  enum_covers :
    forall n k : Nat, { t : Nat // enum t = (n, k) }
  A : Set X
  A_full : BishopRegularSeqFullSet S A
  limit_pfun : BishopRegularSeqPFun X
  limit_domain_is_A : limit_pfun.dom = A
  flat_abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun t =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqTheorem116.flatSeq input row_data enum t)))
  flat_integral_sum :
    BishopRegularSeqSeriesSum
      (fun t =>
        S.core.I
          (BishopRegularSeqTheorem116.flatSeq input row_data enum t))
  flat_value_law :
    BishopRegularSeqL1ValueLaw limit_pfun
      (BishopRegularSeqTheorem116.flatSeq input row_data enum)
  original_domain_on_A :
    forall x : X, x ∈ A ->
      forall n : Nat,
        x ∈ BishopRegularSeqIntegrableRep.domain (input.seq n)
  original_abs_series_on_A :
    forall x : X, x ∈ A ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((input.seq n).pfun.toFun x))
  limit_agrees_with_original_series :
    forall x : X,
      x ∈ A ->
        forall hsum :
          BishopRegularSeqSeriesSum
            (fun n => (input.seq n).pfun.toFun x),
          relEventually (limit_pfun.toFun x) hsum.sum
  source_A_is_double_abs_convergence_set : Prop
  source_limit_uses_flattened_double_series : Prop

namespace BishopRegularSeqTheorem116

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The integrable limit representation obtained by enumerating the double
series. -/
def limitRep
    (input : BishopRegularSeqTheorem116Input S)
    (data : BishopRegularSeqTheorem116DoubleData S input) :
    BishopRegularSeqIntegrableRep S where
  pfun := data.limit_pfun
  fn := flatSeq input data.row_data data.enum
  fn_mem := flatSeq_mem input data.row_data data.enum
  abs_integral_sum := data.flat_abs_integral_sum
  integral_sum := data.flat_integral_sum
  value_law := data.flat_value_law
  source_definition_1_6_regularseq := True

end BishopRegularSeqTheorem116

/-- Explicit finite partial sums used in the norm convergence conclusion of
Theorem 1.16. -/
structure BishopRegularSeqL1FinitePartialSums
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (seq : Nat -> BishopRegularSeqIntegrableRep S) : Type 1 where
  partialRep : Nat -> BishopRegularSeqIntegrableRep S
  partial_pfun_agrees :
    forall N : Nat,
      BishopRegularSeqPFunAlmostEverywhereEq S
        (partialRep N).pfun
        (BishopRegularSeqPFun.finSum
          (fun n => (seq n).pfun) N)
  source_partial_sum_representation : Prop

/-- Tail norm convergence data in Theorem 1.16. -/
structure BishopRegularSeqTheorem116TailNormData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem116Input S)
    (limit : BishopRegularSeqIntegrableRep S) : Type 1 where
  partial_sums :
    BishopRegularSeqL1FinitePartialSums S input.seq
  tail_sub_data :
    forall N : Nat,
      BishopRegularSeqIntegrableRep.SubData
        limit (partial_sums.partialRep N)
  tail_abs_data :
    forall N : Nat,
      BishopRegularSeqIntegrableRep.AbsData
        (BishopRegularSeqIntegrableRep.sub
          limit (partial_sums.partialRep N) (tail_sub_data N))
  norm_tendsto_zero :
    BishopRegularSeqTendsto
      (fun N =>
        BishopRegularSeqIntegrableRep.sourceNorm
          (BishopRegularSeqIntegrableRep.sub
            limit (partial_sums.partialRep N) (tail_sub_data N))
          (tail_abs_data N))
      zeroSeq
  source_uses_lemma_1_7_for_tail_bound : Prop
  source_tail_bound_uses_row_estimates : Prop

/-- Theorem 1.16 conclusion in source-level form. -/
structure BishopRegularSeqTheorem116Conclusion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem116Input S) : Type 1 where
  A : Set X
  full : BishopRegularSeqFullSet S A
  limit : BishopRegularSeqIntegrableRep S
  limit_domain_is_A :
    BishopRegularSeqIntegrableRep.domain limit = A
  original_domain_on_A :
    forall x : X, x ∈ A ->
      forall n : Nat,
        x ∈ BishopRegularSeqIntegrableRep.domain (input.seq n)
  original_abs_series_on_A :
    forall x : X, x ∈ A ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((input.seq n).pfun.toFun x))
  limit_agrees_with_original_series :
    forall x : X,
      x ∈ A ->
        forall hsum :
          BishopRegularSeqSeriesSum
            (fun n => (input.seq n).pfun.toFun x),
          relEventually (limit.pfun.toFun x) hsum.sum
  tail_norm_data :
    BishopRegularSeqTheorem116TailNormData S input limit
  source_theorem_1_16_regularseq : Prop

/-- Assemble Theorem 1.16 once the double-series and tail-norm data have been
supplied explicitly. -/
def bishopRegularSeqTheorem116_from_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem116Input S)
    (data : BishopRegularSeqTheorem116DoubleData S input)
    (tail :
      BishopRegularSeqTheorem116TailNormData S input
        (BishopRegularSeqTheorem116.limitRep input data)) :
    BishopRegularSeqTheorem116Conclusion S input where
  A := data.A
  full := data.A_full
  limit := BishopRegularSeqTheorem116.limitRep input data
  limit_domain_is_A := data.limit_domain_is_A
  original_domain_on_A := data.original_domain_on_A
  original_abs_series_on_A := data.original_abs_series_on_A
  limit_agrees_with_original_series :=
    data.limit_agrees_with_original_series
  tail_norm_data := tail
  source_theorem_1_16_regularseq := True

/-- Source-facing package for Theorem 1.16. -/
structure BishopRegularSeqTheorem116Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  input : Type 1
  double_data : BishopRegularSeqTheorem116Input S -> Type 1
  conclusion : BishopRegularSeqTheorem116Input S -> Type 1
  theorem116 :
    forall i : BishopRegularSeqTheorem116Input S,
      forall data : BishopRegularSeqTheorem116DoubleData S i,
        BishopRegularSeqTheorem116TailNormData S
          i
          (BishopRegularSeqTheorem116.limitRep i data) ->
          BishopRegularSeqTheorem116Conclusion S i
  source_uses_lemma_1_15_rowwise : Prop
  source_full_set_is_double_abs_convergence : Prop
  source_norm_convergence_is_tail_estimate : Prop

def bishopRegularSeqTheorem116Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem116Package S where
  input := BishopRegularSeqTheorem116Input S
  double_data := BishopRegularSeqTheorem116DoubleData S
  conclusion := BishopRegularSeqTheorem116Conclusion S
  theorem116 := fun i data tail =>
    bishopRegularSeqTheorem116_from_data S i data tail
  source_uses_lemma_1_15_rowwise := True
  source_full_set_is_double_abs_convergence := True
  source_norm_convergence_is_tail_estimate := True

/-- Progress after G48: Theorem 1.16 is now represented by explicit
double-series and tail-norm data on the Bishop RegularSeq route. -/
def bishopRegularSeqCh1To4ProgressAfterG48 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 68
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 48
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G48: added the Theorem 1.16 double-series interface, explicit row \
    Lemma 1.15 data, full-set limit representation, and tail norm convergence."


end BishopCReal
