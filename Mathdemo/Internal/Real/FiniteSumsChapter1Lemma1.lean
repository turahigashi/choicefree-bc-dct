import Mathdemo.Internal.Real.Chapter1Lemma15Closure

/-!
# G35: finite sums for chapter 1, Lemma 1.2 over Bishop RegularSeq reals

Lemma 1.2 uses a finite sum of the `g_i`, a finite initial sum of the
nonnegative `f_n`, and a tail series of the remaining `f_n`.  This file adds
those finite-sum objects and proves the source continuity step:

if the tail integral is below the integral of the finite comparison function,
Definition 1.1(2) supplies the required pointwise witness.
-/

namespace BishopCReal

open BishopC
open BishopCRat

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Finite sum of partial functions, indexed as `0..n`. -/
def finSum (F : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X
  | 0 => F 0
  | Nat.succ n => add (finSum F n) (F (Nat.succ n))

/-- Tail sequence `F_N, F_{N+1}, ...`. -/
def tail (F : Nat -> BishopRegularSeqPFun X) (N : Nat) :
    Nat -> BishopRegularSeqPFun X :=
  fun n => F (N + n)

/-- The finite comparison function in the proof of Lemma 1.2:
`sum_i g_i + sum_{n < N} f_n`, represented with the local `0..n` convention. -/
def lemma12FiniteSide (g f : Nat -> BishopRegularSeqPFun X)
    (k N : Nat) : BishopRegularSeqPFun X :=
  add (finSum g k) (finSum f N)

end BishopRegularSeqPFun

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Finite sums stay in `L`. -/
theorem def11_finSum_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (F : Nat -> BishopRegularSeqPFun X)
    (hF : forall n : Nat, F n ∈ S.core.L) :
    forall n : Nat, BishopRegularSeqPFun.finSum F n ∈ S.core.L
  | 0 => hF 0
  | Nat.succ n =>
      S.core.add_mem
        (def11_finSum_mem S F hF n)
        (hF (Nat.succ n))

/-- The integral of a finite sum is the finite sum of the integrals, up to
Bishop equality. -/
theorem def11_I_finSum
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (F : Nat -> BishopRegularSeqPFun X)
    (hF : forall n : Nat, F n ∈ S.core.L) :
    forall n : Nat,
      relEventually
        (S.core.I (BishopRegularSeqPFun.finSum F n))
        (regularSeqFinSum (fun i => S.core.I (F i)) n)
  | 0 => relEventually_refl (S.core.I (F 0))
  | Nat.succ n => by
      have hprev : BishopRegularSeqPFun.finSum F n ∈ S.core.L :=
        def11_finSum_mem S F hF n
      have hnext : F (Nat.succ n) ∈ S.core.L :=
        hF (Nat.succ n)
      have hadd :
          relEventually
            (S.core.I
              (BishopRegularSeqPFun.add
                (BishopRegularSeqPFun.finSum F n)
                (F (Nat.succ n))))
            (addSeq
              (S.core.I (BishopRegularSeqPFun.finSum F n))
              (S.core.I (F (Nat.succ n)))) :=
        S.core.I_add hprev hnext
      have hrec :
          relEventually
            (S.core.I (BishopRegularSeqPFun.finSum F n))
            (regularSeqFinSum (fun i => S.core.I (F i)) n) :=
        def11_I_finSum S F hF n
      have hsum :
          relEventually
            (addSeq
              (S.core.I (BishopRegularSeqPFun.finSum F n))
              (S.core.I (F (Nat.succ n))))
            (addSeq
              (regularSeqFinSum (fun i => S.core.I (F i)) n)
              (S.core.I (F (Nat.succ n)))) :=
        addSeq_respects_eventually
          (S.core.I (BishopRegularSeqPFun.finSum F n))
          (regularSeqFinSum (fun i => S.core.I (F i)) n)
          (S.core.I (F (Nat.succ n)))
          (S.core.I (F (Nat.succ n)))
          hrec
          (relEventually_refl (S.core.I (F (Nat.succ n))))
      exact
        relEventually_trans
          (S.core.I
            (BishopRegularSeqPFun.finSum F (Nat.succ n)))
          (addSeq
            (S.core.I (BishopRegularSeqPFun.finSum F n))
            (S.core.I (F (Nat.succ n))))
          (regularSeqFinSum (fun i => S.core.I (F i)) (Nat.succ n))
          hadd
          hsum

/-- The finite comparison side in Lemma 1.2 belongs to `L`. -/
theorem lemma12_finiteSide_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (g f : Nat -> BishopRegularSeqPFun X)
    (hg : forall n : Nat, g n ∈ S.core.L)
    (hf : forall n : Nat, f n ∈ S.core.L)
    (k N : Nat) :
    BishopRegularSeqPFun.lemma12FiniteSide g f k N ∈ S.core.L :=
  S.core.add_mem
    (def11_finSum_mem S g hg k)
    (def11_finSum_mem S f hf N)

/-- Data for the proof step in Lemma 1.2 where a large enough cut point `N`
has been selected and the tail integral is below the finite comparison side. -/
structure BishopRegularSeqLemma12CutData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (g f : Nat -> BishopRegularSeqPFun X)
    (k N : Nat) : Type where
  tail_integral :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I ((BishopRegularSeqPFun.tail f N) n))
  tail_lt_finite :
    regularSeqLtData tail_integral.sum
      (S.core.I (BishopRegularSeqPFun.lemma12FiniteSide g f k N))

/-- The Definition 1.1(2) continuity step used in Lemma 1.2.  This returns
pointwise witness data, so it is a definition rather than a proposition-valued
theorem. -/
def lemma12_continuity_step
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (g f : Nat -> BishopRegularSeqPFun X)
    (hg : forall n : Nat, g n ∈ S.core.L)
    (hf : forall n : Nat, f n ∈ S.core.L)
    (hnonneg : forall n : Nat, BishopRegularSeqPFun.PointwiseNonneg (f n))
    (k N : Nat)
    (cut : BishopRegularSeqLemma12CutData S g f k N) :
    BishopRegularSeqPointwiseSeriesBelow
      (BishopRegularSeqPFun.tail f N)
      (BishopRegularSeqPFun.lemma12FiniteSide g f k N) :=
  S.continuity
    (lemma12_finiteSide_mem S g f hg hf k N)
    (fun n => hf (N + n))
    (fun n => hnonneg (N + n))
    cut.tail_integral
    cut.tail_lt_finite

/-- Source-facing target for the remaining arithmetic in Lemma 1.2.  G35
proves the continuity step; the next step is to turn the below-witness into
the stated positive finite-plus-series value. -/
structure BishopRegularSeqLemma12RemainingOrderTarget
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (g f : Nat -> BishopRegularSeqPFun X) : Type where
  finite_count : Nat
  cut_index : Nat
  cut_data : BishopRegularSeqLemma12CutData S g f finite_count cut_index
  continuity_witness :
    BishopRegularSeqPointwiseSeriesBelow
      (BishopRegularSeqPFun.tail f cut_index)
      (BishopRegularSeqPFun.lemma12FiniteSide g f finite_count cut_index)
  source_positive_conclusion : Prop

/-- Progress after G35: the finite-sum machinery and Lemma 1.2 continuity
step are available in the new Bishop-real route. -/
def bishopRegularSeqCh1To4ProgressAfterG35 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 30
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 32
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G35: added finite sums for RegularSeq partial functions and closed the \
    Definition 1.1(2) continuity step used in Lemma 1.2."


end BishopCReal
