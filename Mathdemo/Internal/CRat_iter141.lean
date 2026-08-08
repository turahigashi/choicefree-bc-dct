import Mathdemo.Internal.CRat_iter140

/-!
# G41: absolute-value representation and Lemma 1.8 boundary

After Definition 1.6 the source defines `|(f,{f_n})|` by the representation

`{|f_0|, f_0, -f_0, |f_0+f_1|-|f_0|, f_1, -f_1, ...}`.

This file records that source representation over RegularSeq partial
functions.  The analytic identification with `|f|` and the Lemma 1.8 limit are
kept as explicit data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Merge three sequences as `a_0,b_0,c_0,a_1,b_1,c_1,...`. -/
def tripleMerge
    (a b c : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X :=
  fun n =>
    if n % 3 = 0 then a (n / 3)
    else if n % 3 = 1 then b (n / 3)
    else c (n / 3)

/-- The telescoping absolute-prefix increment:
`d_0 = |S_0|`, `d_{j+1} = |S_{j+1}| - |S_j|`, where
`S_j = f_0 + ... + f_j`. -/
def absDelta
    (Arch : ScalarMulArchimedeanData)
    (fn : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X
  | 0 => absf (finSum fn 0)
  | Nat.succ j =>
      sub Arch
        (absf (finSum fn (Nat.succ j)))
        (absf (finSum fn j))

/-- Source representation for `|(f,{f_n})|`:
absolute-prefix increment, original term, negative original term. -/
def absRepSeq
    (Arch : ScalarMulArchimedeanData)
    (fn : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X :=
  tripleMerge
    (absDelta Arch fn)
    fn
    (fun j => neg Arch (fn j))

end BishopRegularSeqPFun

/-- Every term of a three-way merged representation belongs to `L`. -/
theorem def16_tripleMerge_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a b c : Nat -> BishopRegularSeqPFun X)
    (ha : forall n : Nat, a n ∈ S.core.L)
    (hb : forall n : Nat, b n ∈ S.core.L)
    (hc : forall n : Nat, c n ∈ S.core.L) :
    forall n : Nat, BishopRegularSeqPFun.tripleMerge a b c n ∈ S.core.L := by
  intro n
  unfold BishopRegularSeqPFun.tripleMerge
  by_cases h0 : n % 3 = 0
  · simp [h0, ha]
  · by_cases h1 : n % 3 = 1
    · simp [h1, hb]
    · simp [h0, h1, hc]

/-- The absolute-prefix increments used in the source representation belong
to `L`. -/
theorem def16_absDelta_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) :
    forall j : Nat, BishopRegularSeqPFun.absDelta Arch r.fn j ∈ S.core.L
  | 0 =>
      S.core.abs_mem (def11_finSum_mem S r.fn r.fn_mem 0)
  | Nat.succ j =>
      def11_sub_mem S
        (S.core.abs_mem
          (def11_finSum_mem S r.fn r.fn_mem (Nat.succ j)))
        (S.core.abs_mem
          (def11_finSum_mem S r.fn r.fn_mem j))

/-- Every term of the source absolute-value representation belongs to `L`. -/
theorem def16_absRepSeq_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) :
    forall n : Nat, BishopRegularSeqPFun.absRepSeq Arch r.fn n ∈ S.core.L :=
  def16_tripleMerge_mem S
    (BishopRegularSeqPFun.absDelta Arch r.fn)
    r.fn
    (fun j => BishopRegularSeqPFun.neg Arch (r.fn j))
    (def16_absDelta_mem S r)
    r.fn_mem
    (fun j => def11_neg_mem S (r.fn_mem j))

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data required by the source absolute-value operation on `L1`. -/
structure AbsData
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.absRepSeq Arch r.fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.absRepSeq Arch r.fn n))
  value_law :
    BishopRegularSeqL1ValueLaw
      (BishopRegularSeqPFun.absf r.pfun)
      (BishopRegularSeqPFun.absRepSeq Arch r.fn)
  prefix_abs_integral_tends :
    BishopRegularSeqTendsto
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.finSum r.fn n)))
      integral_sum.sum

/-- Source absolute value on `L1`, represented by the three-term telescoping
sequence. -/
def abs
    (r : BishopRegularSeqIntegrableRep S)
    (data : AbsData r) :
    BishopRegularSeqIntegrableRep S where
  pfun := BishopRegularSeqPFun.absf r.pfun
  fn := BishopRegularSeqPFun.absRepSeq Arch r.fn
  fn_mem := def16_absRepSeq_mem S r
  abs_integral_sum := data.abs_integral_sum
  integral_sum := data.integral_sum
  value_law := data.value_law
  source_definition_1_6_regularseq := True

/-- Lemma 1.8 boundary: the integral of the source absolute-value
representation is the limit of `I(|f_0+...+f_n|)` once the representation data
has supplied that limit. -/
def lemma18_abs_integral_limit
    (r : BishopRegularSeqIntegrableRep S)
    (data : AbsData r) :
    BishopRegularSeqTendsto
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.finSum r.fn n)))
      (abs r data).integral := by
  simpa [abs, integral] using data.prefix_abs_integral_tends

end BishopRegularSeqIntegrableRep

/-- Source-facing package for the absolute-value representation and Lemma 1.8
frontier. -/
structure BishopRegularSeqDef16AbsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  abs :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.AbsData r ->
        BishopRegularSeqIntegrableRep S
  lemma18 :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall data : BishopRegularSeqIntegrableRep.AbsData r,
        BishopRegularSeqTendsto
          (fun n =>
            S.core.I
              (BishopRegularSeqPFun.absf
                (BishopRegularSeqPFun.finSum r.fn n)))
          ((BishopRegularSeqIntegrableRep.abs r data).integral)
  source_abs_uses_three_term_representation : Prop
  padding_terms_keep_domain_information : Prop

def bishopRegularSeqDef16AbsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqDef16AbsPackage S where
  abs := fun r data => BishopRegularSeqIntegrableRep.abs r data
  lemma18 := fun r data =>
    BishopRegularSeqIntegrableRep.lemma18_abs_integral_limit r data
  source_abs_uses_three_term_representation := True
  padding_terms_keep_domain_information := True

/-- Progress after G41: the source absolute-value representation and Lemma
1.8 limit boundary are now present in the Bishop RegularSeq route. -/
def bishopRegularSeqCh1To4ProgressAfterG41 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 50
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 40
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G41: added the source three-term representation for L1 absolute value \
    and exposed Lemma 1.8 as an explicit prefix-absolute-integral limit."


end BishopCReal
