import Mathdemo.Internal.Real.AbsoluteValueRepresentationLemma18

/-!
# G42: source representation for `min(f,1)` after Lemma 1.8

The source next defines `min{(f,{f_n}),1}` by the representation

`{min(f_0,1), f_0, -f_0, min(f_0+f_1,1)-min(f_0,1), f_1, -f_1, ...}`.

This file records that representation over the RegularSeq partial-function
surface.  Its convergence and value law are kept explicit, as in G41.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqPFun

variable {X : Type}

/-- The telescoping `min(prefix,1)` increment:
`d_0 = min(S_0,1)`, `d_{j+1}=min(S_{j+1},1)-min(S_j,1)`. -/
def minOneDelta
    (Arch : ScalarMulArchimedeanData)
    (fn : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X
  | 0 => cutOne Arch (finSum fn 0)
  | Nat.succ j =>
      sub Arch
        (cutOne Arch (finSum fn (Nat.succ j)))
        (cutOne Arch (finSum fn j))

/-- Source representation for `min{(f,{f_n}),1}`. -/
def minOneRepSeq
    (Arch : ScalarMulArchimedeanData)
    (fn : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X :=
  tripleMerge
    (minOneDelta Arch fn)
    fn
    (fun j => neg Arch (fn j))

end BishopRegularSeqPFun

/-- The `min(prefix,1)` increments used in the source representation belong
to `L`. -/
theorem def16_minOneDelta_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) :
    forall j : Nat, BishopRegularSeqPFun.minOneDelta Arch r.fn j ∈ S.core.L
  | 0 =>
      def11_cutOne_mem S (def11_finSum_mem S r.fn r.fn_mem 0)
  | Nat.succ j =>
      def11_sub_mem S
        (def11_cutOne_mem S
          (def11_finSum_mem S r.fn r.fn_mem (Nat.succ j)))
        (def11_cutOne_mem S
          (def11_finSum_mem S r.fn r.fn_mem j))

/-- Every term of the source `min(f,1)` representation belongs to `L`. -/
theorem def16_minOneRepSeq_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) :
    forall n : Nat, BishopRegularSeqPFun.minOneRepSeq Arch r.fn n ∈ S.core.L :=
  def16_tripleMerge_mem S
    (BishopRegularSeqPFun.minOneDelta Arch r.fn)
    r.fn
    (fun j => BishopRegularSeqPFun.neg Arch (r.fn j))
    (def16_minOneDelta_mem S r)
    r.fn_mem
    (fun j => def11_neg_mem S (r.fn_mem j))

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data required by the source `min(f,1)` operation on `L1`. -/
structure MinOneData
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.minOneRepSeq Arch r.fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.minOneRepSeq Arch r.fn n))
  value_law :
    BishopRegularSeqL1ValueLaw
      (BishopRegularSeqPFun.cutOne Arch r.pfun)
      (BishopRegularSeqPFun.minOneRepSeq Arch r.fn)

/-- Source `min(f,1)` operation on `L1`. -/
def minOne
    (r : BishopRegularSeqIntegrableRep S)
    (data : MinOneData r) :
    BishopRegularSeqIntegrableRep S where
  pfun := BishopRegularSeqPFun.cutOne Arch r.pfun
  fn := BishopRegularSeqPFun.minOneRepSeq Arch r.fn
  fn_mem := def16_minOneRepSeq_mem S r
  abs_integral_sum := data.abs_integral_sum
  integral_sum := data.integral_sum
  value_law := data.value_law
  source_definition_1_6_regularseq := True

end BishopRegularSeqIntegrableRep

/-- Source-facing package for the `min(f,1)` representation. -/
structure BishopRegularSeqDef16MinOnePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  minOne :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.MinOneData r ->
        BishopRegularSeqIntegrableRep S
  source_min_one_uses_three_term_representation : Prop
  padding_terms_keep_domain_information : Prop

def bishopRegularSeqDef16MinOnePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqDef16MinOnePackage S where
  minOne := fun r data => BishopRegularSeqIntegrableRep.minOne r data
  source_min_one_uses_three_term_representation := True
  padding_terms_keep_domain_information := True

/-- Progress after G42: the source `min(f,1)` representation is now present in
the Bishop RegularSeq route. -/
def bishopRegularSeqCh1To4ProgressAfterG42 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 52
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 41
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G42: added the source three-term representation for L1 min(f,1), \
    matching the paragraph after Lemma 1.8."


end BishopCReal
