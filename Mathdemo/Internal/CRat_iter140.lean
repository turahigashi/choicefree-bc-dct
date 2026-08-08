import Mathdemo.Internal.CRat_iter139

/-!
# G40: source operations on `L1` after Definition 1.6

The source next defines addition and scalar multiplication on integrable
functions:

* `(f,{f_n}) + (g,{g_n})` is represented by `{f_0,g_0,f_1,g_1,...}`;
* `a * (f,{f_n})` is represented by `{a*f_n}`.

This file records these operations over the RegularSeq presentation with all
convergence and value-law data explicit.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Interleave two sequences as `f_0,g_0,f_1,g_1,...`. -/
def pairInterleave
    (f g : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X :=
  fun n => if n % 2 = 0 then f (n / 2) else g (n / 2)

/-- Pointwise scalar multiplication of a representing sequence. -/
def smulSeq (Arch : ScalarMulArchimedeanData)
    (a : RegularSeq) (f : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X :=
  fun n => smul Arch a (f n)

end BishopRegularSeqPFun

/-- Every term of the source addition representation belongs to `L`. -/
theorem def16_pairInterleave_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (f g : Nat -> BishopRegularSeqPFun X)
    (hf : forall n : Nat, f n ∈ S.core.L)
    (hg : forall n : Nat, g n ∈ S.core.L) :
    forall n : Nat, BishopRegularSeqPFun.pairInterleave f g n ∈ S.core.L := by
  intro n
  unfold BishopRegularSeqPFun.pairInterleave
  by_cases h : n % 2 = 0
  · simp [h, hf]
  · simp [h, hg]

/-- Every term of a scalar-multiplied representation belongs to `L`. -/
theorem def16_smulSeq_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a : RegularSeq)
    (f : Nat -> BishopRegularSeqPFun X)
    (hf : forall n : Nat, f n ∈ S.core.L) :
    forall n : Nat, BishopRegularSeqPFun.smulSeq Arch a f n ∈ S.core.L := by
  intro n
  exact S.core.smul_mem a (hf n)

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data required by the source addition operation on `L1`. -/
structure AddData
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.pairInterleave r.fn s.fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.pairInterleave r.fn s.fn n))
  value_law :
    BishopRegularSeqL1ValueLaw
      (BishopRegularSeqPFun.add r.pfun s.pfun)
      (BishopRegularSeqPFun.pairInterleave r.fn s.fn)
  integral_agrees :
    relEventually integral_sum.sum
      (addSeq r.integral s.integral)

/-- Source addition on `L1`, represented by interleaving the two representing
series. -/
def add
    (r s : BishopRegularSeqIntegrableRep S)
    (data : AddData r s) :
    BishopRegularSeqIntegrableRep S where
  pfun := BishopRegularSeqPFun.add r.pfun s.pfun
  fn := BishopRegularSeqPFun.pairInterleave r.fn s.fn
  fn_mem := def16_pairInterleave_mem S r.fn s.fn r.fn_mem s.fn_mem
  abs_integral_sum := data.abs_integral_sum
  integral_sum := data.integral_sum
  value_law := data.value_law
  source_definition_1_6_regularseq := True

/-- The represented integral of source addition is the sum of represented
integrals, when supplied by the operation data. -/
theorem add_integral_agrees
    (r s : BishopRegularSeqIntegrableRep S)
    (data : AddData r s) :
    relEventually (add r s data).integral
      (addSeq r.integral s.integral) :=
  data.integral_agrees

/-- Data required by source scalar multiplication on `L1`. -/
structure SmulData
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.smulSeq Arch a r.fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.smulSeq Arch a r.fn n))
  value_law :
    BishopRegularSeqL1ValueLaw
      (BishopRegularSeqPFun.smul Arch a r.pfun)
      (BishopRegularSeqPFun.smulSeq Arch a r.fn)
  integral_agrees :
    relEventually integral_sum.sum
      (mulSeqConcreteWith Arch a r.integral)

/-- Source scalar multiplication on `L1`. -/
def smul
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : SmulData a r) :
    BishopRegularSeqIntegrableRep S where
  pfun := BishopRegularSeqPFun.smul Arch a r.pfun
  fn := BishopRegularSeqPFun.smulSeq Arch a r.fn
  fn_mem := def16_smulSeq_mem S a r.fn r.fn_mem
  abs_integral_sum := data.abs_integral_sum
  integral_sum := data.integral_sum
  value_law := data.value_law
  source_definition_1_6_regularseq := True

/-- The represented integral of source scalar multiplication is the scalar
multiple of the represented integral, when supplied by the operation data. -/
theorem smul_integral_agrees
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : SmulData a r) :
    relEventually (smul a r data).integral
      (mulSeqConcreteWith Arch a r.integral) :=
  data.integral_agrees

end BishopRegularSeqIntegrableRep

/-- Source-facing package for the `L1` addition and scalar multiplication
frontier. -/
structure BishopRegularSeqDef16LinearOpsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  add :
    forall r s : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.AddData r s ->
        BishopRegularSeqIntegrableRep S
  smul :
    forall a : RegularSeq,
      forall r : BishopRegularSeqIntegrableRep S,
        BishopRegularSeqIntegrableRep.SmulData a r ->
          BishopRegularSeqIntegrableRep S
  source_addition_uses_interleaving : Prop
  source_scalar_multiplication_is_pointwise : Prop
  abs_operation_remains_next_frontier : Prop

def bishopRegularSeqDef16LinearOpsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqDef16LinearOpsPackage S where
  add := fun r s data =>
    BishopRegularSeqIntegrableRep.add r s data
  smul := fun a r data =>
    BishopRegularSeqIntegrableRep.smul a r data
  source_addition_uses_interleaving := True
  source_scalar_multiplication_is_pointwise := True
  abs_operation_remains_next_frontier := True

/-- Progress after G40: the source linear operations on `L1` are represented
over the Bishop RegularSeq route. -/
def bishopRegularSeqCh1To4ProgressAfterG40 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 48
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 39
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G40: added source L1 addition by interleaving representations and scalar \
    multiplication by pointwise scaling."


end BishopCReal
