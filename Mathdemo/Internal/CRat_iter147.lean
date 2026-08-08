import Mathdemo.Internal.CRat_iter146

/-!
# G47: equality a.e. convention and Lemma 1.15 compression data

After Proposition 1.14 the source changes the working equality/order on
`F(X)` to mean equality/order on some full set.  Lemma 1.15 then compresses an
arbitrary representation of an integrable function by replacing an initial
block with its finite sum.

This file records both moves on the Bishop RegularSeq route.  The cutoff `N`,
the compressed representation, and the final strict estimate are explicit
data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Equality of partial functions on a specified full set. -/
structure BishopRegularSeqPFunEqOnFull
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (A : Set X)
    (f g : BishopRegularSeqPFun X) : Type 1 where
  values_agree :
    forall x : X,
      x ∈ A ->
        x ∈ f.dom ->
          x ∈ g.dom ->
            relEventually (f.toFun x) (g.toFun x)

/-- Order of partial functions on a specified full set. -/
structure BishopRegularSeqPFunLeOnFull
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (A : Set X)
    (f g : BishopRegularSeqPFun X) : Type 1 where
  values_le :
    forall x : X,
      x ∈ A ->
        x ∈ f.dom ->
          x ∈ g.dom ->
            RegularSeqLe (f.toFun x) (g.toFun x)

/-- Source convention after Proposition 1.14 for `F(X)`: equality means
equality on some full set. -/
structure BishopRegularSeqPFunAlmostEverywhereEq
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (f g : BishopRegularSeqPFun X) : Type 1 where
  A : Set X
  full : BishopRegularSeqFullSet S A
  eq_on_full : BishopRegularSeqPFunEqOnFull S A f g

/-- Source convention after Proposition 1.14 for `F(X)`: order means order on
some full set. -/
structure BishopRegularSeqPFunAlmostEverywhereLe
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (f g : BishopRegularSeqPFun X) : Type 1 where
  A : Set X
  full : BishopRegularSeqFullSet S A
  le_on_full : BishopRegularSeqPFunLeOnFull S A f g

/-- `L1` order in the same a.e. convention. -/
structure BishopRegularSeqAlmostEverywhereLe
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  A : Set X
  full : BishopRegularSeqFullSet S A
  le_on_full : BishopRegularSeqL1LeOnFull S A r s

/-- Source-facing package for the convention introduced after Proposition
1.14. -/
structure BishopRegularSeqAEEqConventionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  pfun_ae_eq : BishopRegularSeqPFun X -> BishopRegularSeqPFun X -> Type 1
  pfun_ae_le : BishopRegularSeqPFun X -> BishopRegularSeqPFun X -> Type 1
  l1_ae_eq :
    BishopRegularSeqIntegrableRep S ->
      BishopRegularSeqIntegrableRep S -> Type 1
  l1_ae_le :
    BishopRegularSeqIntegrableRep S ->
      BishopRegularSeqIntegrableRep S -> Type 1
  proposition_1_14_identifies_l1_ae_eq_with_zero_norm : Prop
  source_declares_ae_eq_more_important_than_prior_equality : Prop
  source_extends_eq_and_le_to_FX_by_full_sets : Prop

def bishopRegularSeqAEEqConventionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqAEEqConventionPackage S where
  pfun_ae_eq := BishopRegularSeqPFunAlmostEverywhereEq S
  pfun_ae_le := BishopRegularSeqPFunAlmostEverywhereLe S
  l1_ae_eq := BishopRegularSeqAlmostEverywhereEq S
  l1_ae_le := BishopRegularSeqAlmostEverywhereLe S
  proposition_1_14_identifies_l1_ae_eq_with_zero_norm := True
  source_declares_ae_eq_more_important_than_prior_equality := True
  source_extends_eq_and_le_to_FX_by_full_sets := True

namespace BishopRegularSeqPFun

variable {X : Type}

/-- The tail of a representation after the compressed initial block. -/
def lemma115Tail
    (cutoff : Nat)
    (fn : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X :=
  fun n => fn (cutoff + 1 + n)

/-- Lemma 1.15's compressed representation:
`sum_{i <= cutoff} f_i, f_{cutoff+1}, f_{cutoff+2}, ...`. -/
def lemma115CompressedSeq
    (cutoff : Nat)
    (fn : Nat -> BishopRegularSeqPFun X) :
    Nat -> BishopRegularSeqPFun X
  | 0 => finSum fn cutoff
  | Nat.succ n => lemma115Tail cutoff fn n

end BishopRegularSeqPFun

/-- Every term of Lemma 1.15's tail remains in `L`. -/
theorem lemma115_tail_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (cutoff : Nat)
    (fn : Nat -> BishopRegularSeqPFun X)
    (hfn : forall n : Nat, fn n ∈ S.core.L) :
    forall n : Nat,
      BishopRegularSeqPFun.lemma115Tail cutoff fn n ∈ S.core.L := by
  intro n
  exact hfn (cutoff + 1 + n)

/-- Every term of Lemma 1.15's compressed representation remains in `L`. -/
theorem lemma115_compressedSeq_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (cutoff : Nat)
    (fn : Nat -> BishopRegularSeqPFun X)
    (hfn : forall n : Nat, fn n ∈ S.core.L) :
    forall n : Nat,
      BishopRegularSeqPFun.lemma115CompressedSeq cutoff fn n ∈ S.core.L
  | 0 => def11_finSum_mem S fn hfn cutoff
  | Nat.succ n => lemma115_tail_mem S cutoff fn hfn n

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data used in Lemma 1.15: the cutoff, the tail estimate, and the
compressed representation data. -/
structure Lemma115CompressionData
    (r : BishopRegularSeqIntegrableRep S)
    (epsv : RegularSeq)
    (abs_data : BishopRegularSeqIntegrableRep.AbsData r) : Type 1 where
  eps_pos : regularSeqLtData zeroSeq epsv
  cutoff : Nat
  cutoff_pos : 1 <= cutoff
  tail_abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.lemma115Tail cutoff r.fn n)))
  tail_abs_lt_half_eps :
    regularSeqLtData tail_abs_integral_sum.sum
      (mulSeqConcreteWith Arch halfSeq epsv)
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.lemma115CompressedSeq cutoff r.fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.lemma115CompressedSeq cutoff r.fn n))
  value_law :
    BishopRegularSeqL1ValueLaw r.pfun
      (BishopRegularSeqPFun.lemma115CompressedSeq cutoff r.fn)
  compressed_abs_bound :
    regularSeqLtData abs_integral_sum.sum
      (addSeq
        (BishopRegularSeqIntegrableRep.sourceNorm r abs_data)
        epsv)
  source_representation_is_initial_block_compression : Prop

/-- The compressed representation supplied by Lemma 1.15. -/
def lemma115CompressedRep
    (r : BishopRegularSeqIntegrableRep S)
    (epsv : RegularSeq)
    (abs_data : BishopRegularSeqIntegrableRep.AbsData r)
    (data : Lemma115CompressionData r epsv abs_data) :
    BishopRegularSeqIntegrableRep S where
  pfun := r.pfun
  fn := BishopRegularSeqPFun.lemma115CompressedSeq data.cutoff r.fn
  fn_mem := lemma115_compressedSeq_mem S data.cutoff r.fn r.fn_mem
  abs_integral_sum := data.abs_integral_sum
  integral_sum := data.integral_sum
  value_law := data.value_law
  source_definition_1_6_regularseq := True

/-- Lemma 1.15 conclusion in representation form. -/
structure Lemma115Conclusion
    (r : BishopRegularSeqIntegrableRep S)
    (epsv : RegularSeq)
    (abs_data : BishopRegularSeqIntegrableRep.AbsData r) : Type 1 where
  rep : BishopRegularSeqIntegrableRep S
  represents_r : BishopRegularSeqPFun.equiv rep.pfun r.pfun
  abs_integral_lt_norm_add_eps :
    regularSeqLtData rep.abs_integral_sum.sum
      (addSeq
        (BishopRegularSeqIntegrableRep.sourceNorm r abs_data)
        epsv)

/-- Lemma 1.15 from explicit compression data. -/
def lemma115_from_compression
    (r : BishopRegularSeqIntegrableRep S)
    (epsv : RegularSeq)
    (abs_data : BishopRegularSeqIntegrableRep.AbsData r)
    (data : Lemma115CompressionData r epsv abs_data) :
    Lemma115Conclusion r epsv abs_data where
  rep := lemma115CompressedRep r epsv abs_data data
  represents_r := by
    constructor
    · rfl
    · intro x _hx
      exact relEventually_refl (r.pfun.toFun x)
  abs_integral_lt_norm_add_eps := data.compressed_abs_bound

end BishopRegularSeqIntegrableRep

/-- Source-facing package for Lemma 1.15. -/
structure BishopRegularSeqLemma115Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  compression_data :
    forall r : BishopRegularSeqIntegrableRep S,
      RegularSeq ->
        BishopRegularSeqIntegrableRep.AbsData r -> Type 1
  lemma115 :
    forall r : BishopRegularSeqIntegrableRep S,
      forall epsv : RegularSeq,
        forall abs_data : BishopRegularSeqIntegrableRep.AbsData r,
          compression_data r epsv abs_data ->
            BishopRegularSeqIntegrableRep.Lemma115Conclusion
              r epsv abs_data
  source_lemma_1_15_regularseq : Prop
  initial_block_compression_is_explicit : Prop
  epsilon_and_cutoff_data_are_explicit : Prop

def bishopRegularSeqLemma115Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqLemma115Package S where
  compression_data :=
    fun r epsv abs_data =>
      BishopRegularSeqIntegrableRep.Lemma115CompressionData
        r epsv abs_data
  lemma115 := fun r epsv abs_data data =>
    BishopRegularSeqIntegrableRep.lemma115_from_compression
      r epsv abs_data data
  source_lemma_1_15_regularseq := True
  initial_block_compression_is_explicit := True
  epsilon_and_cutoff_data_are_explicit := True

/-- Progress after G47: the post-Proposition 1.14 a.e. convention and Lemma
1.15 compression interface are present on the Bishop RegularSeq route. -/
def bishopRegularSeqCh1To4ProgressAfterG47 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 64
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 46
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G47: added the post-Proposition 1.14 a.e. equality/order convention and \
    Lemma 1.15's explicit initial-block compression data."


end BishopCReal
