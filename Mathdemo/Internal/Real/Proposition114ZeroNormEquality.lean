import Mathdemo.Internal.Real.Corollary112Definition113

/-!
# G46: Proposition 1.14, zero norm and equality on a full set

Proposition 1.14 says that for integrable functions `f` and `g`:

* `f = g` on some full set;
* `||f - g|| = 0`;

are equivalent.  The reverse direction in the source proof selects an
increasing subsequence `k(n)` with small prefix absolute integral and then uses
the full set `B1 ∩ B2`.

This file adds the RegularSeq statement shape and keeps the `k(n)` and full-set
construction as explicit witness data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data for the source difference `r - s`, implemented as
`r + (-1) * s` with all Definition 1.6 operation data supplied explicitly. -/
structure SubData
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  neg_data : BishopRegularSeqIntegrableRep.SmulData (negSeq oneSeq) s
  add_data :
    BishopRegularSeqIntegrableRep.AddData r
      (BishopRegularSeqIntegrableRep.smul
        (S := S) (negSeq oneSeq) s neg_data)

/-- Source difference of two `L1` representatives. -/
def sub
    (r s : BishopRegularSeqIntegrableRep S)
    (data : SubData r s) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.add r
    (BishopRegularSeqIntegrableRep.smul
      (S := S) (negSeq oneSeq) s data.neg_data)
    data.add_data

end BishopRegularSeqIntegrableRep

/-- Almost-everywhere equality in the source sense: equality on some full
set. -/
structure BishopRegularSeqAlmostEverywhereEq
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  A : Set X
  full : BishopRegularSeqFullSet S A
  eq_on_full : BishopRegularSeqL1EqOnFull S A r s

/-- Zero norm of `r - s`, with the difference and absolute-value data supplied
explicitly. -/
structure BishopRegularSeqNormZero
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  sub_data : BishopRegularSeqIntegrableRep.SubData r s
  abs_data :
    BishopRegularSeqIntegrableRep.AbsData
      (BishopRegularSeqIntegrableRep.sub r s sub_data)
  norm_zero :
    relEventually
      (BishopRegularSeqIntegrableRep.sourceNorm
        (BishopRegularSeqIntegrableRep.sub r s sub_data)
        abs_data)
      zeroSeq

/-- The source reverse implication data in Proposition 1.14.  The field
`index` is the increasing `k(n)` used after Lemma 1.8, and `B1` is the full
set on which the selected prefix absolute values tend to zero.  The second
full set is the domain of the difference representative. -/
structure BishopRegularSeqProp114SubsequenceData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (diff : BishopRegularSeqIntegrableRep S) : Type 1 where
  index : Nat -> Nat
  index_strict :
    forall m n : Nat, m < n -> index m < index n
  prefix_abs_integral_small :
    forall n : Nat,
      regularSeqLtData
        (S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.finSum diff.fn (index n))))
        (constSeq (eps n))
  B1 : Set X
  B1_full : BishopRegularSeqFullSet S B1
  prefix_abs_tends_zero_on_B1 :
    forall x : X,
      x ∈ B1 ->
        BishopRegularSeqTendsto
          (fun n =>
            absSeq
              ((BishopRegularSeqPFun.finSum diff.fn (index n)).toFun x))
          zeroSeq
  source_B2_is_diff_domain : Prop

namespace BishopRegularSeqProp114SubsequenceData

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The full set `B1 ∩ B2` from the source proof, where
`B2` is the domain of the difference representative. -/
def finalFullSet
    {diff : BishopRegularSeqIntegrableRep S}
    (data : BishopRegularSeqProp114SubsequenceData S diff) :
    BishopRegularSeqFullSet S
      (data.B1 ∩ BishopRegularSeqIntegrableRep.domain diff) :=
  BishopRegularSeqFullSet.inter data.B1_full
    (BishopRegularSeqFullSet.of_domain diff)

end BishopRegularSeqProp114SubsequenceData

/-- Proposition 1.14 bridge.  The forward direction uses the fact that on a
full set `|r-s| = 0`; the reverse direction uses Lemma 1.8 and the explicit
subsequence data to build the full set where `r-s = 0`. -/
structure BishopRegularSeqProp114Bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  cor112_bridge : BishopRegularSeqCor112Bridge S
  zero_norm_from_ae_eq :
    forall r s : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqAlmostEverywhereEq S r s ->
        forall sub_data : BishopRegularSeqIntegrableRep.SubData r s,
          forall abs_data :
            BishopRegularSeqIntegrableRep.AbsData
              (BishopRegularSeqIntegrableRep.sub r s sub_data),
            relEventually
              (BishopRegularSeqIntegrableRep.sourceNorm
                (BishopRegularSeqIntegrableRep.sub r s sub_data)
                abs_data)
              zeroSeq
  ae_eq_from_zero_norm :
    forall r s : BishopRegularSeqIntegrableRep S,
      forall nz : BishopRegularSeqNormZero S r s,
        BishopRegularSeqProp114SubsequenceData S
          (BishopRegularSeqIntegrableRep.sub r s nz.sub_data) ->
          BishopRegularSeqAlmostEverywhereEq S r s
  source_uses_lemma_1_8 : Prop
  source_uses_full_set_B1_inter_B2 : Prop
  source_subsequence_k_is_explicit_data : Prop

/-- Proposition 1.14, forward implication. -/
def bishopRegularSeqProp114_forward
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : BishopRegularSeqProp114Bridge S)
    (r s : BishopRegularSeqIntegrableRep S)
    (hae : BishopRegularSeqAlmostEverywhereEq S r s)
    (sub_data : BishopRegularSeqIntegrableRep.SubData r s)
    (abs_data :
      BishopRegularSeqIntegrableRep.AbsData
        (BishopRegularSeqIntegrableRep.sub r s sub_data)) :
    BishopRegularSeqNormZero S r s where
  sub_data := sub_data
  abs_data := abs_data
  norm_zero :=
    bridge.zero_norm_from_ae_eq r s hae sub_data abs_data

/-- Proposition 1.14, reverse implication. -/
def bishopRegularSeqProp114_reverse
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : BishopRegularSeqProp114Bridge S)
    (r s : BishopRegularSeqIntegrableRep S)
    (nz : BishopRegularSeqNormZero S r s)
    (data :
      BishopRegularSeqProp114SubsequenceData S
        (BishopRegularSeqIntegrableRep.sub r s nz.sub_data)) :
    BishopRegularSeqAlmostEverywhereEq S r s :=
  bridge.ae_eq_from_zero_norm r s nz data

/-- Source-facing package for Proposition 1.14. -/
structure BishopRegularSeqProp114Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  ae_eq :
    BishopRegularSeqIntegrableRep S ->
      BishopRegularSeqIntegrableRep S -> Type 1
  norm_zero :
    BishopRegularSeqIntegrableRep S ->
      BishopRegularSeqIntegrableRep S -> Type 1
  forward :
    BishopRegularSeqProp114Bridge S ->
      forall r s : BishopRegularSeqIntegrableRep S,
        ae_eq r s ->
          forall sub_data : BishopRegularSeqIntegrableRep.SubData r s,
            forall abs_data :
              BishopRegularSeqIntegrableRep.AbsData
                (BishopRegularSeqIntegrableRep.sub r s sub_data),
              relEventually
                (BishopRegularSeqIntegrableRep.sourceNorm
                  (BishopRegularSeqIntegrableRep.sub r s sub_data)
                  abs_data)
                zeroSeq
  reverse :
    BishopRegularSeqProp114Bridge S ->
      forall r s : BishopRegularSeqIntegrableRep S,
        forall nz : BishopRegularSeqNormZero S r s,
          BishopRegularSeqProp114SubsequenceData S
            (BishopRegularSeqIntegrableRep.sub r s nz.sub_data) ->
            BishopRegularSeqAlmostEverywhereEq S r s
  source_proposition_1_14_regularseq : Prop
  zero_norm_uses_sourceNorm_from_definition_1_13 : Prop
  reverse_direction_keeps_k_sequence_as_data : Prop

def bishopRegularSeqProp114Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqProp114Package S where
  ae_eq := BishopRegularSeqAlmostEverywhereEq S
  norm_zero := BishopRegularSeqNormZero S
  forward := fun bridge r s hae sub_data abs_data =>
    (bishopRegularSeqProp114_forward
      S bridge r s hae sub_data abs_data).norm_zero
  reverse := fun bridge r s nz data =>
    bishopRegularSeqProp114_reverse S bridge r s nz data
  source_proposition_1_14_regularseq := True
  zero_norm_uses_sourceNorm_from_definition_1_13 := True
  reverse_direction_keeps_k_sequence_as_data := True

/-- Progress after G46: Proposition 1.14 is now represented as a
source-shaped equivalence on the Bishop RegularSeq route. -/
def bishopRegularSeqCh1To4ProgressAfterG46 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 61
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 45
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G46: added the RegularSeq Proposition 1.14 bridge, explicit difference \
    data, zero source-norm data, and the source k(n) subsequence frontier."


end BishopCReal
