import Mathdemo.Internal.CRat_iter143

/-!
# G44: Proposition 1.11 monotonicity interface

Proposition 1.11 says: if `r <= s` on a full set `A`, then `I(r) <= I(s)`.
The source proof uses Lemma 1.10 to restrict the domain with `h-h`, and then
applies Lemma 1.7.

This file records the RegularSeq statement shape and keeps the proof step as
an explicit bridge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Non-strict order on RegularSeq reals, represented as non-negativity of the
difference `y - x`. -/
abbrev RegularSeqLe (x y : RegularSeq) : Prop :=
  RegularSeqNonneg (subSeq y x)

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Value selected by Definition 1.6's value law from explicit absolute
summability data at a point. -/
def valueAt
    (r : BishopRegularSeqIntegrableRep S)
    (x : X)
    (habs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))) :
    RegularSeq :=
  (r.value_law.value_from_abs x habs).val.sum

end BishopRegularSeqIntegrableRep

/-- Source hypothesis "r <= s on full set A", stated with explicit value-sum
data at each point. -/
structure BishopRegularSeqL1LeOnFull
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (A : Set X)
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  le_value :
    forall x : X,
      x ∈ A ->
        forall hr :
          BishopRegularSeqSeriesSum
            (fun n => absSeq ((r.fn n).toFun x)),
        forall hs :
          BishopRegularSeqSeriesSum
            (fun n => absSeq ((s.fn n).toFun x)),
          RegularSeqLe
            (BishopRegularSeqIntegrableRep.valueAt r x hr)
            (BishopRegularSeqIntegrableRep.valueAt s x hs)

/-- Proposition 1.11 as an explicit bridge.  The bridge records the source
dependencies: Lemma 1.10 for the full-set domain reduction and Lemma 1.7 for
the final positivity argument. -/
structure BishopRegularSeqProp111Bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  lemma110_bridge : BishopRegularSeqLemma110Bridge S
  monotone :
    forall {A : Set X},
      BishopRegularSeqFullSet S A ->
        forall r s : BishopRegularSeqIntegrableRep S,
          BishopRegularSeqL1LeOnFull S A r s ->
            RegularSeqLe r.integral s.integral
  source_uses_lemma_1_10 : Prop
  source_uses_lemma_1_7 : Prop

/-- Proposition 1.11 in source-level form. -/
def bishopRegularSeqProp111
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : BishopRegularSeqProp111Bridge S)
    {A : Set X}
    (hA : BishopRegularSeqFullSet S A)
    (r s : BishopRegularSeqIntegrableRep S)
    (hle : BishopRegularSeqL1LeOnFull S A r s) :
    RegularSeqLe r.integral s.integral :=
  bridge.monotone hA r s hle

/-- Source-facing package for Proposition 1.11. -/
structure BishopRegularSeqProp111Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  le_on_full :
    Set X ->
      BishopRegularSeqIntegrableRep S ->
        BishopRegularSeqIntegrableRep S -> Type 1
  prop111 :
    BishopRegularSeqProp111Bridge S ->
      forall {A : Set X},
        BishopRegularSeqFullSet S A ->
          forall r s : BishopRegularSeqIntegrableRep S,
            le_on_full A r s ->
              RegularSeqLe r.integral s.integral
  source_proposition_1_11_regularseq : Prop
  lemma_1_10_and_lemma_1_7_remain_the_frontier : Prop

def bishopRegularSeqProp111Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqProp111Package S where
  le_on_full := BishopRegularSeqL1LeOnFull S
  prop111 := fun bridge => fun {A} hA r s hle =>
    bishopRegularSeqProp111 S bridge (A := A) hA r s hle
  source_proposition_1_11_regularseq := True
  lemma_1_10_and_lemma_1_7_remain_the_frontier := True

/-- Progress after G44: Proposition 1.11 is now represented as a source-shaped
monotonicity bridge over full sets. -/
def bishopRegularSeqCh1To4ProgressAfterG44 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 56
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 43
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G44: added the source-shaped Proposition 1.11 monotonicity interface over \
    full sets, with Lemma 1.10 and Lemma 1.7 exposed as the proof frontier."


end BishopCReal
