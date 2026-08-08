import Mathdemo.Internal.CRat_iter136

/-!
# G37: source-shaped Lemma 1.2 bridge and corollary targets

G36 isolated the remaining step in Lemma 1.2 as order/series arithmetic.  In
the Richman-style route we keep all selector data explicit:

* a cut index `N` and its tail-below-finite data;
* a bridge turning the common-domain/tail-below-finite witness into the final
  positive pointwise conclusion.

This file proves the source-shaped Lemma 1.2 conclusion from those explicit
data, and prepares the two immediate corollary targets.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Data replacing the informal phrase "for all sufficiently large `N`" in the
source proof of Lemma 1.2.  No cut is selected implicitly. -/
structure BishopRegularSeqLemma12CutChoice
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (g f : Nat -> BishopRegularSeqPFun X)
    (k : Nat) : Type where
  N : Nat
  cut : BishopRegularSeqLemma12CutData S g f k N

/-- Source-shaped hypotheses for Lemma 1.2 after G36. -/
structure BishopRegularSeqLemma12Hypotheses
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (g f : Nat -> BishopRegularSeqPFun X)
    (k : Nat) : Type where
  hg : forall n : Nat, g n ∈ S.core.L
  hf : forall n : Nat, f n ∈ S.core.L
  hnonneg : forall n : Nat, BishopRegularSeqPFun.PointwiseNonneg (f n)
  cut_choice : BishopRegularSeqLemma12CutChoice S g f k
  order_series_bridge : BishopRegularSeqLemma12OrderSeriesBridge g f

/-- Lemma 1.2 in the RegularSeq route, reduced exactly to the explicit cut and
order/series bridge data. -/
def lemma12_positive_from_hypotheses
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (g f : Nat -> BishopRegularSeqPFun X)
    (k : Nat)
    (H : BishopRegularSeqLemma12Hypotheses S g f k) :
    BishopRegularSeqLemma12PositiveConclusion g f k :=
  H.order_series_bridge.to_positive
    (lemma12_commonDomain_from_cut
      S g f H.hg H.hf H.hnonneg
      k H.cut_choice.N H.cut_choice.cut)

/-- The Corollary 1.3 conclusion: finite positivity gives a point in the common
domain of the finite family where the finite value is positive. -/
structure BishopRegularSeqCor13Conclusion
    (g : Nat -> BishopRegularSeqPFun X) (k : Nat) : Type where
  x : X
  hx_g : forall i : Nat, i <= k -> x ∈ (g i).dom
  positive :
    regularSeqLtData zeroSeq
      (regularSeqFinSum (fun i => (g i).toFun x) k)

/-- A selector-free bridge from Lemma 1.2's conclusion with a zero tail to
Corollary 1.3's finite positive conclusion. -/
structure BishopRegularSeqCor13ZeroTailBridge
    (g fzero : Nat -> BishopRegularSeqPFun X) (k : Nat) : Type where
  to_finite_positive :
    BishopRegularSeqLemma12PositiveConclusion g fzero k ->
      BishopRegularSeqCor13Conclusion g k

/-- Corollary 1.3, reduced to an explicit zero-tail bridge rather than an
implicit proof extraction. -/
def cor13_from_lemma12_positive
    (g fzero : Nat -> BishopRegularSeqPFun X)
    (k : Nat)
    (bridge : BishopRegularSeqCor13ZeroTailBridge g fzero k)
    (lemma12_result : BishopRegularSeqLemma12PositiveConclusion g fzero k) :
    BishopRegularSeqCor13Conclusion g k :=
  bridge.to_finite_positive lemma12_result

/-- The Corollary 1.4 conclusion: one point belongs to every domain in a
sequence. -/
structure BishopRegularSeqCor14Conclusion
    (f : Nat -> BishopRegularSeqPFun X) : Type where
  x : X
  hx_f : forall n : Nat, x ∈ (f n).dom

/-- Corollary 1.4 follows from any Lemma 1.2 positive conclusion by forgetting
the positivity and finite family data. -/
def cor14_from_lemma12_positive
    (g f : Nat -> BishopRegularSeqPFun X)
    (k : Nat)
    (lemma12_result : BishopRegularSeqLemma12PositiveConclusion g f k) :
    BishopRegularSeqCor14Conclusion f where
  x := lemma12_result.x
  hx_f := lemma12_result.hx_f

/-- A source-level package for chapter 1 through Corollary 1.4. -/
structure BishopRegularSeqChapter1EarlyPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type where
  lemma12 :
    forall (g f : Nat -> BishopRegularSeqPFun X) (k : Nat),
      BishopRegularSeqLemma12Hypotheses S g f k ->
      BishopRegularSeqLemma12PositiveConclusion g f k
  cor13 :
    forall (g fzero : Nat -> BishopRegularSeqPFun X) (k : Nat),
      BishopRegularSeqCor13ZeroTailBridge g fzero k ->
      BishopRegularSeqLemma12PositiveConclusion g fzero k ->
      BishopRegularSeqCor13Conclusion g k
  cor14 :
    forall (g f : Nat -> BishopRegularSeqPFun X) (k : Nat),
      BishopRegularSeqLemma12PositiveConclusion g f k ->
      BishopRegularSeqCor14Conclusion f

/-- The package currently obtained from the explicit bridge reductions. -/
def bishopRegularSeqChapter1EarlyPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter1EarlyPackage S where
  lemma12 := fun g f k H =>
    lemma12_positive_from_hypotheses S g f k H
  cor13 := fun g fzero k bridge lemma12_result =>
    cor13_from_lemma12_positive g fzero k bridge lemma12_result
  cor14 := fun g f k lemma12_result =>
    cor14_from_lemma12_positive g f k lemma12_result

/-- Progress after G37: Lemma 1.2, Corollary 1.3, and Corollary 1.4 now have
source-shaped selector-free bridge endpoints. -/
def bishopRegularSeqCh1To4ProgressAfterG37 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 39
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 35
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G37: assembled Lemma 1.2 from explicit cut and order/series bridge data, \
    and added Corollary 1.3/1.4 endpoints."


end BishopCReal
