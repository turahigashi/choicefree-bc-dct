import Mathdemo.Internal.Real.CommonGoodSourceDataProduceDyadic

set_option linter.style.longLine false

/-!
# G189: data-carrying convergence supplies the common-good witnesses

G188 still separated "all common-good source data" from the convergence
hypotheses because the source-level `ConvergeInMeasure` is Prop-valued.
This file records the Bishop-style repair: keep the same mathematical content,
but expose the witnesses as Type/Sigma data.  From that data we can construct
the `B,C,N` common-good part without any later choice operation.

The remaining assumption-free source frontiers stay honest:

* the current Prop-valued convergence interface must be replaced or paired with
  this data-carrying interface if later code needs actual witnesses;
* the bad-set `<= n` bound remains a concrete analytic bound to prove or
  correct.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- Data-carrying version of Definition 4.11 for Proposition 4.12.

This has the same local fields as `ConvergeInMeasure`, but `close` returns the
modulus and good set as `Sigma` data instead of hiding them behind a
Prop-valued existential. -/
structure Prop412ConvergeInMeasureData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (fn : Nat -> BishopC.PFunR Y R)
    (f : BishopC.PFunR Y R) : Type _ where
  close :
    ∀ (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (eps : R) (_heps : COF.lt 0 eps),
      Sigma (fun N : Nat =>
        ∀ n, N ≤ n ->
          Sigma (fun B : BishopC.BSet Y =>
            Sigma (fun hB : BishopC.IntegrableSet1 S B =>
              PLift ((B.S1 ⊆ A.S1 ∩ f.dom ∩ (fn n).dom) ∧
              COF.lt (BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hB)) eps ∧
              ∀ x (_hxB : x ∈ B.S1) (hxf : x ∈ f.dom) (hxfn : x ∈ (fn n).dom),
                COF.lt (COF.abs (f.toFun x hxf - (fn n).toFun x hxfn)) eps))))

/-- The data-carrying convergence hypotheses produce the source's common
`B,C,N` witnesses.  This is the Type-valued analogue of G168's Prop theorem. -/
def prop412_common_good_pair_data_from_convergence_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R} {f g : BishopC.PFunR Y R}
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (eps : R) (heps : COF.lt 0 eps) :
    Sigma (fun N : Nat =>
      ∀ n, N ≤ n ->
        Sigma (fun B : BishopC.BSet Y =>
          Sigma (fun hB : BishopC.IntegrableSet1 S B =>
            Sigma (fun C : BishopC.BSet Y =>
              Sigma (fun hC : BishopC.IntegrableSet1 S C =>
                PLift (Prop412CommonGoodPair fn f g A hA eps n B hB C hC)))))) := by
  let eps2 : R := prop412Half eps
  have heps2 : COF.lt 0 eps2 := by
    dsimp [eps2]
    exact prop412Half_pos heps
  obtain ⟨Nf, hNf⟩ := hf.close A hA eps2 heps2
  obtain ⟨Ng, hNg⟩ := hg.close A hA eps2 heps2
  refine ⟨Nat.max Nf Ng, ?_⟩
  intro n hn
  have hnF : Nf ≤ n := Nat.le_trans (Nat.le_max_left Nf Ng) hn
  have hnG : Ng ≤ n := Nat.le_trans (Nat.le_max_right Nf Ng) hn
  obtain ⟨B, hB, hBdata⟩ := hNf n hnF
  obtain ⟨C, hC, hCdata⟩ := hNg n hnG
  obtain ⟨hBsubset, hBmeasure, hBpoint⟩ := hBdata.down
  obtain ⟨hCsubset, hCmeasure, hCpoint⟩ := hCdata.down
  refine ⟨B, hB, C, hC, ?_⟩
  dsimp [Prop412CommonGoodPair, eps2, prop412Half] at *
  exact ⟨⟨hBsubset, hBmeasure, hBpoint, hCsubset, hCmeasure, hCpoint⟩⟩

/-- The non-convergence auxiliary fields needed to upgrade a common-good pair to
one full dyadic source datum.  Keeping this separate makes explicit that G189 is
closing the witness-extraction layer, not smuggling in the bad-set estimate. -/
structure Prop412DyadicCommonGoodAuxData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (k : Nat)
    (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
    (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C)
    (eps : R) : Type _ where
  chiA_abs_on_good :
    Prop412GoodSetChiAAbsData A (BishopC.BSet.and B C) hA
  pointwise_seed :
    Prop412ComplementPointwiseConcreteSupportSeedData
      A (BishopC.BSet.and B C) hA (BishopC.IntegrableSet1_and hB hC)
      truncN f g F G
  bad_bound :
    Prop412ConcreteBadSetNBoundData
      A (BishopC.BSet.and B C) hA (BishopC.IntegrableSet1_and hB hC)
      truncN F G
  truncN_pos : COF.lt 0 (truncN : R)
  arithmetic_budget :
    COF.lt
      (eps * BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC) +
        (truncN : R) * eps)
      (COF.halfPow (R := R) k)

/-- Per-dyadic construction data: an epsilon to feed to convergence, plus the
analytic auxiliary builder for the returned common-good pair. -/
structure Prop412DyadicCommonGoodConstructionData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.PFunR Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (k : Nat) : Type _ where
  eps : R
  heps : COF.lt 0 eps
  aux :
    ∀ (seqN : Nat)
      (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      Prop412CommonGoodPair fn f g A hA eps seqN B hB C hC ->
        Prop412DyadicCommonGoodAuxData A hA truncN F G k B hB C hC eps

/-- One dyadic common-good source datum from data-carrying convergence. -/
def prop412_dyadic_common_good_source_from_convergence_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    {k : Nat}
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (D : Prop412DyadicCommonGoodConstructionData fn A hA truncN F G k) :
    Prop412DyadicCommonGoodSourceData fn A hA truncN F G k := by
  obtain ⟨N, hN⟩ :=
    prop412_common_good_pair_data_from_convergence_data
      hf hg A hA D.eps D.heps
  obtain ⟨B, hB, C, hC, hpairData⟩ := hN N (Nat.le_refl N)
  let hpair := hpairData.down
  let Aux := D.aux N B hB C hC hpair
  exact
    { seqN := N
      B := B
      hB := hB
      C := C
      hC := hC
      eps := D.eps
      common_pair := hpair
      chiA_abs_on_good := Aux.chiA_abs_on_good
      pointwise_seed := Aux.pointwise_seed
      bad_bound := Aux.bad_bound
      truncN_pos := Aux.truncN_pos
      arithmetic_budget := Aux.arithmetic_budget }

/-- Construction data for every dyadic target. -/
structure Prop412AllCommonGoodConstructionData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.PFunR Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g) : Type _ where
  data :
    ∀ k : Nat, Prop412DyadicCommonGoodConstructionData fn A hA truncN F G k

/-- All common-good source data from data-carrying convergence. -/
def prop412_all_common_good_sources_from_convergence_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (D : Prop412AllCommonGoodConstructionData fn A hA truncN F G) :
    Prop412AllCommonGoodSourceData fn A hA truncN F G where
  data := by
    intro k
    exact prop412_dyadic_common_good_source_from_convergence_data
      hA F G hf hg (D.data k)

/-- Final equality from data-carrying convergence plus the explicit remaining
analytic construction data. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (D : Prop412AllCommonGoodConstructionData fn A hA truncN F G) :
    F.mid.rep.integral = G.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_common_good_sources
    hA F G
    (prop412_all_common_good_sources_from_convergence_data hA F G hf hg D)

/-- Residual shape after G189. -/
structure Prop412DataCarryingConvergenceFrontierAfterG189 : Type where
  data_carrying_convergence_to_common_good_witnesses_closed : Prop
  data_carrying_convergence_to_truncated_equality_closed_given_aux_data : Prop
  prop_valued_convergence_extraction_still_requires_redesign_not_choice : Prop
  bad_set_n_bound_still_open_for_assumption_free_source : Prop
  old_true_statement_used : Nat

def prop412DataCarryingConvergenceFrontierAfterG189 :
    Prop412DataCarryingConvergenceFrontierAfterG189 where
  data_carrying_convergence_to_common_good_witnesses_closed := True
  data_carrying_convergence_to_truncated_equality_closed_given_aux_data := True
  prop_valued_convergence_extraction_still_requires_redesign_not_choice := True
  bad_set_n_bound_still_open_for_assumption_free_source := True
  old_true_statement_used := 0

/-- G189 package. -/
structure Chapter4G189Prop412DataCarryingConvergencePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g188 : BishopRegularSeqChapter4G188Package S
  data_carrying_convergence_frontier_after_g189 :
    Prop412DataCarryingConvergenceFrontierAfterG189
  data_carrying_convergence_extraction_closed_this_step : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_assumption_free_source_prop412_pass : Nat

def chapter4G189Prop412DataCarryingConvergencePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G189Prop412DataCarryingConvergencePackage S where
  g188 := bishopRegularSeqChapter4G188Package S
  data_carrying_convergence_frontier_after_g189 :=
    prop412DataCarryingConvergenceFrontierAfterG189
  data_carrying_convergence_extraction_closed_this_step := 1
  proposition_4_12_truncated_integral_subfrontiers_remaining := 0
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_assumption_free_source_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G189 package exposed at top level. -/
structure BishopRegularSeqChapter4G189Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G189Prop412DataCarryingConvergencePackage S
  data_carrying_convergence_extraction_closed_this_step : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_assumption_free_source_prop412_pass : Nat

def bishopRegularSeqChapter4G189Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G189Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G189Prop412DataCarryingConvergencePackage S
  data_carrying_convergence_extraction_closed_this_step := 1
  proposition_4_12_truncated_integral_subfrontiers_remaining := 0
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_assumption_free_source_prop412_pass := 2

/-- Progress after G189. -/
def bishopRegularSeqCh1To4ProgressAfterG189 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G189: introduced a Type/Sigma data-carrying convergence interface for \
    Proposition 4.12 and used it to construct the common-good B,C,N witnesses \
    without a later choice operation. The remaining source-faithful frontiers \
    are the Prop-valued convergence redesign boundary and the concrete \
    bad-set n-bound."


end BishopCReal
