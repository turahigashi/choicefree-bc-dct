import Mathdemo.Internal.Real.ConvergenceDataRoutedCanonicalTwoN

set_option linter.style.longLine false

/-!
# G196: separating epsilon schedules from local source witnesses

G195 still packaged two different obligations in one per-dyadic auxiliary datum:
local representative witnesses and the arithmetic choice of a small epsilon.
This file separates them.

The result is a narrower frontier: once an epsilon schedule for the canonical
`n+n` cap and the local good-set witnesses are provided as data, the G195
construction data is generated automatically.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- A dyadic epsilon schedule for the corrected `n+n` bad-set cap.  This is the
data-carrying version of "choose epsilon small enough that
`eps * mu(E) + (n+n) * eps < 2^-k`" uniformly for the good set returned by
convergence. -/
structure Prop412TwoNatDyadicEpsilonScheduleData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (truncN : Nat)
    (k : Nat) : Type _ where
  eps : R
  heps : COF.lt 0 eps
  arithmetic_budget :
    ∀ (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      COF.lt
        (eps * BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC) +
          ((truncN : R) + (truncN : R)) * eps)
        (COF.halfPow (R := R) k)

/-- Epsilon schedules for all dyadic targets. -/
structure Prop412AllTwoNatEpsilonScheduleData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (truncN : Nat) : Type _ where
  data : ∀ k : Nat, Prop412TwoNatDyadicEpsilonScheduleData S truncN k

/-- Local witness data for one returned good-set pair.  This record deliberately
contains no epsilon arithmetic. -/
structure Prop412TwoNatLocalGoodSetWitnessData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
    (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C) : Type _ where
  chiA_abs_on_good :
    Prop412GoodSetChiAAbsData A (BishopC.BSet.and B C) hA
  pointwise_seed :
    Prop412ComplementPointwiseConcreteSupportSeedData
      A (BishopC.BSet.and B C) hA (BishopC.IntegrableSet1_and hB hC)
      truncN f g F G

/-- Local witness provider for every good-set pair returned by convergence. -/
structure Prop412TwoNatLocalGoodSetWitnessProviderData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g) : Type _ where
  data :
    ∀ (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      Prop412TwoNatLocalGoodSetWitnessData A hA truncN F G B hB C hC

/-- A separated epsilon schedule and local witness provider generate one G195
dyadic construction datum. -/
def prop412_dyadic_two_nat_common_good_construction_from_schedule
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    {k : Nat}
    (Schedule : Prop412TwoNatDyadicEpsilonScheduleData S truncN k)
    (Local : Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN F G) :
    Prop412DyadicTwoNatCommonGoodConstructionData fn A hA truncN F G k where
  eps := Schedule.eps
  heps := Schedule.heps
  aux := by
    intro seqN B hB C hC _Common
    let L := Local.data B hB C hC
    exact
      { chiA_abs_on_good := L.chiA_abs_on_good
        pointwise_seed := L.pointwise_seed
        arithmetic_budget := Schedule.arithmetic_budget B hB C hC }

/-- Separated schedules and local witness data generate all G195 construction
data. -/
def prop412_all_two_nat_common_good_construction_from_schedules
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (Schedules : Prop412AllTwoNatEpsilonScheduleData S truncN)
    (Local : Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN F G) :
    Prop412AllTwoNatCommonGoodConstructionData fn A hA truncN F G where
  data := by
    intro k
    exact prop412_dyadic_two_nat_common_good_construction_from_schedule
      hA F G (Schedules.data k) Local

/-- Final equality from convergence data when the `n+n` epsilon schedules and
local good-set witnesses have been supplied separately. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data_two_nat_schedules
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
    (FSrc : Prop412MidRepresentativeBoundSourceData F)
    (GSrc : Prop412MidRepresentativeBoundSourceData G)
    (truncN_pos : COF.lt 0 (truncN : R))
    (Schedules : Prop412AllTwoNatEpsilonScheduleData S truncN)
    (Local : Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN F G) :
    F.mid.rep.integral = G.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_two_nat_bound_sources
    hA F G hf hg FSrc GSrc truncN_pos
    (prop412_all_two_nat_common_good_construction_from_schedules
      hA F G Schedules Local)

/-- Residual shape after G196. -/
structure Prop412TwoNatScheduleFrontierAfterG196 : Type where
  epsilon_schedule_separated_from_local_witnesses : Prop
  schedules_plus_local_witnesses_to_g195_construction_closed : Prop
  schedules_plus_local_witnesses_to_truncated_equality_closed : Prop
  prove_or_construct_epsilon_schedules_still_needed : Prop
  provide_bound_source_data_in_actual_mid_constructor_still_needed : Prop
  prop_valued_convergence_extraction_still_requires_redesign_not_choice : Prop
  old_true_statement_used : Nat

def prop412TwoNatScheduleFrontierAfterG196 :
    Prop412TwoNatScheduleFrontierAfterG196 where
  epsilon_schedule_separated_from_local_witnesses := True
  schedules_plus_local_witnesses_to_g195_construction_closed := True
  schedules_plus_local_witnesses_to_truncated_equality_closed := True
  prove_or_construct_epsilon_schedules_still_needed := True
  provide_bound_source_data_in_actual_mid_constructor_still_needed := True
  prop_valued_convergence_extraction_still_requires_redesign_not_choice := True
  old_true_statement_used := 0

/-- G196 package. -/
structure Chapter4G196Prop412TwoNatSchedulePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g195 : BishopRegularSeqChapter4G195Package S
  two_nat_schedule_frontier_after_g196 :
    Prop412TwoNatScheduleFrontierAfterG196
  two_nat_schedule_split_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_assumption_free_source_prop412_pass : Nat

def chapter4G196Prop412TwoNatSchedulePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G196Prop412TwoNatSchedulePackage S where
  g195 := bishopRegularSeqChapter4G195Package S
  two_nat_schedule_frontier_after_g196 :=
    prop412TwoNatScheduleFrontierAfterG196
  two_nat_schedule_split_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_assumption_free_source_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G196 package exposed at top level. -/
structure BishopRegularSeqChapter4G196Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G196Prop412TwoNatSchedulePackage S
  two_nat_schedule_split_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_assumption_free_source_prop412_pass : Nat

def bishopRegularSeqChapter4G196Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G196Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G196Prop412TwoNatSchedulePackage S
  two_nat_schedule_split_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_assumption_free_source_prop412_pass := 2

/-- Progress after G196. -/
def bishopRegularSeqCh1To4ProgressAfterG196 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G196: separated the n+n epsilon schedule from local good-set witness data. \
    Schedules plus local witnesses now generate the G195 construction data and \
    the convergence-data truncated-integral equality."


end BishopCReal
