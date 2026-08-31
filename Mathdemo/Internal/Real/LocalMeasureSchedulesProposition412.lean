import Mathdemo.Internal.Real.MeasureCapEpsilonSchedulesProposition4

set_option linter.style.longLine false

/-!
# G199: local A-measure schedules for Proposition 4.12

G198 converted measure-cap schedule data into the G196 all-pair epsilon
schedule.  That was useful, but still stronger than the source proof: in
Proposition 4.12 the good sets `B` and `C` are returned by convergence and
satisfy `B ∧ C ⊆ A`, so the relevant cap is simply `mu(A)`.

This file localizes the schedule to common-good pairs.  It proves the cap
`mu(B ∧ C) <= mu(A)` from the carried common-good data, then uses the arithmetic
budget based on `mu(A)` to build the G195 construction data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- For a common-good pair in Prop. 4.12, the intersection `B ∧ C` is contained
in the original integrable set `A`, hence its measure is bounded by `mu(A)`. -/
theorem prop412_common_good_pair_intersection_measure_le_A
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A B C : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hB : BishopC.IntegrableSet1 S B)
    (hC : BishopC.IntegrableSet1 S C)
    {f g : BishopC.PFunR Y R}
    {eps : R} {seqN : Nat}
    (Common : Prop412CommonGoodPair fn f g A hA eps seqN B hB C hC) :
    BishopC.Le
      (BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC))
      (BishopC.measure1 S hA) := by
  have hsub :
      (BishopC.BSet.and B C).S1 ⊆ A.S1 :=
    (prop412_intersection_domains Common.1 Common.2.2.2.1).1
  exact
    MeasureDefectBridge.prop412_measure1_mono_of_s1_subset
      (BishopC.IntegrableSet1_and hB hC) hA hsub

/-- A dyadic epsilon schedule whose only measure cap is the source set `A`.

This is the constructive reading of "choose epsilon small enough that
`eps * mu(A) + (n+n) * eps < 2^-k`"; the common-good pair later supplies
`mu(B ∧ C) <= mu(A)`. -/
structure Prop412TwoNatDyadicAMeasureScheduleData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (k : Nat) : Type _ where
  eps : R
  heps : COF.lt 0 eps
  arithmetic_budget_A :
    COF.lt
      (eps * BishopC.measure1 S hA +
        ((truncN : R) + (truncN : R)) * eps)
      (COF.halfPow (R := R) k)

/-- An `A`-measure schedule and local witnesses generate one G195 construction
datum.  The arithmetic is local to the common-good pair returned by convergence,
not to arbitrary integrable sets. -/
def prop412_dyadic_two_nat_common_good_construction_from_A_measure_schedule
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    {k : Nat}
    (Schedule : Prop412TwoNatDyadicAMeasureScheduleData S A hA truncN k)
    (Local : Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN F G) :
    Prop412DyadicTwoNatCommonGoodConstructionData fn A hA truncN F G k where
  eps := Schedule.eps
  heps := Schedule.heps
  aux := by
    intro seqN B hB C hC Common
    let L := Local.data B hB C hC
    have hmeasure :
        BishopC.Le
          (BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC))
          (BishopC.measure1 S hA) :=
      prop412_common_good_pair_intersection_measure_le_A
        hA hB hC Common
    have hmul0 :
        BishopC.Le
          (BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC) *
            Schedule.eps)
          (BishopC.measure1 S hA * Schedule.eps) :=
      BishopC.lemma33_mul_le_mul_right hmeasure
        (BishopC.le_of_lt Schedule.heps)
    have hmul :
        BishopC.Le
          (Schedule.eps *
            BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC))
          (Schedule.eps * BishopC.measure1 S hA) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul0
    have hle :
        BishopC.Le
          (Schedule.eps *
              BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC) +
            ((truncN : R) + (truncN : R)) * Schedule.eps)
          (Schedule.eps * BishopC.measure1 S hA +
            ((truncN : R) + (truncN : R)) * Schedule.eps) :=
      BishopC.lemma33_add_le_add hmul
        (BishopC.le_refl (((truncN : R) + (truncN : R)) * Schedule.eps))
    exact
      { chiA_abs_on_good := L.chiA_abs_on_good
        pointwise_seed := L.pointwise_seed
        arithmetic_budget :=
          BishopC.lt_of_le_of_lt hle Schedule.arithmetic_budget_A }

/-- `A`-measure schedules for every dyadic target. -/
structure Prop412AllTwoNatAMeasureScheduleData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) : Type _ where
  data : ∀ k : Nat, Prop412TwoNatDyadicAMeasureScheduleData S A hA truncN k

/-- All `A`-measure schedules generate all G195 construction data. -/
def prop412_all_two_nat_common_good_construction_from_A_measure_schedules
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (Schedules : Prop412AllTwoNatAMeasureScheduleData S A hA truncN)
    (Local : Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN F G) :
    Prop412AllTwoNatCommonGoodConstructionData fn A hA truncN F G where
  data := by
    intro k
    exact prop412_dyadic_two_nat_common_good_construction_from_A_measure_schedule
      hA F G (Schedules.data k) Local

/-- Final equality from full-support mid data and source-local `A`-measure
schedules. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data_full_support_A_measure_schedules
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeFullSupportData A hA truncN f)
    (G : Prop412MidRepresentativeFullSupportData A hA truncN g)
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (truncN_pos : COF.lt 0 (truncN : R))
    (Schedules : Prop412AllTwoNatAMeasureScheduleData S A hA truncN)
    (Local :
      Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN
        F.support G.support) :
    F.support.mid.rep.integral = G.support.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_two_nat_bound_sources
    hA F.support G.support hf hg
    F.bound_source G.bound_source truncN_pos
    (prop412_all_two_nat_common_good_construction_from_A_measure_schedules
      hA F.support G.support Schedules Local)

/-- Residual shape after G199. -/
structure Prop412AMeasureScheduleFrontierAfterG199 : Type where
  common_good_intersection_measure_le_A_closed : Prop
  A_measure_schedule_to_g195_construction_closed : Prop
  full_support_A_measure_schedule_to_truncated_equality_closed : Prop
  construct_A_measure_epsilon_schedules_from_archimedean_data_still_needed : Prop
  actual_mid_constructor_should_return_full_support_data_still_needed : Prop
  prop_valued_convergence_extraction_still_requires_redesign_not_choice : Prop
  old_true_statement_used : Nat

def prop412AMeasureScheduleFrontierAfterG199 :
    Prop412AMeasureScheduleFrontierAfterG199 where
  common_good_intersection_measure_le_A_closed := True
  A_measure_schedule_to_g195_construction_closed := True
  full_support_A_measure_schedule_to_truncated_equality_closed := True
  construct_A_measure_epsilon_schedules_from_archimedean_data_still_needed :=
    True
  actual_mid_constructor_should_return_full_support_data_still_needed := True
  prop_valued_convergence_extraction_still_requires_redesign_not_choice := True
  old_true_statement_used := 0

/-- G199 package. -/
structure Chapter4G199Prop412AMeasureSchedulePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g198 : BishopRegularSeqChapter4G198Package S
  A_measure_schedule_frontier_after_g199 :
    Prop412AMeasureScheduleFrontierAfterG199
  A_measure_schedule_adapter_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_assumption_free_source_prop412_pass : Nat

def chapter4G199Prop412AMeasureSchedulePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G199Prop412AMeasureSchedulePackage S where
  g198 := bishopRegularSeqChapter4G198Package S
  A_measure_schedule_frontier_after_g199 :=
    prop412AMeasureScheduleFrontierAfterG199
  A_measure_schedule_adapter_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_assumption_free_source_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G199 package exposed at top level. -/
structure BishopRegularSeqChapter4G199Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G199Prop412AMeasureSchedulePackage S
  A_measure_schedule_adapter_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_assumption_free_source_prop412_pass : Nat

def bishopRegularSeqChapter4G199Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G199Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G199Prop412AMeasureSchedulePackage S
  A_measure_schedule_adapter_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_assumption_free_source_prop412_pass := 2

/-- Progress after G199. -/
def bishopRegularSeqCh1To4ProgressAfterG199 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G199: localized the Prop. 4.12 n+n epsilon schedule to the source set A. \
    For common-good B,C, the proof now derives mu(B and C) <= mu(A), so the \
    remaining epsilon budget only has to control eps*mu(A)+(n+n)*eps."


end BishopCReal
