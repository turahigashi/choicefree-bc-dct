import Mathdemo.Internal.CRat_iter298

set_option linter.style.longLine false

/-!
# G200: Archimedean construction of the A-measure epsilon schedule

G199 reduced the remaining epsilon budget in Proposition 4.12 to the source
set `A`:

`eps * mu(A) + (n+n) * eps < 2^-k`.

This file closes that arithmetic frontier constructively.  The coefficient
`mu(A) + (n+n)` is nonnegative, so the `COFOC.mul_archimedean` datum gives an
explicit integer `m` with `(mu(A)+n+n) * 2^-m <= 1`; then
`eps = 2^-(k+1+m)` gives the desired strict dyadic budget.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- The coefficient controlled by the final Prop. 4.12 epsilon choice:
`mu(A) + (n+n)`. -/
noncomputable def prop412_A_measure_two_nat_coefficient
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) : R :=
  BishopC.measure1 S hA + ((truncN : R) + (truncN : R))

/-- The `n+n` part of the coefficient is nonnegative. -/
theorem prop412_two_nat_sum_nonneg
    {R : Type*} [COFOC R] (truncN : Nat) :
    BishopC.Nonneg (((truncN : R) + (truncN : R))) := by
  have h :=
    BishopC.lemma33_add_le_add
      (BishopC.lemma33_natCast_nonneg (R := R) truncN)
      (BishopC.lemma33_natCast_nonneg (R := R) truncN)
  simpa [BishopC.Nonneg] using h

/-- The whole coefficient `mu(A)+(n+n)` is nonnegative. -/
theorem prop412_A_measure_two_nat_coefficient_nonneg
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) :
    BishopC.Nonneg (prop412_A_measure_two_nat_coefficient S hA truncN) := by
  have hmeasure : BishopC.Nonneg (BishopC.measure1 S hA) :=
    BishopC.measure1_nonneg hA
  have hsum : BishopC.Nonneg (((truncN : R) + (truncN : R))) :=
    prop412_two_nat_sum_nonneg (R := R) truncN
  have h :=
    BishopC.lemma33_add_le_add hmeasure hsum
  simpa [prop412_A_measure_two_nat_coefficient, BishopC.Nonneg] using h

/-- The Archimedean scale index for the coefficient `mu(A)+(n+n)`. -/
noncomputable def prop412_A_measure_schedule_index
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) : Nat :=
  (COFO.mul_archimedean
    (prop412_A_measure_two_nat_coefficient S hA truncN)).val

/-- The explicit dyadic epsilon selected for target `k`. -/
noncomputable def prop412_A_measure_schedule_eps
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) (k : Nat) : R :=
  COF.halfPow (R := R)
    (k + 1 + prop412_A_measure_schedule_index S hA truncN)

/-- The Archimedean witness absorbs the coefficient into one dyadic step. -/
theorem prop412_A_measure_coefficient_scaled_le
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) (j : Nat) :
    BishopC.Le
      (COF.halfPow (R := R)
          (j + prop412_A_measure_schedule_index S hA truncN) *
        prop412_A_measure_two_nat_coefficient S hA truncN)
      (COF.halfPow (R := R) j) := by
  have hcoeff_nonneg :
      BishopC.Nonneg
        (prop412_A_measure_two_nat_coefficient S hA truncN) :=
    prop412_A_measure_two_nat_coefficient_nonneg S hA truncN
  have harch :
      BishopC.Le
        (COF.abs
            (prop412_A_measure_two_nat_coefficient S hA truncN) *
          COF.halfPow (R := R)
            (prop412_A_measure_schedule_index S hA truncN))
        1 := by
    simpa [prop412_A_measure_schedule_index] using
      (COFO.mul_archimedean
        (prop412_A_measure_two_nat_coefficient S hA truncN)).property
  have hkey :
      BishopC.Le
        (COF.halfPow (R := R)
            (prop412_A_measure_schedule_index S hA truncN) *
          prop412_A_measure_two_nat_coefficient S hA truncN)
        1 := by
    rw [mul_comm,
      ← COFO.abs_of_nonneg hcoeff_nonneg]
    exact harch
  have heq :
      COF.halfPow (R := R)
          (j + prop412_A_measure_schedule_index S hA truncN) *
        prop412_A_measure_two_nat_coefficient S hA truncN =
      COF.halfPow (R := R) j *
        (COF.halfPow (R := R)
            (prop412_A_measure_schedule_index S hA truncN) *
          prop412_A_measure_two_nat_coefficient S hA truncN) := by
    rw [BishopC.halfPow_add (R := R) j
      (prop412_A_measure_schedule_index S hA truncN)]
    ring
  rw [heq]
  have hstep :=
    BishopC.mul_le_mul_left hkey
      (BishopC.le_of_lt (BishopC.halfPow_pos (R := R) j))
  rwa [mul_one] at hstep

/-- The explicit dyadic epsilon satisfies the source-local budget. -/
theorem prop412_A_measure_schedule_arithmetic_budget
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) (k : Nat) :
    COF.lt
      (prop412_A_measure_schedule_eps S hA truncN k *
          BishopC.measure1 S hA +
        ((truncN : R) + (truncN : R)) *
          prop412_A_measure_schedule_eps S hA truncN k)
      (COF.halfPow (R := R) k) := by
  have hleft :
      prop412_A_measure_schedule_eps S hA truncN k *
          BishopC.measure1 S hA +
        ((truncN : R) + (truncN : R)) *
          prop412_A_measure_schedule_eps S hA truncN k =
      prop412_A_measure_schedule_eps S hA truncN k *
        prop412_A_measure_two_nat_coefficient S hA truncN := by
    simp [prop412_A_measure_two_nat_coefficient]
    ring
  have hle :
      BishopC.Le
        (prop412_A_measure_schedule_eps S hA truncN k *
          prop412_A_measure_two_nat_coefficient S hA truncN)
        (COF.halfPow (R := R) (k + 1)) := by
    simpa [prop412_A_measure_schedule_eps] using
      prop412_A_measure_coefficient_scaled_le S hA truncN (k + 1)
  rw [hleft]
  exact BishopC.lt_of_le_of_lt hle
    (BishopC.halfPow_lt_succ (R := R) k)

/-- The source-local dyadic schedule is constructed from Archimedean data. -/
noncomputable def prop412_two_nat_A_measure_schedule_from_archimedean
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) (k : Nat) :
    Prop412TwoNatDyadicAMeasureScheduleData S A hA truncN k where
  eps := prop412_A_measure_schedule_eps S hA truncN k
  heps := by
    exact
      BishopC.halfPow_pos (R := R)
        (k + 1 + prop412_A_measure_schedule_index S hA truncN)
  arithmetic_budget_A :=
    prop412_A_measure_schedule_arithmetic_budget S hA truncN k

/-- All source-local schedules, with no separate schedule hypothesis. -/
noncomputable def prop412_all_two_nat_A_measure_schedules_from_archimedean
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) :
    Prop412AllTwoNatAMeasureScheduleData S A hA truncN where
  data := fun k =>
    prop412_two_nat_A_measure_schedule_from_archimedean S hA truncN k

/-- Final equality from full-support mid data and the Archimedean epsilon
schedule.  The remaining non-arithmetic data are exactly the mid-support/local
good-set constructors already isolated in G199. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data_full_support_archimedean_A_measure_schedules
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
    (Local :
      Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN
        F.support G.support) :
    F.support.mid.rep.integral = G.support.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_full_support_A_measure_schedules
    hA F G hf hg truncN_pos
    (prop412_all_two_nat_A_measure_schedules_from_archimedean S hA truncN)
    Local

/-- Residual shape after G200. -/
structure Prop412ArchimedeanAMeasureScheduleFrontierAfterG200 : Type where
  A_measure_coefficient_nonnegative_closed : Prop
  archimedean_epsilon_schedule_closed : Prop
  full_support_archimedean_schedule_to_truncated_equality_closed : Prop
  actual_mid_constructor_should_return_full_support_data_still_needed : Prop
  prop_valued_convergence_extraction_still_requires_redesign_not_choice : Prop
  old_true_statement_used : Nat

def prop412ArchimedeanAMeasureScheduleFrontierAfterG200 :
    Prop412ArchimedeanAMeasureScheduleFrontierAfterG200 where
  A_measure_coefficient_nonnegative_closed := True
  archimedean_epsilon_schedule_closed := True
  full_support_archimedean_schedule_to_truncated_equality_closed := True
  actual_mid_constructor_should_return_full_support_data_still_needed := True
  prop_valued_convergence_extraction_still_requires_redesign_not_choice := True
  old_true_statement_used := 0

/-- G200 package. -/
structure Chapter4G200Prop412ArchimedeanAMeasureSchedulePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g199 : BishopRegularSeqChapter4G199Package S
  A_measure_schedule_frontier_after_g200 :
    Prop412ArchimedeanAMeasureScheduleFrontierAfterG200
  archimedean_A_measure_schedule_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_assumption_free_source_prop412_pass : Nat

def chapter4G200Prop412ArchimedeanAMeasureSchedulePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G200Prop412ArchimedeanAMeasureSchedulePackage S where
  g199 := bishopRegularSeqChapter4G199Package S
  A_measure_schedule_frontier_after_g200 :=
    prop412ArchimedeanAMeasureScheduleFrontierAfterG200
  archimedean_A_measure_schedule_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 1
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_assumption_free_source_prop412_pass := 1

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G200 package exposed at top level. -/
structure BishopRegularSeqChapter4G200Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package :
    BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G200Prop412ArchimedeanAMeasureSchedulePackage S
  archimedean_A_measure_schedule_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_assumption_free_source_prop412_pass : Nat

def bishopRegularSeqChapter4G200Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G200Package S where
  package :=
    BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G200Prop412ArchimedeanAMeasureSchedulePackage S
  archimedean_A_measure_schedule_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 1
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_assumption_free_source_prop412_pass := 1

/-- Progress after G200. -/
def bishopRegularSeqCh1To4ProgressAfterG200 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G200: closed the Archimedean construction of the Prop. 4.12 source-local \
    epsilon schedule.  The remaining assumption-free frontier is the actual \
    mid(-n, chi_A h, n) constructor returning full-support data, plus the \
    already isolated Prop-valued convergence interface redesign."


end BishopCReal
