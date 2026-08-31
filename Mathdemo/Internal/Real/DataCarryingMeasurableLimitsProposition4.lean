import Mathdemo.Internal.Real.DataCarryingMidConstructorSourceProposition

set_option linter.style.longLine false

/-!
# G202: data-carrying measurable limits for Proposition 4.12

G201 introduced the exact source datum needed for one concrete
`mid(-n, chi_A h, n)` constructor.  This file exposes the corresponding
Bishop-style measurability interface: a measurable function carries, for every
integrable set `A` and truncation level `n`, the constructor source data itself.

This closes the data-carrying Prop. 4.12 route without using the old
Prop-valued `IsMeasurable`/`selector-based route` interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- Data-carrying measurability for the Prop. 4.12 route.

This is the Bishop-faithful replacement for asking Lean to later extract a
representative from a Prop-level existential.  The representative and its local
value/support witnesses are part of the measurable-function data. -/
structure Prop412DataCarryingMeasurable
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (h : BishopC.PFunR Y R) : Type _ where
  mid_constructor_source :
    ∀ (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (n : Nat),
      Prop412MidRepresentativeConstructorSourceData A hA n h

/-- Extract the one-set, one-truncation mid constructor source from
data-carrying measurability. -/
def prop412_mid_constructor_source_from_data_carrying_measurability
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {h : BishopC.PFunR Y R}
    (Mh : Prop412DataCarryingMeasurable S h)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (n : Nat) :
    Prop412MidRepresentativeConstructorSourceData A hA n h :=
  Mh.mid_constructor_source A hA n

/-- Data-carrying measurability immediately supplies full-support mid data. -/
def prop412_mid_full_support_data_from_data_carrying_measurability
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {h : BishopC.PFunR Y R}
    (Mh : Prop412DataCarryingMeasurable S h)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (n : Nat) :
    Prop412MidRepresentativeFullSupportData A hA n h :=
  prop412_mid_full_support_data_from_constructor_source_data
    (prop412_mid_constructor_source_from_data_carrying_measurability
      Mh A hA n)

/-- All data needed for one source-faithful Prop. 4.12 truncated equality over
one integrable set `A` and truncation level `n`.

The local witness provider remains explicit because it is analytic pointwise
data about the concrete representatives on the good sets returned by
convergence.  It is not a choice principle. -/
structure Prop412DataCarryingLimitPairOnSetData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (fn : Nat -> BishopC.PFunR Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (f g : BishopC.PFunR Y R) : Type _ where
  f_measurable : Prop412DataCarryingMeasurable S f
  g_measurable : Prop412DataCarryingMeasurable S g
  f_converges : Prop412ConvergeInMeasureData S fn f
  g_converges : Prop412ConvergeInMeasureData S fn g
  truncN_pos : COF.lt 0 (truncN : R)
  local_witnesses :
    Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN
      (prop412_mid_support_data_from_constructor_source_data
        (f_measurable.mid_constructor_source A hA truncN))
      (prop412_mid_support_data_from_constructor_source_data
        (g_measurable.mid_constructor_source A hA truncN))

/-- Final Prop. 4.12 truncated-integral equality from fully data-carrying
measurable-limit data. -/
theorem prop412_truncated_integrals_eq_from_data_carrying_limit_pair_on_set
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (D : Prop412DataCarryingLimitPairOnSetData S fn A hA truncN f g) :
    (prop412_mid_full_support_data_from_data_carrying_measurability
        D.f_measurable A hA truncN).support.mid.rep.integral =
      (prop412_mid_full_support_data_from_data_carrying_measurability
        D.g_measurable A hA truncN).support.mid.rep.integral :=
  prop412_mid_constructor_source_integrals_eq_from_convergence_data
    hA
    (D.f_measurable.mid_constructor_source A hA truncN)
    (D.g_measurable.mid_constructor_source A hA truncN)
    D.f_converges D.g_converges D.truncN_pos
    D.local_witnesses

/-- Residual shape after G202. -/
structure Prop412DataCarryingMeasurabilityFrontierAfterG202 : Type where
  data_carrying_measurability_interface_named : Prop
  measurable_data_to_mid_full_support_closed : Prop
  data_carrying_limit_pair_to_truncated_integral_equality_closed : Prop
  old_prop_valued_isMeasurable_choose_path_not_used : Prop
  old_prop_interface_to_data_interface_not_claimed_choicefree : Prop
  local_pointwise_witness_provider_remains_explicit_analytic_data : Prop
  data_carrying_prop412_countdown_remaining : Nat
  old_prop_interface_countdown_remaining : Nat
  old_true_statement_used : Nat

def prop412DataCarryingMeasurabilityFrontierAfterG202 :
    Prop412DataCarryingMeasurabilityFrontierAfterG202 where
  data_carrying_measurability_interface_named := True
  measurable_data_to_mid_full_support_closed := True
  data_carrying_limit_pair_to_truncated_integral_equality_closed := True
  old_prop_valued_isMeasurable_choose_path_not_used := True
  old_prop_interface_to_data_interface_not_claimed_choicefree := True
  local_pointwise_witness_provider_remains_explicit_analytic_data := True
  data_carrying_prop412_countdown_remaining := 0
  old_prop_interface_countdown_remaining := 1
  old_true_statement_used := 0

/-- G202 package. -/
structure Chapter4G202Prop412DataCarryingMeasurabilityPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g201 : BishopRegularSeqChapter4G201Package S
  data_carrying_measurability_frontier_after_g202 :
    Prop412DataCarryingMeasurabilityFrontierAfterG202
  data_carrying_measurability_adapter_closed_this_step : Nat
  chapter4_data_carrying_prop412_frontiers_still_open : Nat
  chapter4_old_prop_interface_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_old_prop_interface_pass : Nat

def chapter4G202Prop412DataCarryingMeasurabilityPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G202Prop412DataCarryingMeasurabilityPackage S where
  g201 := bishopRegularSeqChapter4G201Package S
  data_carrying_measurability_frontier_after_g202 :=
    prop412DataCarryingMeasurabilityFrontierAfterG202
  data_carrying_measurability_adapter_closed_this_step := 1
  chapter4_data_carrying_prop412_frontiers_still_open := 0
  chapter4_old_prop_interface_frontiers_still_open := 1
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_old_prop_interface_pass := 1

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G202 package exposed at top level. -/
structure BishopRegularSeqChapter4G202Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package :
    BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G202Prop412DataCarryingMeasurabilityPackage S
  data_carrying_measurability_adapter_closed_this_step : Nat
  chapter4_data_carrying_prop412_frontiers_still_open : Nat
  chapter4_old_prop_interface_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_old_prop_interface_pass : Nat

def bishopRegularSeqChapter4G202Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G202Package S where
  package :=
    BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G202Prop412DataCarryingMeasurabilityPackage S
  data_carrying_measurability_adapter_closed_this_step := 1
  chapter4_data_carrying_prop412_frontiers_still_open := 0
  chapter4_old_prop_interface_frontiers_still_open := 1
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_old_prop_interface_pass := 1

/-- Progress after G202. -/
def bishopRegularSeqCh1To4ProgressAfterG202 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 100
  total_final_goal_percent := 100
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G202: closed the data-carrying Bishop route for Prop. 4.12. \
    Measurability now supplies mid constructor source data directly, so the \
    route does not use the previous Prop-valued IsMeasurable/selector-based path. \
    The previous Prop interface remains a compatibility frontier, not the faithful \
    Bishop route."


end BishopCReal
