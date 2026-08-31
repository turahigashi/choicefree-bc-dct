import Mathdemo.Internal.Real.ClosedChapter4TheoryInterfaceBishop

set_option linter.style.longLine false

/-!
# G205: removing the global closed-theory parameter from Prop. 4.12

G204 still used a global `BishopRealChapter4ClosedTheory` parameter.  That was
useful for closing the Prop. 4.12 proof shape, but it also hid construction
obligations inside a theory record.

This file removes that global parameter.  The remaining data are attached to the
Bishop measurable function object itself.  This is still not the final
raw-Bishop-real discharge: the intrinsic function data must next be constructed
from the earlier Chapter 4 development, especially the data-carrying 4.10 route
and the local representative-witness synthesis.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Prop412AssumptionDischarge

open Proposition412.TruncatedIntegralBridge
open SourceComplete412

/-- Intrinsic data carried by a Bishop-real measurable function for the Prop. 4.12
route.

This is not a global theory assumption.  The data are attached to the function
object.  The next discharge target is to construct this record from the earlier
Chapter 4 Bishop-real machinery instead of taking it as input. -/
structure Prop412IntrinsicBishopMeasurable
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (h : BishopC.PFunR Y R) : Type _ where
  measurable : Prop412DataCarryingMeasurable S h
  local_witnesses_with :
    ∀ {g : BishopC.PFunR Y R}
      (Mg : Prop412DataCarryingMeasurable S g)
      (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (truncN : Nat),
      Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN
        (prop412_mid_support_data_from_constructor_source_data
          (measurable.mid_constructor_source A hA truncN))
        (prop412_mid_support_data_from_constructor_source_data
          (Mg.mid_constructor_source A hA truncN))

/-- Limit data with no global closed-theory parameter.  The convergence datum is
still a genuine hypothesis of Proposition 4.12; it is not a hidden construction
assumption. -/
structure Prop412IntrinsicBishopLimit
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.PFunR Y R)
    (f : BishopC.PFunR Y R) : Type _ where
  function_data : Prop412IntrinsicBishopMeasurable S f
  converges : Prop412ConvergeInMeasureData S fn f

/-- One-set, one-truncation Prop. 4.12 equality with no global `T` argument and
no Theorem-4.10 field argument. -/
theorem prop412_truncated_integral_eq_from_intrinsic_bishop_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (F : Prop412IntrinsicBishopLimit fn f)
    (G : Prop412IntrinsicBishopLimit fn g)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (truncN_pos : COF.lt 0 (truncN : R)) :
    (prop412_mid_full_support_data_from_data_carrying_measurability
        F.function_data.measurable A hA truncN).support.mid.rep.integral =
      (prop412_mid_full_support_data_from_data_carrying_measurability
        G.function_data.measurable A hA truncN).support.mid.rep.integral := by
  exact
    prop412_truncated_integrals_eq_from_data_carrying_limit_pair_on_set
      { f_measurable := F.function_data.measurable
        g_measurable := G.function_data.measurable
        f_converges := F.converges
        g_converges := G.converges
        truncN_pos := truncN_pos
        local_witnesses :=
          F.function_data.local_witnesses_with
            G.function_data.measurable A hA truncN }

/-- Function-level equality package with no global closed-theory parameter. -/
def prop412_function_eq_from_intrinsic_bishop_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (F : Prop412IntrinsicBishopLimit (S := S) fn f)
    (G : Prop412IntrinsicBishopLimit (S := S) fn g) :
    Prop412DataCarryingMeasurableFunctionEqualityData S f g where
  f_measurable := F.function_data.measurable
  g_measurable := G.function_data.measurable
  truncated_integral_eq := by
    intro A hA truncN truncN_pos
    exact prop412_truncated_integral_eq_from_intrinsic_bishop_data
      F G A hA truncN truncN_pos

/-- Debt ledger after removing the global theory parameter.  This is deliberately
kept as data in Lean so the remaining construction obligations cannot be hidden
behind the progress meter. -/
structure Prop412AssumptionDischargeLedger : Type where
  global_closed_theory_parameter_removed : Prop
  theorem410_field_argument_removed_from_prop412 : Prop
  remaining_construct_intrinsic_measurability_from_chapter4_10 : Nat
  remaining_construct_local_witnesses_from_bishop_real_representatives : Nat
  convergence_data_is_source_hypothesis_not_discharge_debt : Nat
  old_prop_valued_isMeasurable_choose_route_used : Nat
  external_choice_principle_added : Nat
  raw_bishop_real_to_prop412_complete : Nat

def prop412AssumptionDischargeLedgerAfterG205 :
    Prop412AssumptionDischargeLedger where
  global_closed_theory_parameter_removed := True
  theorem410_field_argument_removed_from_prop412 := True
  remaining_construct_intrinsic_measurability_from_chapter4_10 := 1
  remaining_construct_local_witnesses_from_bishop_real_representatives := 1
  convergence_data_is_source_hypothesis_not_discharge_debt := 0
  old_prop_valued_isMeasurable_choose_route_used := 0
  external_choice_principle_added := 0
  raw_bishop_real_to_prop412_complete := 0

end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Prop412AssumptionDischarge

/-- G205 package exposed at top level. -/
structure BishopRegularSeqChapter4G205Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g204 : BishopRegularSeqChapter4G204Package S
  assumption_discharge_ledger :
    BishopRegularSeqChapter4.Prop412AssumptionDischarge.Prop412AssumptionDischargeLedger
  global_closed_theory_parameter_removed_this_step : Nat
  remaining_assumption_discharge_steps_for_raw_bishop_real_prop412 : Nat

def bishopRegularSeqChapter4G205Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G205Package S where
  g204 := bishopRegularSeqChapter4G204Package S
  assumption_discharge_ledger :=
    BishopRegularSeqChapter4.Prop412AssumptionDischarge.prop412AssumptionDischargeLedgerAfterG205
  global_closed_theory_parameter_removed_this_step := 1
  remaining_assumption_discharge_steps_for_raw_bishop_real_prop412 := 2

/-- Corrected progress after G205: Prop. 4.12's proof core is closed, but the
raw-Bishop-real discharge still has two construction debts. -/
def bishopRegularSeqProp412AssumptionDischargeProgressAfterG205 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 96
  total_final_goal_percent := 96
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G205: removed the global closed-theory parameter from Prop. 4.12 and \
    exposed the remaining discharge debts explicitly. Remaining: construct \
    intrinsic measurable data from the Chapter 4.10 route, and construct local \
    representative witnesses from Bishop-real representative data. No previous \
    Prop-valued IsMeasurable/choose route is used."


end BishopCReal
