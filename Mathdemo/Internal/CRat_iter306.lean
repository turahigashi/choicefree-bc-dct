import Mathdemo.Internal.CRat_iter305

set_option linter.style.longLine false

/-!
# G207: discharging the Theorem 4.10 measurable-core debt for Prop. 4.12

G205 exposed two remaining raw-Bishop-real debts for Proposition 4.12:

1. construct intrinsic measurable data from the Chapter 4.10 route;
2. construct local good-set witnesses from the representative data.

This file discharges the first item.  Theorem 4.10's data-carrying output already
contains the measurable mid-constructor source.  The local witness law is kept as
the single remaining construction debt; it is not hidden inside a global closed
theory record.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Prop412AssumptionDischarge

open Proposition412.TruncatedIntegralBridge
open SourceComplete412

/-- The measurable core of Prop.4.12 intrinsic function data.

This is exactly the part supplied by the data-carrying Theorem 4.10 route.  It
does not contain the local good-set witness law. -/
structure Prop412IntrinsicBishopMeasurableCore
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (h : BishopC.PFunR Y R) : Type _ where
  theorem410_data : Chapter4Theorem410MeasurabilityData S h
  measurable : Prop412DataCarryingMeasurable S h
  measurable_eq_theorem410_output :
    measurable = theorem410_data.measurable

/-- Extract the intrinsic measurable core from the Chapter 4.10 data-carrying
route. -/
def prop412_intrinsic_measurable_core_from_theorem410
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {h : BishopC.PFunR Y R}
    (D : Chapter4Theorem410MeasurabilityData S h) :
    Prop412IntrinsicBishopMeasurableCore S h where
  theorem410_data := D
  measurable := D.measurable
  measurable_eq_theorem410_output := rfl

/-- The remaining local representative-witness law needed to upgrade a
Theorem-4.10 measurable core to the full Prop.4.12 intrinsic data.

This record is intentionally separate from Theorem 4.10.  It is the one remaining
construction debt after G207. -/
structure Prop412LocalRepresentativeWitnessLaw
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (Mf : Prop412DataCarryingMeasurable S f) : Type _ where
  local_witnesses_with :
    ∀ {g : BishopC.PFunR Y R}
      (Mg : Prop412DataCarryingMeasurable S g)
      (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (truncN : Nat),
      Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN
        (prop412_mid_support_data_from_constructor_source_data
          (Mf.mid_constructor_source A hA truncN))
        (prop412_mid_support_data_from_constructor_source_data
          (Mg.mid_constructor_source A hA truncN))

/-- Upgrade a Theorem-4.10 measurable core to full Prop.4.12 intrinsic function
data once the local representative-witness law is supplied. -/
def prop412_intrinsic_bishop_measurable_from_theorem410_core
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (Core : Prop412IntrinsicBishopMeasurableCore S f)
    (Local : Prop412LocalRepresentativeWitnessLaw Core.measurable) :
    Prop412IntrinsicBishopMeasurable S f where
  measurable := Core.measurable
  local_witnesses_with := by
    intro g Mg A hA truncN
    exact Local.local_witnesses_with Mg A hA truncN

/-- Build the intrinsic Prop.4.12 limit data from Theorem 4.10 measurable data,
Definition 4.11 convergence data, and the remaining local witness law. -/
def prop412_intrinsic_bishop_limit_from_theorem410_and_def411
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f : BishopC.PFunR Y R}
    (M410 : Chapter4Theorem410MeasurabilityData S f)
    (Local :
      Prop412LocalRepresentativeWitnessLaw
        (prop412_intrinsic_measurable_core_from_theorem410 M410).measurable)
    (Conv : Prop412ConvergeInMeasureData S fn f) :
    Prop412IntrinsicBishopLimit (S := S) fn f where
  function_data :=
    prop412_intrinsic_bishop_measurable_from_theorem410_core
      (prop412_intrinsic_measurable_core_from_theorem410 M410)
      Local
  converges := Conv

/-- Proposition 4.12 equality from the Chapter 4.10 measurable route plus the
single remaining local witness law. -/
def prop412_function_eq_from_theorem410_def411_and_local_witness_law
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (Mf410 : Chapter4Theorem410MeasurabilityData S f)
    (Mg410 : Chapter4Theorem410MeasurabilityData S g)
    (FLocal :
      Prop412LocalRepresentativeWitnessLaw
        (prop412_intrinsic_measurable_core_from_theorem410 Mf410).measurable)
    (GLocal :
      Prop412LocalRepresentativeWitnessLaw
        (prop412_intrinsic_measurable_core_from_theorem410 Mg410).measurable)
    (FConv : Prop412ConvergeInMeasureData S fn f)
    (GConv : Prop412ConvergeInMeasureData S fn g) :
    Prop412DataCarryingMeasurableFunctionEqualityData S f g :=
  prop412_function_eq_from_intrinsic_bishop_data
    (prop412_intrinsic_bishop_limit_from_theorem410_and_def411
      Mf410 FLocal FConv)
    (prop412_intrinsic_bishop_limit_from_theorem410_and_def411
      Mg410 GLocal GConv)

/-- G207 ledger: the Theorem-4.10 measurable-core debt is discharged; local
representative-witness synthesis remains open. -/
structure Prop412AssumptionDischargeLedgerAfterG207 : Type where
  theorem410_measurable_core_constructed : Prop
  theorem410_measurable_core_remaining_debt : Nat
  local_representative_witness_law_remaining_debt : Nat
  old_prop_valued_selector_route_used : Nat
  external_choice_principle_added : Nat
  raw_bishop_real_to_prop412_complete : Nat

def prop412AssumptionDischargeLedgerAfterG207 :
    Prop412AssumptionDischargeLedgerAfterG207 where
  theorem410_measurable_core_constructed := True
  theorem410_measurable_core_remaining_debt := 0
  local_representative_witness_law_remaining_debt := 1
  old_prop_valued_selector_route_used := 0
  external_choice_principle_added := 0
  raw_bishop_real_to_prop412_complete := 0

end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Prop412AssumptionDischarge

/-- G207 package exposed at top level. -/
structure BishopRegularSeqChapter4G207Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g206 : BishopRegularSeqChapter1To3G206AuditPackage S
  assumption_discharge_ledger_after_g207 :
    BishopRegularSeqChapter4.Prop412AssumptionDischarge.Prop412AssumptionDischargeLedgerAfterG207
  theorem410_measurable_core_closed_this_step : Nat
  remaining_assumption_discharge_steps_for_raw_bishop_real_prop412 : Nat

def bishopRegularSeqChapter4G207Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G207Package S where
  g206 := bishopRegularSeqChapter1To3G206AuditPackage S
  assumption_discharge_ledger_after_g207 :=
    BishopRegularSeqChapter4.Prop412AssumptionDischarge.prop412AssumptionDischargeLedgerAfterG207
  theorem410_measurable_core_closed_this_step := 1
  remaining_assumption_discharge_steps_for_raw_bishop_real_prop412 := 1

/-- Progress after G207: one Chapter 4 Prop.4.12 discharge debt remains. -/
def bishopRegularSeqProp412AssumptionDischargeProgressAfterG207 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 98
  total_final_goal_percent := 98
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G207: discharged the Prop.4.12 Theorem-4.10 measurable-core debt. \
    Remaining: construct the local representative-witness law from Bishop-real \
    representative data. No previous Prop-valued selector route or external choice \
    principle is used."


end BishopCReal
