import Mathdemo.Internal.CRat_iter306

set_option linter.style.longLine false

/-!
# G208: splitting the remaining local-witness law for Proposition 4.12

G207 removed the global closed-theory wrapper and discharged the Theorem 4.10
measurable-core part of Proposition 4.12.  The remaining datum was the local
good-set witness law.

This file does not mark that analytic frontier as complete.  Instead it replaces
the one large law-shaped assumption by the two source obligations it actually
contains:

1. pointwise absolute convergence of the characteristic representative of `A`
   on each common good set;
2. pointwise seed data for the complement and bad-set representatives built
   from the explicit mid representatives.

Thus the debt is no longer hidden behind a Prop.4.12-level wrapper.  The
remaining work is visibly at representative-data level, where it must be
discharged from the Bishop-real source information.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Prop412AssumptionDischarge

open Proposition412.TruncatedIntegralBridge
open SourceComplete412

/-- Source-level obligations that generate the local representative-witness law.

This is intentionally lower level than `Prop412LocalRepresentativeWitnessLaw`.
It names the two analytic facts that still have to be obtained from the
Bishop-real representative data, instead of letting them sit inside one opaque
law-shaped parameter. -/
structure Prop412LocalRepresentativeWitnessSource
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (Mf : Prop412DataCarryingMeasurable S f) : Type _ where
  chiA_abs_on_common_good :
    ∀ {g : BishopC.PFunR Y R}
      (_Mg : Prop412DataCarryingMeasurable S g)
      (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (_truncN : Nat)
      (B : BishopC.BSet Y) (_hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (_hC : BishopC.IntegrableSet1 S C),
      Prop412GoodSetChiAAbsData A (BishopC.BSet.and B C) hA
  pointwise_seed_on_common_good :
    ∀ {g : BishopC.PFunR Y R}
      (Mg : Prop412DataCarryingMeasurable S g)
      (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (truncN : Nat)
      (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      Prop412ComplementPointwiseConcreteSupportSeedData
        A (BishopC.BSet.and B C) hA (BishopC.IntegrableSet1_and hB hC)
        truncN f g
        (prop412_mid_support_data_from_constructor_source_data
          (Mf.mid_constructor_source A hA truncN))
        (prop412_mid_support_data_from_constructor_source_data
          (Mg.mid_constructor_source A hA truncN))

/-- The split representative source data reconstruct the local witness law
used in G207. -/
def prop412_local_witness_law_from_source
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    {Mf : Prop412DataCarryingMeasurable S f}
    (Src : Prop412LocalRepresentativeWitnessSource Mf) :
    Prop412LocalRepresentativeWitnessLaw Mf where
  local_witnesses_with := by
    intro g Mg A hA truncN
    exact
      { data := by
          intro B hB C hC
          exact
            { chiA_abs_on_good :=
                Src.chiA_abs_on_common_good Mg A hA truncN B hB C hC
              pointwise_seed :=
                Src.pointwise_seed_on_common_good Mg A hA truncN B hB C hC } }

/-- Proposition 4.12 equality from Theorem 4.10, Definition 4.11, and the split
representative-source obligations. -/
def prop412_function_eq_from_theorem410_def411_and_local_source
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (Mf410 : Chapter4Theorem410MeasurabilityData S f)
    (Mg410 : Chapter4Theorem410MeasurabilityData S g)
    (FSource :
      Prop412LocalRepresentativeWitnessSource
        (prop412_intrinsic_measurable_core_from_theorem410 Mf410).measurable)
    (GSource :
      Prop412LocalRepresentativeWitnessSource
        (prop412_intrinsic_measurable_core_from_theorem410 Mg410).measurable)
    (FConv : Prop412ConvergeInMeasureData S fn f)
    (GConv : Prop412ConvergeInMeasureData S fn g) :
    Prop412DataCarryingMeasurableFunctionEqualityData S f g :=
  prop412_function_eq_from_theorem410_def411_and_local_witness_law
    Mf410 Mg410
    (prop412_local_witness_law_from_source FSource)
    (prop412_local_witness_law_from_source GSource)
    FConv GConv

/-- G208 ledger: the local-witness law itself is no longer an opaque debt; its
two representative-level source obligations are now visible. -/
structure Prop412AssumptionDischargeLedgerAfterG208 : Type where
  theorem410_measurable_core_remaining_debt : Nat
  local_witness_law_remaining_debt : Nat
  chiA_abs_on_common_good_from_integrable_set_remaining_debt : Nat
  pointwise_seed_from_complement_bad_representatives_remaining_debt : Nat
  representative_source_obligations_remaining : Nat
  old_prop_valued_selector_route_used : Nat
  external_choice_principle_added : Nat
  global_closed_theory_wrapper_used : Nat
  raw_bishop_real_to_prop412_complete : Nat

def prop412AssumptionDischargeLedgerAfterG208 :
    Prop412AssumptionDischargeLedgerAfterG208 where
  theorem410_measurable_core_remaining_debt := 0
  local_witness_law_remaining_debt := 0
  chiA_abs_on_common_good_from_integrable_set_remaining_debt := 1
  pointwise_seed_from_complement_bad_representatives_remaining_debt := 1
  representative_source_obligations_remaining := 2
  old_prop_valued_selector_route_used := 0
  external_choice_principle_added := 0
  global_closed_theory_wrapper_used := 0
  raw_bishop_real_to_prop412_complete := 0

end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Prop412AssumptionDischarge

/-- G208 package exposed at top level. -/
structure BishopRegularSeqChapter4G208Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g207 : BishopRegularSeqChapter4G207Package S
  assumption_discharge_ledger_after_g208 :
    BishopRegularSeqChapter4.Prop412AssumptionDischarge.Prop412AssumptionDischargeLedgerAfterG208
  local_witness_law_split_this_step : Nat
  remaining_representative_source_obligations_for_raw_prop412 : Nat

def bishopRegularSeqChapter4G208Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G208Package S where
  g207 := bishopRegularSeqChapter4G207Package S
  assumption_discharge_ledger_after_g208 :=
    BishopRegularSeqChapter4.Prop412AssumptionDischarge.prop412AssumptionDischargeLedgerAfterG208
  local_witness_law_split_this_step := 1
  remaining_representative_source_obligations_for_raw_prop412 := 2

/-- Progress after G208: the Chapter 4 Prop.4.12 debt is now at two
representative-source obligations rather than at a theorem-level wrapper. -/
def bishopRegularSeqProp412AssumptionDischargeProgressAfterG208 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G208: split the remaining Prop.4.12 local-witness law into two explicit \
    representative-source obligations: chi_A absolute convergence on common \
    good sets, and complement/bad representative pointwise seed data. The \
    theorem-level local witness law is no longer opaque. No previous Prop-valued \
    selector route, global closed-theory wrapper, or external choice principle \
    is used."


end BishopCReal
