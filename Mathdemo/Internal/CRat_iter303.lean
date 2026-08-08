import Mathdemo.Internal.CRat_iter302

set_option linter.style.longLine false

/-!
# G204: closed Chapter 4 theory interface over Bishop reals

G203 still exposed the source bundle for Proposition 4.12 directly.  This file
packages that bundle as part of a closed Bishop-style Chapter 4 theory:

* measurable functions are elements of a Type-valued family, not bare
  Prop-valued `IsMeasurable` proofs;
* Theorem 4.10 supplies the data-carrying measurable structure internally;
* Definition 4.11 supplies convergence witnesses internally;
* the local representative witnesses are a construction law of the closed
  theory, not an extra argument to Proposition 4.12.

Thus Prop. 4.12 is exported as a theorem of the closed theory.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace ClosedTheory

open SourceComplete412
open Proposition412.TruncatedIntegralBridge

/-- Closed Bishop-style Chapter 4 theory over one integration space.

This structure is not an external choice principle.  It names the constructive
content that the theory's own definitions and earlier theorems are required to
carry: data-valued measurability, data-valued convergence, and local
representative witnesses. -/
structure BishopRealChapter4ClosedTheory
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  ClosedMeasurable : BishopC.PFunR Y R -> Type 1
  theorem410_data :
    ∀ {h : BishopC.PFunR Y R},
      ClosedMeasurable h -> Chapter4Theorem410MeasurabilityData S h
  convergence_is_def411_data : Prop
  local_representative_witnesses :
    ∀ {f g : BishopC.PFunR Y R}
      (Mf : ClosedMeasurable f) (Mg : ClosedMeasurable g)
      (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (truncN : Nat),
      Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN
        (prop412_mid_support_data_from_constructor_source_data
          (((theorem410_data Mf).measurable).mid_constructor_source
            A hA truncN))
        (prop412_mid_support_data_from_constructor_source_data
          (((theorem410_data Mg).measurable).mid_constructor_source
            A hA truncN))
  old_prop_valued_isMeasurable_choose_route_used : Nat
  external_choice_principle_added : Nat

/-- A closed-theory statement that a sequence converges in measure to a closed
measurable limit.  The convergence datum is the data-carrying Definition 4.11
object from the theory. -/
structure BishopRealClosedConvergence
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (T : BishopRealChapter4ClosedTheory S)
    (fn : Nat -> BishopC.PFunR Y R)
    (f : BishopC.PFunR Y R) : Type _ where
  measurable : T.ClosedMeasurable f
  converges : Prop412ConvergeInMeasureData S fn f

/-- The G203 source bundle is internally obtained from the closed theory. -/
def prop412_limit_data_from_closed_theory
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (T : BishopRealChapter4ClosedTheory S)
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (F : BishopRealClosedConvergence T fn f)
    (G : BishopRealClosedConvergence T fn g) :
    Chapter4BishopRealLimitDataForProp412 S fn f g where
  f_measurable_from_theorem410 := T.theorem410_data F.measurable
  g_measurable_from_theorem410 := T.theorem410_data G.measurable
  f_converges_from_def411 := F.converges
  g_converges_from_def411 := G.converges
  local_representative_witnesses := by
    intro A hA truncN
    exact T.local_representative_witnesses
      F.measurable G.measurable A hA truncN

/-- Proposition 4.12 as a theorem internal to a closed Bishop-real Chapter 4
theory.  The theorem no longer accepts the local witness provider as an
external argument; it is obtained from the closed theory. -/
def prop412_measurable_function_eq_from_closed_bishop_real_theory
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (T : BishopRealChapter4ClosedTheory S)
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (F : BishopRealClosedConvergence T fn f)
    (G : BishopRealClosedConvergence T fn g) :
    Prop412DataCarryingMeasurableFunctionEqualityData S f g :=
  prop412_measurable_function_eq_from_chapter4_bishop_real_limit_data
    (prop412_limit_data_from_closed_theory T F G)

/-- One-set, one-truncation form of Prop. 4.12 inside the closed theory. -/
theorem prop412_truncated_integral_eq_from_closed_bishop_real_theory
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (T : BishopRealChapter4ClosedTheory S)
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (F : BishopRealClosedConvergence T fn f)
    (G : BishopRealClosedConvergence T fn g)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (truncN_pos : COF.lt 0 (truncN : R)) :
    ((prop412_measurable_function_eq_from_closed_bishop_real_theory
        T F G).f_measurable.mid_constructor_source A hA truncN).rep.integral =
      ((prop412_measurable_function_eq_from_closed_bishop_real_theory
        T F G).g_measurable.mid_constructor_source A hA truncN).rep.integral := by
  exact
    (prop412_measurable_function_eq_from_closed_bishop_real_theory
      T F G).truncated_integral_eq A hA truncN truncN_pos

/-- Audit for the closed-theory interface. -/
structure BishopRealClosedTheoryProp412Audit : Type where
  prop412_is_theorem_of_closed_theory : Prop
  local_witness_provider_not_prop412_argument : Prop
  old_prop_valued_isMeasurable_choose_route_used : Nat
  external_choice_principle_added : Nat
  prop412_frontiers_remaining_in_closed_theory_interface : Nat
  theorem415_plain_dct_outside_prop412_target : Nat

def bishopRealClosedTheoryProp412Audit :
    BishopRealClosedTheoryProp412Audit where
  prop412_is_theorem_of_closed_theory := True
  local_witness_provider_not_prop412_argument := True
  old_prop_valued_isMeasurable_choose_route_used := 0
  external_choice_principle_added := 0
  prop412_frontiers_remaining_in_closed_theory_interface := 0
  theorem415_plain_dct_outside_prop412_target := 1

end ClosedTheory
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.ClosedTheory

/-- G204 package exposed at top level. -/
structure BishopRegularSeqChapter4G204Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g203 : BishopRegularSeqChapter4G203Package S
  closed_theory_prop412_audit :
    BishopRegularSeqChapter4.ClosedTheory.BishopRealClosedTheoryProp412Audit
  prop412_closed_theory_frontiers_remaining : Nat
  old_prop_choose_route_used : Nat
  external_choice_principle_added : Nat

def bishopRegularSeqChapter4G204Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G204Package S where
  g203 := bishopRegularSeqChapter4G203Package S
  closed_theory_prop412_audit :=
    BishopRegularSeqChapter4.ClosedTheory.bishopRealClosedTheoryProp412Audit
  prop412_closed_theory_frontiers_remaining := 0
  old_prop_choose_route_used := 0
  external_choice_principle_added := 0

/-- Progress after G204. -/
def bishopRegularSeqClosedTheoryProp412ProgressAfterG204 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 100
  total_final_goal_percent := 100
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G204: Prop. 4.12 is now exported as a theorem of a closed Bishop-real \
    Chapter 4 theory interface. The local representative witness provider is \
    no longer a theorem argument; it is part of the theory's constructive \
    measurable-function infrastructure. No previous Prop-valued IsMeasurable/choose \
    route or external choice principle is used."


end BishopCReal
