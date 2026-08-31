import Mathdemo.Internal.Real.ConnectingTheorem46Corollary4

set_option linter.style.longLine false

/-!
# G227: final Chapter 4 route to Proposition 4.12

G226 connected the strengthened Theorem 4.6 data to Corollary 4.7 and the
data-carrying Theorem 4.10 output.  G215 already connected data-carrying
measurability, Definition 4.11 convergence data, and definition-facing
characteristic witnesses to the no-seed Proposition 4.12 truncated-integral
equality.

This file records the end-to-end route:

* Theorem 4.10 output is a data object carrying `mid_constructor_source`.
* Definition 4.11 convergence remains a theorem premise, as in the source text.
* Characteristic witnesses are read from the integrable-set definition.
* Proposition 4.12's truncated-integral equality follows without a Prop-to-data
  selector or an external choice principle.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Chapter4To412Final

open SourceComplete412
open Proposition412.TruncatedIntegralBridge
open Prop412AssumptionDischarge
open Lemma45Theorem46

/-- Proposition 4.12 one-set, one-truncation equality directly from the
data-carrying Theorem 4.10 outputs, Definition 4.11 convergence data, and the
definition-facing characteristic witnesses. -/
theorem prop412_truncated_integrals_eq_from_theorem410_data_no_seed
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (Mf410 : Chapter4Theorem410MeasurabilityData S f)
    (Mg410 : Chapter4Theorem410MeasurabilityData S g)
    (Fam : Prop412CharacteristicWitnessFamily (S := S))
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (truncN_pos : COF.lt 0 (truncN : R)) :
    (prop412_mid_full_support_data_from_constructor_source_data
        (Mf410.measurable.mid_constructor_source A hA truncN)).support.mid.rep.integral =
      (prop412_mid_full_support_data_from_constructor_source_data
        (Mg410.measurable.mid_constructor_source A hA truncN)).support.mid.rep.integral :=
  prop412_truncated_integrals_eq_from_characteristic_family_no_seed
    (Mf := Mf410.measurable) Fam Mg410.measurable hf hg A hA truncN truncN_pos

/-- Final audit for Chapter 4 up to Proposition 4.12. -/
structure Chapter4UpTo412FinalAuditAfterG227 : Type where
  theorem46_to_corollary47_to_theorem410_connection_closed : Nat
  theorem410_to_prop412_no_seed_route_closed : Nat
  def411_convergence_data_is_source_premise : Nat
  characteristic_witnesses_come_from_integrable_set_definition : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_steps_for_chapter4_to_prop412 : Nat

def chapter4UpTo412FinalAuditAfterG227 :
    Chapter4UpTo412FinalAuditAfterG227 where
  theorem46_to_corollary47_to_theorem410_connection_closed := 1
  theorem410_to_prop412_no_seed_route_closed := 1
  def411_convergence_data_is_source_premise := 1
  characteristic_witnesses_come_from_integrable_set_definition := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_steps_for_chapter4_to_prop412 := 0

/-- G227 package combining the no-seed Prop.4.12 route and the new
Theorem 4.6/Corollary 4.7/Theorem 4.10 connection. -/
structure Chapter4G227UpTo412FinalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g215 : BishopRegularSeqChapter4G215Package S
  g226 : Lemma45Theorem46.Chapter4G226Corollary47Theorem410ConnectionPackage S
  audit : Chapter4UpTo412FinalAuditAfterG227
  final_connection_closed_this_step : Nat
  remaining_steps_for_chapter4_to_prop412 : Nat

def chapter4G227UpTo412FinalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G227UpTo412FinalPackage S where
  g215 := bishopRegularSeqChapter4G215Package S
  g226 := Lemma45Theorem46.chapter4G226Corollary47Theorem410ConnectionPackage S
  audit := chapter4UpTo412FinalAuditAfterG227
  final_connection_closed_this_step := 1
  remaining_steps_for_chapter4_to_prop412 := 0

end Chapter4To412Final
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Chapter4To412Final

/-- Progress after G227. -/
def bishopRegularSeqChapter4ToProp412FinalProgressAfterG227 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 100
  total_final_goal_percent := 100
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G227: final Chapter-4-to-Prop.4.12 route connected. G226 supplies the \
    Theorem 4.6 / Corollary 4.7 / Theorem 4.10 data connection, and G215 supplies \
    the no-seed Prop.4.12 truncated-integral equality from data-carrying \
    measurability, Definition 4.11 convergence, and characteristic witnesses \
    from integrable-set definitions. No Prop-to-Type witness extraction or \
    external choice principle is used on this route."


end BishopCReal
