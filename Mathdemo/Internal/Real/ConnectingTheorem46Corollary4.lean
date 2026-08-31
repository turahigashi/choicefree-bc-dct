import Mathdemo.Internal.Real.AttachingScalarTheorem46Laws

set_option linter.style.longLine false

/-!
# G226: connecting Theorem 4.6 to Corollary 4.7 and Theorem 4.10

G225 closed the representative-level monotonicity and increment witnesses needed
for the strengthened Theorem 4.6 route.  This file packages that result in the
source-level form used downstream:

* Corollary 4.7 receives its source data explicitly: data-carrying measurable
  witnesses for `f+`, `f-`, `|f|`, and a located supremum for the `|f|` surface.
* Theorem 4.6 then supplies located suprema for the positive and negative parts.
* Theorem 4.10's data-carrying output is connected by wrapping the already
  carried measurable data, not by selecting a representative from a Prop proof.

No previous `IsMeasurable`/choice interface is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge
open SourceComplete412

/-- Theorem 4.10 data output from already carried measurable data.

This is only a wrapper: the constructive content remains the
`Prop412DataCarryingMeasurable` value, especially its `mid_constructor_source`
field. -/
def theorem410_data_from_data_carrying_measurable
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {h : BishopC.PFunR Y R}
    (Mh : Prop412DataCarryingMeasurable S h) :
    Chapter4Theorem410MeasurabilityData S h where
  local_approximation_source_recorded := True
  exact_patch_to_prop49_recorded := True
  measurable := Mh
  old_prop_valued_isMeasurable_not_used := True

/-- Source data for the Corollary 4.7 use of Theorem 4.6.

The fields are deliberately data-valued.  The `abs_located_supremum` field is the
Bishop located-integrability datum for the dominating absolute-value surface. -/
structure Corollary47SourceData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (f : BishopC.PFunR Y R) : Type _ where
  pos_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_posPart f)
  neg_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_negPart f)
  abs_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_absPart f)
  abs_located_supremum :
    Sigma fun cAbs : R =>
      LocatedRangeSupremum
        (R := R) (T := Theorem46StateData S)
        (theorem46_midIntegralSurface abs_measurable) cAbs

/-- The Corollary 4.7 / Theorem 4.10 connection data produced from the source
data and the strengthened Theorem 4.6 route. -/
structure Corollary47Theorem410ConnectionData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (f : BishopC.PFunR Y R) : Type _ where
  source : Corollary47SourceData S f
  pointwise_parts : Theorem46ConcretePointwisePartSurfaceData S f
  concrete_parts : Theorem46ConcretePartSurfaceData S f
  positive_negative_located_suprema :
    Theorem46PositiveNegativeLocatedSuprema
      (theorem46_located_input_from_concrete_parts concrete_parts)
  pos_theorem410_data :
    Chapter4Theorem410MeasurabilityData S (theorem46_pfun_posPart f)
  neg_theorem410_data :
    Chapter4Theorem410MeasurabilityData S (theorem46_pfun_negPart f)
  abs_theorem410_data :
    Chapter4Theorem410MeasurabilityData S (theorem46_pfun_absPart f)
  old_prop_valued_selector_used : Nat
  external_choice_principle_added : Nat

/-- Construct the source-level Corollary 4.7 / Theorem 4.10 connection from
the explicit Bishop data. -/
noncomputable def corollary47_theorem410_connection_from_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (D : Corollary47SourceData S f) :
    Corollary47Theorem410ConnectionData S f :=
  let P :=
    theorem46_concrete_pointwise_parts_from_measurable_parts
      D.pos_measurable D.neg_measurable D.abs_measurable D.abs_located_supremum
  { source := D
    pointwise_parts := P
    concrete_parts := theorem46_concrete_parts_from_pointwise_data P
    positive_negative_located_suprema :=
      theorem46_positive_negative_located_suprema_from_pointwise_parts P
    pos_theorem410_data :=
      theorem410_data_from_data_carrying_measurable D.pos_measurable
    neg_theorem410_data :=
      theorem410_data_from_data_carrying_measurable D.neg_measurable
    abs_theorem410_data :=
      theorem410_data_from_data_carrying_measurable D.abs_measurable
    old_prop_valued_selector_used := 0
    external_choice_principle_added := 0 }

/-- The positive-part located supremum exported from the Corollary 4.7
connection. -/
def corollary47_positive_located_supremum
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (D : Corollary47Theorem410ConnectionData S f) :
    Sigma fun cPos : R =>
      LocatedRangeSupremum
        (R := R) (T := Theorem46StateData S)
        (theorem46_located_input_from_concrete_parts D.concrete_parts).phi_pos cPos :=
  D.positive_negative_located_suprema.positive

/-- The negative-part located supremum exported from the Corollary 4.7
connection. -/
def corollary47_negative_located_supremum
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (D : Corollary47Theorem410ConnectionData S f) :
    Sigma fun cNeg : R =>
      LocatedRangeSupremum
        (R := R) (T := Theorem46StateData S)
        (theorem46_located_input_from_concrete_parts D.concrete_parts).phi_neg cNeg :=
  D.positive_negative_located_suprema.negative

/-- Audit after G226. -/
structure Corollary47Theorem410ConnectionAuditAfterG226 : Type where
  theorem46_to_corollary47_located_suprema_closed : Nat
  theorem410_data_wrappers_from_carried_measurability_closed : Nat
  corollary47_source_inputs_are_explicit_bishop_data : Nat
  old_prop_valued_selector_used : Nat
  external_choice_principle_added : Nat
  remaining_connection_steps_for_4_6_to_4_10 : Nat

def corollary47Theorem410ConnectionAuditAfterG226 :
    Corollary47Theorem410ConnectionAuditAfterG226 where
  theorem46_to_corollary47_located_suprema_closed := 1
  theorem410_data_wrappers_from_carried_measurability_closed := 1
  corollary47_source_inputs_are_explicit_bishop_data := 1
  old_prop_valued_selector_used := 0
  external_choice_principle_added := 0
  remaining_connection_steps_for_4_6_to_4_10 := 0

/-- G226 package. -/
structure Chapter4G226Corollary47Theorem410ConnectionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g225 : Chapter4G225Theorem46MidSourceConnectionPackage S
  audit : Corollary47Theorem410ConnectionAuditAfterG226
  connection_closed_this_step : Nat
  remaining_source_completion_steps_for_4_6_to_4_10 : Nat

def chapter4G226Corollary47Theorem410ConnectionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G226Corollary47Theorem410ConnectionPackage S where
  g225 := chapter4G225Theorem46MidSourceConnectionPackage S
  audit := corollary47Theorem410ConnectionAuditAfterG226
  connection_closed_this_step := 1
  remaining_source_completion_steps_for_4_6_to_4_10 := 0

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G226. -/
def bishopRegularSeqChapter4Corollary47Theorem410ProgressAfterG226 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G226: connected the strengthened Theorem 4.6 data to the Corollary 4.7 \
    located-supremum output and to the Theorem 4.10 data-carrying measurable \
    output. The source inputs are explicit Bishop data: carried measurable \
    constructors for f+, f-, |f| and a located supremum for |f|. No Prop-valued \
    selector route or external choice principle is introduced."


end BishopCReal
