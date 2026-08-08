import Mathdemo.Internal.CRat_iter319

set_option linter.style.longLine false

/-!
# G221: lifting local pointwise mid inequalities to Theorem 4.6 domination

G220 isolated the remaining Theorem 4.6 work as two-step domination data for
the concrete `f+`, `f-`, and `|f|` truncation-integral surfaces.

This increment pushes that obligation down one more Bishop-faithful layer:
instead of assuming the integral domination directly, it is enough to carry
the local pointwise inequalities for the concrete mid representatives.  The
integral statements are then obtained by Proposition 1.11 on a full set built
from the four carried representative domains.

Thus the remaining obligation is now the scalar/set calculation in the
representative values themselves, not any Prop-to-data extraction or
order-theoretic choice.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge

/-- The carried mid constructor source attached to a Theorem 4.6 state. -/
def theorem46_mid_source
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {h : BishopC.PFunR Y R}
    (Mh : Prop412DataCarryingMeasurable S h)
    (s : Theorem46StateData S) :
    Prop412MidRepresentativeConstructorSourceData s.A s.hA s.n h :=
  Mh.mid_constructor_source s.A s.hA s.n

/-- Full set carrying all four Definition-1.6 domains needed for one local
Theorem 4.6 comparison step. -/
noncomputable def theorem46_pointwise_oneStep_fullSet
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (u t : Theorem46StateData S) : Set Y :=
  ((((theorem46_mid_source Mφ t).rep.domain ∩
        (theorem46_mid_source Mφ u).rep.domain) ∩
      (theorem46_mid_source Mψ t).rep.domain) ∩
    (theorem46_mid_source Mψ u).rep.domain)

/-- The one-step full set is full because it is a finite intersection of
carried integrable-representative domains. -/
theorem theorem46_pointwise_oneStep_fullSet_isFull
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (u t : Theorem46StateData S) :
    BishopC.IsFull S
      (theorem46_pointwise_oneStep_fullSet Mφ Mψ u t) := by
  unfold theorem46_pointwise_oneStep_fullSet
  exact BishopC.isFull_inter
    (BishopC.isFull_inter
      (BishopC.isFull_inter
        (theorem46_mid_source Mφ t).rep.domain_isFull
        (theorem46_mid_source Mφ u).rep.domain_isFull)
      (theorem46_mid_source Mψ t).rep.domain_isFull)
    (theorem46_mid_source Mψ u).rep.domain_isFull

/-- Pointwise local data for one source step `t -> u`.

The two fields are exactly what Proposition 1.11 needs:

* monotonicity of the `φ` mid representative;
* domination of the `φ` increment by the corresponding `ψ` increment.

The data is expressed in terms of the actual carried representative values, so
no quotient representative is selected after the fact. -/
structure Theorem46MidPointwiseOneStepData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (u t : Theorem46StateData S) : Type _ where
  support : Set Y
  support_isFull : BishopC.IsFull S support
  support_subset_mid_domains :
    support ⊆ theorem46_pointwise_oneStep_fullSet Mφ Mψ u t
  monotone :
    ∀ x
      (hx : x ∈ support)
      (hφt : RSeq.SeriesSum
        (fun m => ((theorem46_mid_source Mφ t).rep.fn m).toFun x))
      (hφu : RSeq.SeriesSum
        (fun m => ((theorem46_mid_source Mφ u).rep.fn m).toFun x))
      (_hψt : RSeq.SeriesSum
        (fun m => ((theorem46_mid_source Mψ t).rep.fn m).toFun x))
      (_hψu : RSeq.SeriesSum
        (fun m => ((theorem46_mid_source Mψ u).rep.fn m).toFun x)),
      BishopC.Le hφt.sum hφu.sum
  increment_bound :
    ∀ x
      (hx : x ∈ support)
      (hφt : RSeq.SeriesSum
        (fun m => ((theorem46_mid_source Mφ t).rep.fn m).toFun x))
      (hφu : RSeq.SeriesSum
        (fun m => ((theorem46_mid_source Mφ u).rep.fn m).toFun x))
      (hψt : RSeq.SeriesSum
        (fun m => ((theorem46_mid_source Mψ t).rep.fn m).toFun x))
      (hψu : RSeq.SeriesSum
        (fun m => ((theorem46_mid_source Mψ u).rep.fn m).toFun x)),
      BishopC.Le (hφu.sum - hφt.sum) (hψu.sum - hψt.sum)

/-- Pointwise monotonicity lifts to monotonicity of the carried mid integrals. -/
theorem theorem46_mid_integral_mono_from_pointwise_one_step_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    {Mφ : Prop412DataCarryingMeasurable S φh}
    {Mψ : Prop412DataCarryingMeasurable S ψh}
    {u t : Theorem46StateData S}
    (D : Theorem46MidPointwiseOneStepData Mφ Mψ u t) :
    BishopC.Le
      (theorem46_midIntegralSurface Mφ t)
      (theorem46_midIntegralSurface Mφ u) := by
  change BishopC.Le
      (theorem46_mid_source Mφ t).rep.integral
    (theorem46_mid_source Mφ u).rep.integral
  refine BishopC.prop_1_11
    D.support_isFull
    (theorem46_mid_source Mφ t).rep
    (theorem46_mid_source Mφ u).rep
    ?_
  intro x hx hφt hφu
  have hxMid := D.support_subset_mid_domains hx
  unfold theorem46_pointwise_oneStep_fullSet at hxMid
  obtain ⟨hx123, hxψu⟩ := hxMid
  obtain ⟨_, hxψt⟩ := hx123
  obtain ⟨_, ⟨hψt_abs⟩⟩ := hxψt
  obtain ⟨_, ⟨hψu_abs⟩⟩ := hxψu
  let hψt := BishopC.seriesSum_of_abs hψt_abs
  let hψu := BishopC.seriesSum_of_abs hψu_abs
  exact D.monotone x hx hφt hφu hψt hψu

/-- Pointwise domination of increments lifts to domination of integral
increments. -/
theorem theorem46_mid_integral_increment_bound_from_pointwise_one_step_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    {Mφ : Prop412DataCarryingMeasurable S φh}
    {Mψ : Prop412DataCarryingMeasurable S ψh}
    {u t : Theorem46StateData S}
    (D : Theorem46MidPointwiseOneStepData Mφ Mψ u t) :
    BishopC.Le
      (theorem46_midIntegralSurface Mφ u -
        theorem46_midIntegralSurface Mφ t)
      (theorem46_midIntegralSurface Mψ u -
        theorem46_midIntegralSurface Mψ t) := by
  change BishopC.Le
    ((theorem46_mid_source Mφ u).rep.integral -
      (theorem46_mid_source Mφ t).rep.integral)
    ((theorem46_mid_source Mψ u).rep.integral -
      (theorem46_mid_source Mψ t).rep.integral)
  have hleAdd :
      BishopC.Le
        (((theorem46_mid_source Mφ u).rep.add
          (theorem46_mid_source Mψ t).rep).integral)
        (((theorem46_mid_source Mψ u).rep.add
          (theorem46_mid_source Mφ t).rep).integral) := by
    refine BishopC.prop_1_11
      D.support_isFull
      ((theorem46_mid_source Mφ u).rep.add
        (theorem46_mid_source Mψ t).rep)
      ((theorem46_mid_source Mψ u).rep.add
        (theorem46_mid_source Mφ t).rep)
      ?_
    intro x hx hleft hright
    have hxMid := D.support_subset_mid_domains hx
    unfold theorem46_pointwise_oneStep_fullSet at hxMid
    obtain ⟨hx123, hxψu⟩ := hxMid
    obtain ⟨hx12, hxψt⟩ := hx123
    obtain ⟨hxφt, hxφu⟩ := hx12
    obtain ⟨_, ⟨hφt_abs⟩⟩ := hxφt
    obtain ⟨_, ⟨hφu_abs⟩⟩ := hxφu
    obtain ⟨_, ⟨hψt_abs⟩⟩ := hxψt
    obtain ⟨_, ⟨hψu_abs⟩⟩ := hxψu
    let hφt := BishopC.seriesSum_of_abs hφt_abs
    let hφu := BishopC.seriesSum_of_abs hφu_abs
    let hψt := BishopC.seriesSum_of_abs hψt_abs
    let hψu := BishopC.seriesSum_of_abs hψu_abs
    have hleft_eq :
        hleft.sum = hφu.sum + hψt.sum := by
      exact BishopC.seriesSum_unique hleft
        (BishopC.add_seriesSum_value hφu hψt)
    have hright_eq :
        hright.sum = hψu.sum + hφt.sum := by
      exact BishopC.seriesSum_unique hright
        (BishopC.add_seriesSum_value hψu hφt)
    rw [hleft_eq, hright_eq]
    have hdelta := D.increment_bound x hx hφt hφu hψt hψu
    exact BishopC.le_of_nonneg_sub (by
      rw [show (hψu.sum + hφt.sum) - (hφu.sum + hψt.sum)
          = (hψu.sum - hψt.sum) - (hφu.sum - hφt.sum) by ring]
      exact BishopC.nonneg_sub_of_le hdelta)
  rw [BishopC.IntegrableRep.integral_add,
    BishopC.IntegrableRep.integral_add] at hleAdd
  exact BishopC.le_of_nonneg_sub (by
    rw [show
        ((theorem46_mid_source Mψ u).rep.integral -
            (theorem46_mid_source Mψ t).rep.integral) -
          ((theorem46_mid_source Mφ u).rep.integral -
            (theorem46_mid_source Mφ t).rep.integral)
        =
        ((theorem46_mid_source Mψ u).rep.integral +
            (theorem46_mid_source Mφ t).rep.integral) -
          ((theorem46_mid_source Mφ u).rep.integral +
            (theorem46_mid_source Mψ t).rep.integral) by ring]
    exact BishopC.nonneg_sub_of_le hleAdd)

/-- One local pointwise step supplies the one-step domination used in G220. -/
theorem theorem46_oneStepDomination_from_mid_pointwise_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    {Mφ : Prop412DataCarryingMeasurable S φh}
    {Mψ : Prop412DataCarryingMeasurable S ψh}
    {u t : Theorem46StateData S}
    (D : Theorem46MidPointwiseOneStepData Mφ Mψ u t) :
    Theorem46OneStepDomination
      (theorem46_midIntegralSurface Mφ)
      (theorem46_midIntegralSurface Mψ)
      u t := by
  constructor
  · exact BishopC.nonneg_sub_of_le
      (theorem46_mid_integral_mono_from_pointwise_one_step_data D)
  · exact theorem46_mid_integral_increment_bound_from_pointwise_one_step_data D

/-- Pointwise source data for all four local steps in the Theorem 4.6 proof. -/
structure Theorem46MidPointwiseTwoStepDominationData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh) : Type _ where
  left_set_step :
    ∀ s1 s2 : Theorem46StateData S,
      Theorem46MidPointwiseOneStepData Mφ Mψ
        (theorem46_stateData_or_leftN s1 s2) s1
  left_truncation_step :
    ∀ s1 s2 : Theorem46StateData S,
      Theorem46MidPointwiseOneStepData Mφ Mψ
        (theorem46_stateData_s3 s1 s2)
        (theorem46_stateData_or_leftN s1 s2)
  right_set_step :
    ∀ s1 s2 : Theorem46StateData S,
      Theorem46MidPointwiseOneStepData Mφ Mψ
        (theorem46_stateData_or_rightN s1 s2) s2
  right_truncation_step :
    ∀ s1 s2 : Theorem46StateData S,
      Theorem46MidPointwiseOneStepData Mφ Mψ
        (theorem46_stateData_s3 s1 s2)
        (theorem46_stateData_or_rightN s1 s2)

/-- The pointwise two-step data derives the integral two-step domination data
used by the located Theorem 4.6 transfer. -/
def theorem46_twoStepDomination_from_mid_pointwise_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    {Mφ : Prop412DataCarryingMeasurable S φh}
    {Mψ : Prop412DataCarryingMeasurable S ψh}
    (D : Theorem46MidPointwiseTwoStepDominationData Mφ Mψ) :
    Theorem46TwoStepDominationData
      (theorem46_midIntegralSurface Mφ)
      (theorem46_midIntegralSurface Mψ) where
  left_set_step := fun s1 s2 =>
    theorem46_oneStepDomination_from_mid_pointwise_data
      (D.left_set_step s1 s2)
  left_truncation_step := fun s1 s2 =>
    theorem46_oneStepDomination_from_mid_pointwise_data
      (D.left_truncation_step s1 s2)
  right_set_step := fun s1 s2 =>
    theorem46_oneStepDomination_from_mid_pointwise_data
      (D.right_set_step s1 s2)
  right_truncation_step := fun s1 s2 =>
    theorem46_oneStepDomination_from_mid_pointwise_data
      (D.right_truncation_step s1 s2)

/-- Concrete part-surface data where the two-step domination is supplied only
at the pointwise representative-value level. -/
structure Theorem46ConcretePointwisePartSurfaceData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (f : BishopC.PFunR Y R) : Type _ where
  pos_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_posPart f)
  neg_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_negPart f)
  abs_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_absPart f)
  positive_pointwise_two_step_domination :
    Theorem46MidPointwiseTwoStepDominationData pos_measurable abs_measurable
  negative_pointwise_two_step_domination :
    Theorem46MidPointwiseTwoStepDominationData neg_measurable abs_measurable
  abs_located_supremum :
    Sigma fun cAbs : R =>
      LocatedRangeSupremum
        (R := R) (T := Theorem46StateData S)
        (theorem46_midIntegralSurface abs_measurable) cAbs

/-- Convert pointwise representative-level concrete data into the G220 concrete
surface package. -/
def theorem46_concrete_parts_from_pointwise_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (D : Theorem46ConcretePointwisePartSurfaceData S f) :
    Theorem46ConcretePartSurfaceData S f where
  pos_measurable := D.pos_measurable
  neg_measurable := D.neg_measurable
  abs_measurable := D.abs_measurable
  positive_two_step_domination :=
    theorem46_twoStepDomination_from_mid_pointwise_data
      D.positive_pointwise_two_step_domination
  negative_two_step_domination :=
    theorem46_twoStepDomination_from_mid_pointwise_data
      D.negative_pointwise_two_step_domination
  abs_located_supremum := D.abs_located_supremum

/-- Source-facing Theorem 4.6 supremum step from pointwise local data. -/
noncomputable def theorem46_positive_negative_located_suprema_from_pointwise_parts
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (D : Theorem46ConcretePointwisePartSurfaceData S f) :
    Theorem46PositiveNegativeLocatedSuprema
      (theorem46_located_input_from_concrete_parts
        (theorem46_concrete_parts_from_pointwise_data D)) :=
  theorem46_positive_negative_located_suprema_from_concrete_parts
    (theorem46_concrete_parts_from_pointwise_data D)

/-- Audit after G221. -/
structure Theorem46PointwiseLiftAuditAfterG221 : Type where
  one_step_full_set_built_from_carried_rep_domains : Nat
  pointwise_to_integral_monotonicity_by_prop111 : Nat
  pointwise_increment_bound_to_integral_increment_bound_by_prop111 : Nat
  integral_two_step_domination_derived_from_pointwise_data : Nat
  concrete_theorem46_route_accepts_pointwise_data : Nat
  prop_to_data_selector_inputs_added : Nat
  rangeSupremum_to_locatedSupremum_selector_used : Nat
  classical_choice_inputs_added : Nat
  remaining_scalar_set_pointwise_laws_for_fpos_fneg_abs : Nat
  remaining_corollary47_connection_steps : Nat

def theorem46PointwiseLiftAuditAfterG221 :
    Theorem46PointwiseLiftAuditAfterG221 where
  one_step_full_set_built_from_carried_rep_domains := 1
  pointwise_to_integral_monotonicity_by_prop111 := 1
  pointwise_increment_bound_to_integral_increment_bound_by_prop111 := 1
  integral_two_step_domination_derived_from_pointwise_data := 1
  concrete_theorem46_route_accepts_pointwise_data := 1
  prop_to_data_selector_inputs_added := 0
  rangeSupremum_to_locatedSupremum_selector_used := 0
  classical_choice_inputs_added := 0
  remaining_scalar_set_pointwise_laws_for_fpos_fneg_abs := 1
  remaining_corollary47_connection_steps := 1

/-- G221 package. -/
structure Chapter4G221Theorem46PointwiseLiftPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g220 : Chapter4G220Theorem46ConcreteSurfacePackage S
  audit : Theorem46PointwiseLiftAuditAfterG221
  pointwise_to_integral_lift_closed_this_step : Nat
  remaining_source_completion_steps_for_4_6_to_4_10 : Nat

def chapter4G221Theorem46PointwiseLiftPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G221Theorem46PointwiseLiftPackage S where
  g220 := chapter4G220Theorem46ConcreteSurfacePackage S
  audit := theorem46PointwiseLiftAuditAfterG221
  pointwise_to_integral_lift_closed_this_step := 1
  remaining_source_completion_steps_for_4_6_to_4_10 := 2

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G221. -/
def bishopRegularSeqChapter4Theorem46PointwiseLiftProgressAfterG221 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 90
  total_final_goal_percent := 97
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G221: reduced Theorem 4.6's local domination obligation from integral \
    two-step assumptions to pointwise representative-value inequalities. \
    Proposition 1.11 lifts those pointwise laws to integral monotonicity and \
    increment domination on full sets built from carried domains. Remaining: \
    prove the scalar/set pointwise laws for f+, f-, and |f|, then connect \
    Corollary 4.7/4.10."


end BishopCReal
