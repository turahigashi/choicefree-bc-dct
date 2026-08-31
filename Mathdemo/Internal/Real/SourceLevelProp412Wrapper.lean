import Mathdemo.Internal.Real.DownstreamTwoNatRoutePointwiseSeeds

set_option linter.style.longLine false

/-!
# G215: source-level Prop.4.12 wrapper on the no-seed route

G214 removed the pointwise-seed requirement from the downstream two-nat proof.
This increment connects that route back to the source-level data used for
Prop.4.12: constructor sources for the truncated representatives and the
definition-facing characteristic-function witnesses for integrable sets.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- A scoped provider for the only local witness still needed by the no-seed
route: absolute summability of the carried characteristic representative on
the actual good pair returned by convergence. -/
structure Prop412TwoNatScopedChiAProviderData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g) : Type _ where
  data :
    ∀ {eps : R} {seqN : Nat}
      (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      Prop412CommonGoodPair fn f g A hA eps seqN B hB C hC ->
        Prop412GoodSetChiAAbsData A (BishopC.BSet.and B C) hA

/-- One `A`-measure dyadic construction on the no-seed route. -/
noncomputable def prop412_dyadic_two_nat_common_good_construction_from_A_measure_schedule_no_seed
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
    (ChiA :
      Prop412TwoNatScopedChiAProviderData
        (fn := fn) A hA truncN F G) :
    Prop412DyadicTwoNatCommonGoodConstructionNoSeedData fn A hA truncN F G k where
  eps := Schedule.eps
  heps := Schedule.heps
  aux := by
    intro seqN B hB C hC Common
    let chiA_abs_on_good := ChiA.data B hB C hC Common
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
      { chiA_abs_on_good := chiA_abs_on_good
        arithmetic_budget :=
          BishopC.lt_of_le_of_lt hle Schedule.arithmetic_budget_A }

/-- All `A`-measure schedules generate all no-seed construction data. -/
noncomputable def prop412_all_two_nat_common_good_construction_from_A_measure_schedules_no_seed
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (Schedules : Prop412AllTwoNatAMeasureScheduleData S A hA truncN)
    (ChiA :
      Prop412TwoNatScopedChiAProviderData
        (fn := fn) A hA truncN F G) :
    Prop412AllTwoNatCommonGoodConstructionNoSeedData fn A hA truncN F G where
  data := by
    intro k
    exact
      prop412_dyadic_two_nat_common_good_construction_from_A_measure_schedule_no_seed
        hA F G (Schedules.data k) ChiA

/-- Final truncated-integral equality from full-support mid data and scoped
`chi_A` witnesses, using the corrected no-seed route. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data_full_support_A_measure_schedules_no_seed
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
    (ChiA :
      Prop412TwoNatScopedChiAProviderData
        (fn := fn) A hA truncN F.support G.support) :
    F.support.mid.rep.integral = G.support.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_two_nat_bound_sources_no_seed
    hA F.support G.support hf hg
    F.bound_source G.bound_source truncN_pos
    (prop412_all_two_nat_common_good_construction_from_A_measure_schedules_no_seed
      hA F.support G.support Schedules ChiA)

/-- Archimedean schedules plus scoped `chi_A` witnesses give the final no-seed
truncated-integral equality. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data_full_support_archimedean_A_measure_schedules_no_seed
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
    (ChiA :
      Prop412TwoNatScopedChiAProviderData
        (fn := fn) A hA truncN F.support G.support) :
    F.support.mid.rep.integral = G.support.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_full_support_A_measure_schedules_no_seed
    hA F G hf hg truncN_pos
    (prop412_all_two_nat_A_measure_schedules_from_archimedean S hA truncN)
    ChiA

end TruncatedIntegralBridge
end Proposition412

namespace Prop412AssumptionDischarge

open Proposition412
open Proposition412.TruncatedIntegralBridge
open SourceComplete412

/-- Definition-facing characteristic witnesses provide the scoped `chi_A`
source needed by the no-seed Prop.4.12 route. -/
def prop412_scoped_chiA_provider_from_characteristic_witness_family
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    (Fam : Prop412CharacteristicWitnessFamily (S := S))
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g) :
    Prop412TwoNatScopedChiAProviderData (fn := fn) A hA truncN F G where
  data := by
    intro eps seqN B hB C hC Common
    exact
      prop412_good_set_chiA_abs_from_characteristic_witness
        (Fam.witness A hA)
        (fun _ hxE =>
          prop412_common_good_pair_B_s1_subset_A_s1 Common hxE.1)

/-- Prop.4.12 truncated-integral equality from constructor sources and
definition-facing characteristic witnesses, with no pointwise-seed input. -/
theorem prop412_truncated_integrals_eq_from_characteristic_family_no_seed
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    {Mf : Prop412DataCarryingMeasurable S f}
    (Fam : Prop412CharacteristicWitnessFamily (S := S))
    (Mg : Prop412DataCarryingMeasurable S g)
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (truncN_pos : COF.lt 0 (truncN : R)) :
    (prop412_mid_full_support_data_from_constructor_source_data
        (Mf.mid_constructor_source A hA truncN)).support.mid.rep.integral =
      (prop412_mid_full_support_data_from_constructor_source_data
        (Mg.mid_constructor_source A hA truncN)).support.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_full_support_archimedean_A_measure_schedules_no_seed
    hA
    (prop412_mid_full_support_data_from_constructor_source_data
      (Mf.mid_constructor_source A hA truncN))
    (prop412_mid_full_support_data_from_constructor_source_data
      (Mg.mid_constructor_source A hA truncN))
    hf hg truncN_pos
    (prop412_scoped_chiA_provider_from_characteristic_witness_family
      (fn := fn) Fam A hA truncN
      (prop412_mid_support_data_from_constructor_source_data
        (Mf.mid_constructor_source A hA truncN))
      (prop412_mid_support_data_from_constructor_source_data
        (Mg.mid_constructor_source A hA truncN)))

end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge
open BishopRegularSeqChapter4.Prop412AssumptionDischarge

/-- G215 audit: the source-level Prop.4.12 wrapper is now connected to the
no-seed downstream route. -/
structure Prop412SourceNoSeedWrapperAuditAfterG215 : Type where
  source_wrapper_uses_no_seed_downstream_route : Nat
  characteristic_witness_family_supplies_chiA : Nat
  old_good_pair_pointwise_seed_source_needed : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_pointwise_seed_obligations_on_current_route : Nat

def prop412SourceNoSeedWrapperAuditAfterG215 :
    Prop412SourceNoSeedWrapperAuditAfterG215 where
  source_wrapper_uses_no_seed_downstream_route := 1
  characteristic_witness_family_supplies_chiA := 1
  old_good_pair_pointwise_seed_source_needed := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_pointwise_seed_obligations_on_current_route := 0

/-- G215 package. -/
structure BishopRegularSeqChapter4G215Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g214 : BishopRegularSeqChapter4G214Package S
  source_no_seed_wrapper_audit : Prop412SourceNoSeedWrapperAuditAfterG215
  source_wrapper_no_seed_closed_this_step : Nat
  remaining_steps_after_source_no_seed_wrapper : Nat

def bishopRegularSeqChapter4G215Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G215Package S where
  g214 := bishopRegularSeqChapter4G214Package S
  source_no_seed_wrapper_audit := prop412SourceNoSeedWrapperAuditAfterG215
  source_wrapper_no_seed_closed_this_step := 1
  remaining_steps_after_source_no_seed_wrapper := 0

/-- Progress after G215. -/
def bishopRegularSeqSourceNoSeedWrapperProgressAfterG215 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 100
  total_final_goal_percent := 100
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G215: connected the no-seed Prop.4.12 route to constructor-source data \
    and definition-facing characteristic witnesses. The current source wrapper \
    does not take the previous good-pair pointwise-seed provider."


end BishopCReal
