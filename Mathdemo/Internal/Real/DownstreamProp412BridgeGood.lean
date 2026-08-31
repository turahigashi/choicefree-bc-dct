import Mathdemo.Internal.Real.BacktrackingIntegrableSetsCharacteristicFunctionWitnesses

set_option linter.style.longLine false

/-!
# G211: downstream Prop.4.12 bridge with good-pair-scoped witnesses

G210 made the `chi_A` witness source definitional.  This increment removes the
next mismatch: the downstream truncated-integral bridge no longer has to ask
for local witnesses for every arbitrary pair `B,C`.  The source proof only
needs witnesses for the good pair returned by convergence, and
`Prop412CommonGoodPair` already contains the subset information
`B¹ ⊆ A¹`, `C¹ ⊆ A¹`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- The `B` half of a source common-good pair is included in `A¹`. -/
def prop412_common_good_pair_B_s1_subset_A_s1
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    {A B C : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {hB : BishopC.IntegrableSet1 S B}
    {hC : BishopC.IntegrableSet1 S C}
    {eps : R} {seqN : Nat}
    (Common : Prop412CommonGoodPair fn f g A hA eps seqN B hB C hC) :
    B.S1 ⊆ A.S1 :=
  fun _ hxB => (Common.1 hxB).1.1

/-- The `C` half of a source common-good pair is included in `A¹`. -/
def prop412_common_good_pair_C_s1_subset_A_s1
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    {A B C : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {hB : BishopC.IntegrableSet1 S B}
    {hC : BishopC.IntegrableSet1 S C}
    {eps : R} {seqN : Nat}
    (Common : Prop412CommonGoodPair fn f g A hA eps seqN B hB C hC) :
    C.S1 ⊆ A.S1 :=
  fun _ hxC => (Common.2.2.2.1 hxC).1.1

/-- Local witnesses scoped to the actual good pair returned by convergence.

This is weaker and more source-faithful than
`Prop412TwoNatLocalGoodSetWitnessProviderData`, which demanded witnesses for
all arbitrary `B,C`. -/
structure Prop412TwoNatScopedLocalGoodSetWitnessProviderData
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
        Prop412TwoNatLocalGoodSetWitnessData A hA truncN F G B hB C hC

/-- One `A`-measure dyadic construction using only good-pair-scoped local
witnesses. -/
def prop412_dyadic_two_nat_common_good_construction_from_A_measure_schedule_scoped
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
    (Local :
      Prop412TwoNatScopedLocalGoodSetWitnessProviderData
        (fn := fn) A hA truncN F G) :
    Prop412DyadicTwoNatCommonGoodConstructionData fn A hA truncN F G k where
  eps := Schedule.eps
  heps := Schedule.heps
  aux := by
    intro seqN B hB C hC Common
    let L := Local.data B hB C hC Common
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
      { chiA_abs_on_good := L.chiA_abs_on_good
        pointwise_seed := L.pointwise_seed
        arithmetic_budget :=
          BishopC.lt_of_le_of_lt hle Schedule.arithmetic_budget_A }

/-- All `A`-measure schedules generate all construction data using only
good-pair-scoped local witnesses. -/
def prop412_all_two_nat_common_good_construction_from_A_measure_schedules_scoped
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (Schedules : Prop412AllTwoNatAMeasureScheduleData S A hA truncN)
    (Local :
      Prop412TwoNatScopedLocalGoodSetWitnessProviderData
        (fn := fn) A hA truncN F G) :
    Prop412AllTwoNatCommonGoodConstructionData fn A hA truncN F G where
  data := by
    intro k
    exact
      prop412_dyadic_two_nat_common_good_construction_from_A_measure_schedule_scoped
        hA F G (Schedules.data k) Local

/-- Final truncated-integral equality from full-support mid data and scoped
local witnesses. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data_full_support_A_measure_schedules_scoped
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
    (Local :
      Prop412TwoNatScopedLocalGoodSetWitnessProviderData
        (fn := fn) A hA truncN F.support G.support) :
    F.support.mid.rep.integral = G.support.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_two_nat_bound_sources
    hA F.support G.support hf hg
    F.bound_source G.bound_source truncN_pos
    (prop412_all_two_nat_common_good_construction_from_A_measure_schedules_scoped
      hA F.support G.support Schedules Local)

/-- Archimedean schedules plus scoped local witnesses give the final
truncated-integral equality. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data_full_support_archimedean_A_measure_schedules_scoped
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
      Prop412TwoNatScopedLocalGoodSetWitnessProviderData
        (fn := fn) A hA truncN F.support G.support) :
    F.support.mid.rep.integral = G.support.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_full_support_A_measure_schedules_scoped
    hA F G hf hg truncN_pos
    (prop412_all_two_nat_A_measure_schedules_from_archimedean S hA truncN)
    Local

end TruncatedIntegralBridge
end Proposition412

namespace Prop412AssumptionDischarge

open Proposition412
open Proposition412.TruncatedIntegralBridge
open SourceComplete412

/-- The G209 good-pair-scoped source directly supplies the new downstream
scoped local provider.  The subset hypotheses are extracted from the actual
`Prop412CommonGoodPair`, not assumed for arbitrary `B,C`. -/
def prop412_scoped_local_provider_from_good_pair_source
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    {Mf : Prop412DataCarryingMeasurable S f}
    (Src : Prop412GoodPairScopedRepresentativeWitnessSource Mf)
    (Mg : Prop412DataCarryingMeasurable S g)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat) :
    Prop412TwoNatScopedLocalGoodSetWitnessProviderData
      (fn := fn) A hA truncN
      (prop412_mid_support_data_from_constructor_source_data
        (Mf.mid_constructor_source A hA truncN))
      (prop412_mid_support_data_from_constructor_source_data
        (Mg.mid_constructor_source A hA truncN)) where
  data := by
    intro eps seqN B hB C hC Common
    exact
      prop412_good_pair_scoped_witness_data
        Src Mg A hA truncN B hB C hC
        (prop412_common_good_pair_B_s1_subset_A_s1 Common)
        (prop412_common_good_pair_C_s1_subset_A_s1 Common)

/-- Prop.4.12 truncated-integral equality through the good-pair-scoped local
witness route. -/
theorem prop412_truncated_integrals_eq_from_good_pair_scoped_source
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    {Mf : Prop412DataCarryingMeasurable S f}
    (Src : Prop412GoodPairScopedRepresentativeWitnessSource Mf)
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
  prop412_mid_representative_integrals_eq_from_convergence_data_full_support_archimedean_A_measure_schedules_scoped
    hA
    (prop412_mid_full_support_data_from_constructor_source_data
      (Mf.mid_constructor_source A hA truncN))
    (prop412_mid_full_support_data_from_constructor_source_data
      (Mg.mid_constructor_source A hA truncN))
    hf hg truncN_pos
    (prop412_scoped_local_provider_from_good_pair_source
      (fn := fn) Src Mg A hA truncN)

end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge
open BishopRegularSeqChapter4.Prop412AssumptionDischarge

/-- G211 audit: the downstream bridge can now be run with good-pair-scoped
local witnesses, so the previous all-`B,C` provider is no longer required on this
path. -/
structure Prop412GoodPairScopedDownstreamAuditAfterG211 : Type where
  old_all_BC_provider_needed_for_scoped_path : Nat
  common_good_pair_supplies_B_subset_A : Nat
  common_good_pair_supplies_C_subset_A : Nat
  scoped_provider_to_all_construction_data_closed : Nat
  scoped_provider_to_truncated_integral_equality_closed : Nat
  external_choice_principle_added : Nat
  remaining_pointwise_seed_obligations : Nat

def prop412GoodPairScopedDownstreamAuditAfterG211 :
    Prop412GoodPairScopedDownstreamAuditAfterG211 where
  old_all_BC_provider_needed_for_scoped_path := 0
  common_good_pair_supplies_B_subset_A := 1
  common_good_pair_supplies_C_subset_A := 1
  scoped_provider_to_all_construction_data_closed := 1
  scoped_provider_to_truncated_integral_equality_closed := 1
  external_choice_principle_added := 0
  remaining_pointwise_seed_obligations := 1

/-- G211 package. -/
structure BishopRegularSeqChapter4G211Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g210 : BishopRegularSeqChapter4G210Package S
  scoped_downstream_audit : Prop412GoodPairScopedDownstreamAuditAfterG211
  downstream_bridge_from_good_pair_scoped_provider_closed_this_step : Nat
  remaining_steps_after_scoped_downstream_bridge : Nat

def bishopRegularSeqChapter4G211Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G211Package S where
  g210 := bishopRegularSeqChapter4G210Package S
  scoped_downstream_audit := prop412GoodPairScopedDownstreamAuditAfterG211
  downstream_bridge_from_good_pair_scoped_provider_closed_this_step := 1
  remaining_steps_after_scoped_downstream_bridge := 1

/-- Progress after G211. -/
def bishopRegularSeqGoodPairScopedDownstreamProgressAfterG211 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G211: replaced the downstream all-B,C local-witness route by a \
    good-pair-scoped route. Prop412CommonGoodPair supplies B^1 subset A^1 and \
    C^1 subset A^1, and scoped local witnesses now generate the all-dyadic \
    construction data and the truncated-integral equality. Remaining: build \
    the complement/bad pointwise seed itself from the representative data."


end BishopCReal
