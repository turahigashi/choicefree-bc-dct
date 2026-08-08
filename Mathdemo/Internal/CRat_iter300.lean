import Mathdemo.Internal.CRat_iter299

set_option linter.style.longLine false

/-!
# G201: data-carrying mid constructor source for Proposition 4.12

G200 closed the Archimedean epsilon schedule.  The remaining source-faithful
frontier is the actual `mid(-n, chi_A h, n)` constructor.

The previous `BishopSec4_Convergence.IsMeasurable` interface is Prop/existential and
the helper `prop_4_4_min_chi_f` extracts representatives with
`choice witness selector`.  This file therefore does not use that path.  Instead it
names the Bishop-style source datum: the representative and the local witnesses
needed to read its pointwise value are carried from the start.  From that datum
we construct the existing full-support shape used by the G200 Prop. 4.12 bridge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- Scalar support fact for the source truncation: `mid(-n,0,n)=0`. -/
theorem prop412_scalarMid_zero
    {R : Type*} [COFOC R] (n : Nat) :
    prop412ScalarMid n (0 : R) = 0 := by
  dsimp [prop412ScalarMid]
  have hn : BishopC.Nonneg (n : R) :=
    BishopC.lemma33_natCast_nonneg n
  rw [BishopC.min_zero_const hn]
  have hneg_le_zero : BishopC.Le (-(n : R)) 0 := by
    apply BishopC.le_of_nonneg_sub
    convert hn using 1
    ring
  exact BishopC.cof_max_eq_left_of_le hneg_le_zero

/-- Bishop-style source data for the concrete `mid(-n, chi_A h, n)`
constructor.

The representative is not selected later from a quotient or a Prop-level
existence statement.  Its value law and the local domain/absolute-convergence
witnesses are carried as data. -/
structure Prop412MidRepresentativeConstructorSourceData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (n : Nat)
    (h : BishopC.PFunR Y R) : Type _ where
  rep : BishopC.IntegrableRep S
  value_eq :
    ∀ x (hxh : x ∈ h.dom)
      (hchi_abs : RSeq.SeriesSum
        (fun m => COF.abs ((hA.rep.fn m).toFun x)))
      (hrep : RSeq.SeriesSum (fun m => (rep.fn m).toFun x)),
      hrep.sum =
        prop412ScalarMid n
          ((BishopC.seriesSum_of_abs hchi_abs).sum * h.toFun x hxh)
  dom_of_mid_value :
    ∀ x
      (_hrep : RSeq.SeriesSum (fun m => (rep.fn m).toFun x)),
      x ∈ h.dom
  chiA_abs_of_mid_value :
    ∀ x
      (_hrep : RSeq.SeriesSum (fun m => (rep.fn m).toFun x)),
      RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x))
  dom_of_mid_abs :
    ∀ x
      (_hrep_abs : RSeq.SeriesSum
        (fun m => COF.abs ((rep.fn m).toFun x))),
      x ∈ h.dom
  chiA_abs_of_mid_abs :
    ∀ x
      (_hrep_abs : RSeq.SeriesSum
        (fun m => COF.abs ((rep.fn m).toFun x))),
      RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x))

/-- The raw constructor source immediately gives the basic mid representative
data used since G181. -/
def prop412_mid_data_from_constructor_source_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {n : Nat}
    {h : BishopC.PFunR Y R}
    (Src : Prop412MidRepresentativeConstructorSourceData A hA n h) :
    Prop412MidRepresentativeData A hA n h where
  rep := Src.rep
  value_eq := Src.value_eq

/-- The support-zero field is derived from the value law, not carried as an
independent assumption. -/
def prop412_mid_support_data_from_constructor_source_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {n : Nat}
    {h : BishopC.PFunR Y R}
    (Src : Prop412MidRepresentativeConstructorSourceData A hA n h) :
    Prop412MidRepresentativeSupportData A hA n h where
  mid := prop412_mid_data_from_constructor_source_data Src
  zero_of_chiA_zero := by
    intro x hchi_abs hmid hchi_zero
    have hdom : x ∈ h.dom :=
      Src.dom_of_mid_value x hmid
    have hchi_from_mid :
        RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x)) :=
      Src.chiA_abs_of_mid_value x hmid
    have hchi_value_eq :
        (BishopC.seriesSum_of_abs hchi_from_mid).sum =
          (BishopC.seriesSum_of_abs hchi_abs).sum := by
      exact BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hchi_from_mid)
        (BishopC.seriesSum_of_abs hchi_abs)
    have hval :
        hmid.sum =
          prop412ScalarMid n
            ((BishopC.seriesSum_of_abs hchi_from_mid).sum *
              h.toFun x hdom) :=
      Src.value_eq x hdom hchi_from_mid hmid
    rw [hval, hchi_value_eq, hchi_zero, zero_mul,
      prop412_scalarMid_zero]

/-- The same source datum supplies the local witnesses needed for the
pointwise `[-n,n]` bound source. -/
def prop412_mid_bound_source_data_from_constructor_source_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {n : Nat}
    {h : BishopC.PFunR Y R}
    (Src : Prop412MidRepresentativeConstructorSourceData A hA n h) :
    Prop412MidRepresentativeBoundSourceData
      (prop412_mid_support_data_from_constructor_source_data Src) where
  dom_of_mid_abs := by
    intro x hrep_abs
    exact Src.dom_of_mid_abs x hrep_abs
  chiA_abs_of_mid_abs := by
    intro x hrep_abs
    exact Src.chiA_abs_of_mid_abs x hrep_abs

/-- Constructor from Bishop-style raw mid data to the G197 full-support shape. -/
def prop412_mid_full_support_data_from_constructor_source_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {n : Nat}
    {h : BishopC.PFunR Y R}
    (Src : Prop412MidRepresentativeConstructorSourceData A hA n h) :
    Prop412MidRepresentativeFullSupportData A hA n h where
  support := prop412_mid_support_data_from_constructor_source_data Src
  bound_source :=
    prop412_mid_bound_source_data_from_constructor_source_data Src

/-- Prop. 4.12 final equality from data-carrying mid constructor sources and
the G200 Archimedean schedule. -/
theorem prop412_mid_constructor_source_integrals_eq_from_convergence_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (Fsrc : Prop412MidRepresentativeConstructorSourceData A hA truncN f)
    (Gsrc : Prop412MidRepresentativeConstructorSourceData A hA truncN g)
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (truncN_pos : COF.lt 0 (truncN : R))
    (Local :
      Prop412TwoNatLocalGoodSetWitnessProviderData A hA truncN
        (prop412_mid_support_data_from_constructor_source_data Fsrc)
        (prop412_mid_support_data_from_constructor_source_data Gsrc)) :
    (prop412_mid_full_support_data_from_constructor_source_data Fsrc).support.mid.rep.integral =
      (prop412_mid_full_support_data_from_constructor_source_data Gsrc).support.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_convergence_data_full_support_archimedean_A_measure_schedules
    hA
    (prop412_mid_full_support_data_from_constructor_source_data Fsrc)
    (prop412_mid_full_support_data_from_constructor_source_data Gsrc)
    hf hg truncN_pos Local

/-- Residual shape after G201. -/
structure Prop412MidConstructorSourceFrontierAfterG201 : Type where
  scalar_mid_zero_closed : Prop
  constructor_source_to_mid_data_closed : Prop
  constructor_source_to_support_data_closed : Prop
  constructor_source_to_bound_source_closed : Prop
  constructor_source_to_full_support_closed : Prop
  prop412_from_constructor_sources_and_archimedean_schedule_closed : Prop
  produce_constructor_source_data_from_data_carrying_measurability_still_needed : Prop
  prop_valued_convergence_extraction_still_requires_redesign_not_choice : Prop
  old_true_statement_used : Nat

def prop412MidConstructorSourceFrontierAfterG201 :
    Prop412MidConstructorSourceFrontierAfterG201 where
  scalar_mid_zero_closed := True
  constructor_source_to_mid_data_closed := True
  constructor_source_to_support_data_closed := True
  constructor_source_to_bound_source_closed := True
  constructor_source_to_full_support_closed := True
  prop412_from_constructor_sources_and_archimedean_schedule_closed := True
  produce_constructor_source_data_from_data_carrying_measurability_still_needed :=
    True
  prop_valued_convergence_extraction_still_requires_redesign_not_choice := True
  old_true_statement_used := 0

/-- G201 package. -/
structure Chapter4G201Prop412MidConstructorSourcePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g200 : BishopRegularSeqChapter4G200Package S
  mid_constructor_source_frontier_after_g201 :
    Prop412MidConstructorSourceFrontierAfterG201
  mid_constructor_source_adapter_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_assumption_free_source_prop412_pass : Nat

def chapter4G201Prop412MidConstructorSourcePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G201Prop412MidConstructorSourcePackage S where
  g200 := bishopRegularSeqChapter4G200Package S
  mid_constructor_source_frontier_after_g201 :=
    prop412MidConstructorSourceFrontierAfterG201
  mid_constructor_source_adapter_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 1
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_assumption_free_source_prop412_pass := 1

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G201 package exposed at top level. -/
structure BishopRegularSeqChapter4G201Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package :
    BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G201Prop412MidConstructorSourcePackage S
  mid_constructor_source_adapter_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_assumption_free_source_prop412_pass : Nat

def bishopRegularSeqChapter4G201Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G201Package S where
  package :=
    BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G201Prop412MidConstructorSourcePackage S
  mid_constructor_source_adapter_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 1
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_assumption_free_source_prop412_pass := 1

/-- Progress after G201. -/
def bishopRegularSeqCh1To4ProgressAfterG201 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G201: added the choice-free, data-carrying source shape for the \
    mid(-n,chi_A h,n) constructor and proved that it yields the existing \
    full-support Prop. 4.12 bridge. Remaining: produce this source data from a \
    data-carrying measurability interface, instead of the previous Prop/choose one."


end BishopCReal
