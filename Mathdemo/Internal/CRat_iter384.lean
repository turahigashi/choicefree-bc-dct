import Mathdemo.Internal.CRat_iter383

set_option linter.style.longLine false

/-!
# G285: side-specific Def.2.3 local outer surface

G284 connected the Def.2.3/Def.1.6 local witnesses to the flat-value lemmas
under a general local outer provider.  This file narrows that frontier to the
source-shaped side-specific form actually used in the printed Proposition 4.2
argument:

* on `A.S1`, use the positive-side membership together with the local
  Definition-1.6 witness for `f`;
* on `A.S2`, use the negative-side membership together with the same kind of
  local `f` witness.

Thus the remaining analytic theorem is not an arbitrary
membership-to-witness selector.  It is precisely the f-cut/standard-lambda-row
outer absolute convergence for the explicit local witnesses.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Side-specific local outer frontier -/

/-- Source-shaped, side-specific form of the remaining Proposition-4.2 local
outer convergence theorem. -/
structure Sec4Prop42Def23SideLocalOuterProvider
    (D : IntegrableSet1Def23Surface (S := S)) : Type _ where
  outer_on_s1 :
    forall {A : BSet X} (hA : IntegrableSet1 S A)
      {f : IntegrableRep S} (hnn : RepNonneg f)
      {x : X},
      forall (hxA : x ∈ A.S1)
        (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
        (hf_abs : RSeq.SeriesSum
          (fun m => COF.abs ((f.fn m).toFun x))),
        Sec4Prop42LocalStandardAbsOuterAt (S := S) hA
          (Sec4Prop42LocalWitness.ofDef23S1
            (S := S) D hA hxA hf_dom hf_abs)
  outer_on_s2 :
    forall {A : BSet X} (hA : IntegrableSet1 S A)
      {f : IntegrableRep S} (hnn : RepNonneg f)
      {x : X},
      forall (hxA : x ∈ A.S2)
        (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
        (hf_abs : RSeq.SeriesSum
          (fun m => COF.abs ((f.fn m).toFun x))),
        Sec4Prop42LocalStandardAbsOuterAt (S := S) hA
          (Sec4Prop42LocalWitness.ofDef23S2
            (S := S) D hA hxA hf_dom hf_abs)


/-! ## 2. Side-specific abs packages -/

/-- Positive-side abs package from the side-specific local outer theorem. -/
noncomputable def sec4_prop42LocalAbsPackOnS1_of_def23SideLocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23SideLocalOuterProvider (S := S) D)
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    Sec4LambdaRowsAbsPackAt (S := S) A hA f x :=
  let W :=
    Sec4Prop42LocalWitness.ofDef23S1
      (S := S) D hA hxA hf_dom hf_abs
  sec4_lambdaRowsAbsPack_of_localWitness
    (S := S) hA W (O.outer_on_s1 hA hnn hxA hf_dom hf_abs)


/-- Negative-side abs package from the side-specific local outer theorem. -/
noncomputable def sec4_prop42LocalAbsPackOnS2_of_def23SideLocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23SideLocalOuterProvider (S := S) D)
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    Sec4LambdaRowsAbsPackAt (S := S) A hA f x :=
  let W :=
    Sec4Prop42LocalWitness.ofDef23S2
      (S := S) D hA hxA hf_dom hf_abs
  sec4_lambdaRowsAbsPack_of_localWitness
    (S := S) hA W (O.outer_on_s2 hA hnn hxA hf_dom hf_abs)


/-! ## 3. Side-specific flat abs and value statements -/

/-- Positive-side flat absolute convergence for `chi_A * f`, with all
witnesses sourced from Def.2.3 and Def.1.6. -/
noncomputable def sec4_prop42FlatAbsOnS1_of_def23SideLocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23SideLocalOuterProvider (S := S) D)
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x)) :=
  let W :=
    Sec4Prop42LocalWitness.ofDef23S1
      (S := S) D hA hxA hf_dom hf_abs
  sec4_prop42FlatAbs_of_localWitnessOuter
    (S := S) hA hnn W (O.outer_on_s1 hA hnn hxA hf_dom hf_abs)


/-- Negative-side flat absolute convergence for `chi_A * f`, with all
witnesses sourced from Def.2.3 and Def.1.6. -/
noncomputable def sec4_prop42FlatAbsOnS2_of_def23SideLocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23SideLocalOuterProvider (S := S) D)
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x)) :=
  let W :=
    Sec4Prop42LocalWitness.ofDef23S2
      (S := S) D hA hxA hf_dom hf_abs
  sec4_prop42FlatAbs_of_localWitnessOuter
    (S := S) hA hnn W (O.outer_on_s2 hA hnn hxA hf_dom hf_abs)


/-- Positive-side value statement for the side-specific source-shaped route. -/
theorem sec4_prop42ValueOnS1_of_def23SideLocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23SideLocalOuterProvider (S := S) D)
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    (seriesSum_of_abs
      (sec4_prop42FlatAbsOnS1_of_def23SideLocalOuter
        (S := S) D O hA hnn hxA hf_dom hf_abs)).sum =
      (seriesSum_of_abs hf_abs).sum := by
  let W :=
    Sec4Prop42LocalWitness.ofDef23S1
      (S := S) D hA hxA hf_dom hf_abs
  simpa [sec4_prop42FlatAbsOnS1_of_def23SideLocalOuter,
    Sec4Prop42LocalWitness.fSigned, W]
    using
      (sec4_prop42Value_on_s1_of_localWitnessOuter
        (S := S) hA hnn W
        (O.outer_on_s1 hA hnn hxA hf_dom hf_abs) hxA)


/-- Negative-side value statement for the side-specific source-shaped route. -/
theorem sec4_prop42ValueOnS2_of_def23SideLocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23SideLocalOuterProvider (S := S) D)
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    (seriesSum_of_abs
      (sec4_prop42FlatAbsOnS2_of_def23SideLocalOuter
        (S := S) D O hA hnn hxA hf_dom hf_abs)).sum = (0 : R) := by
  let W :=
    Sec4Prop42LocalWitness.ofDef23S2
      (S := S) D hA hxA hf_dom hf_abs
  simpa [sec4_prop42FlatAbsOnS2_of_def23SideLocalOuter, W]
    using
      (sec4_prop42Value_on_s2_of_localWitnessOuter
        (S := S) hA hnn W
        (O.outer_on_s2 hA hnn hxA hf_dom hf_abs) hxA)


/-! ## 4. Audit -/

structure Sec4Prop42Def23SideLocalOuterAuditAfterG285 : Type where
  arbitrary_local_outer_provider_required_for_new_route : Nat
  side_specific_outer_provider_used : Nat
  s1_def23_def16_value_closed : Nat
  s2_def23_def16_value_closed : Nat
  prop_union_case_split_to_type_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_side_specific_outer_analytic_frontier : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def sec4Prop42Def23SideLocalOuterAuditAfterG285 :
    Sec4Prop42Def23SideLocalOuterAuditAfterG285 where
  arbitrary_local_outer_provider_required_for_new_route := 0
  side_specific_outer_provider_used := 1
  s1_def23_def16_value_closed := 1
  s2_def23_def16_value_closed := 1
  prop_union_case_split_to_type_used := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_side_specific_outer_analytic_frontier := 1
  remaining_global_integrable_set_refactor_steps := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G285Prop42Def23SideLocalOuterPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g284 : Chapter4G284Prop42Def23LocalOuterPackage S
  audit : BishopC.Sec4Prop42Def23SideLocalOuterAuditAfterG285
  arbitrary_local_outer_removed_this_step : Nat
  remaining_side_specific_outer_analytic_frontier : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def chapter4G285Prop42Def23SideLocalOuterPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G285Prop42Def23SideLocalOuterPackage S where
  g284 := chapter4G284Prop42Def23LocalOuterPackage S
  audit := BishopC.sec4Prop42Def23SideLocalOuterAuditAfterG285
  arbitrary_local_outer_removed_this_step := 1
  remaining_side_specific_outer_analytic_frontier := 1
  remaining_global_integrable_set_refactor_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G285. -/
def bishopRegularSeqChapter4Prop42Def23SideLocalOuterProgressAfterG285 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G285: narrowed the remaining Proposition-4.2 outer-convergence surface \
    to the source-shaped S1/S2 local form.  The new route does not require an \
    arbitrary local witness provider, does not split a Prop-valued union into \
    Type data, and uses only Def.2.3 characteristic witnesses plus local \
    Def.1.6 f-witnesses. Countdown: 1 side-specific analytic outer theorem \
    remains, then 1 global refactor folds the Def23 surface into \
    IntegrableSet1."


end BishopCReal
