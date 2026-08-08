import Mathdemo.Internal.CRat_iter382

set_option linter.style.longLine false

/-!
# G284: Definition-2.3 local witnesses to Proposition-4.2 flat values

G283 recovered the standard Proposition-4.2 rows from the two source witnesses:

* Definition 2.3 supplies the characteristic-function domain and absolute
  convergence data on the two sides of an integrable set;
* Definition 1.6 supplies the local domain and absolute convergence data for
  the integrable representative `f`.

This node connects those local witnesses to the already verified local
row-to-flat and value-identification lemmas.  The only remaining analytic
frontier is the local standard outer-convergence theorem itself: the convergence
of the series of row absolute sums for the standard lambda rows.  No witness is
extracted from a propositional full-set statement here.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Source-shaped local outer provider -/

/-- General form of the remaining Proposition-4.2 analytic frontier.

For each nonnegative integrable representative `f`, it provides the local
outer absolute convergence of the standard lambda rows built from explicit
local witnesses.  This is deliberately local: the witness comes from Def. 2.3
for `chi_A` and Def. 1.6 for `f`; no global membership-to-witness selector is
used. -/
structure Sec4Prop42Def23LocalOuterProvider : Type _ where
  outer :
    forall (f : IntegrableRep S) (hnn : RepNonneg f),
      Sec4Prop42LocalStandardAbsOuterProvider (S := S) f hnn


/-! ## 2. Abs packages from Definition 2.3 plus local `f` witnesses -/

/-- Positive-side abs package for the standard Proposition-4.2 rows. -/
noncomputable def sec4_prop42LocalAbsPackOnS1_of_def23LocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23LocalOuterProvider (S := S))
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
    (S := S) hA W ((O.outer f hnn) A hA x W)


/-- Negative-side abs package for the standard Proposition-4.2 rows. -/
noncomputable def sec4_prop42LocalAbsPackOnS2_of_def23LocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23LocalOuterProvider (S := S))
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
    (S := S) hA W ((O.outer f hnn) A hA x W)


/-! ## 3. Flat absolute convergence from the local packages -/

/-- Positive-side flat absolute convergence for the representative of
`chi_A * f`. -/
noncomputable def sec4_prop42FlatAbsOnS1_of_def23LocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23LocalOuterProvider (S := S))
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
    (S := S) hA hnn W ((O.outer f hnn) A hA x W)


/-- Negative-side flat absolute convergence for the representative of
`chi_A * f`. -/
noncomputable def sec4_prop42FlatAbsOnS2_of_def23LocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23LocalOuterProvider (S := S))
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
    (S := S) hA hnn W ((O.outer f hnn) A hA x W)


/-! ## 4. Source-facing pointwise value identification -/

/-- On `A.S1`, the constructed `chi_A * f` representative has the same local
value as `f`. -/
theorem sec4_prop42ValueOnS1_of_def23LocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23LocalOuterProvider (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    (seriesSum_of_abs
      (sec4_prop42FlatAbsOnS1_of_def23LocalOuter
        (S := S) D O hA hnn hxA hf_dom hf_abs)).sum =
      (seriesSum_of_abs hf_abs).sum := by
  let W :=
    Sec4Prop42LocalWitness.ofDef23S1
      (S := S) D hA hxA hf_dom hf_abs
  simpa [sec4_prop42FlatAbsOnS1_of_def23LocalOuter,
    Sec4Prop42LocalWitness.fSigned, W]
    using
      (sec4_prop42Value_on_s1_of_localWitnessOuter
        (S := S) hA hnn W ((O.outer f hnn) A hA x W) hxA)


/-- On `A.S2`, the constructed `chi_A * f` representative has value zero. -/
theorem sec4_prop42ValueOnS2_of_def23LocalOuter
    (D : IntegrableSet1Def23Surface (S := S))
    (O : Sec4Prop42Def23LocalOuterProvider (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    (seriesSum_of_abs
      (sec4_prop42FlatAbsOnS2_of_def23LocalOuter
        (S := S) D O hA hnn hxA hf_dom hf_abs)).sum = (0 : R) := by
  let W :=
    Sec4Prop42LocalWitness.ofDef23S2
      (S := S) D hA hxA hf_dom hf_abs
  simpa [sec4_prop42FlatAbsOnS2_of_def23LocalOuter, W]
    using
      (sec4_prop42Value_on_s2_of_localWitnessOuter
        (S := S) hA hnn W ((O.outer f hnn) A hA x W) hxA)


/-! ## 5. Audit -/

structure Sec4Prop42Def23LocalOuterAuditAfterG284 : Type where
  def23_to_local_witness_closed : Nat
  local_witness_to_abs_pack_closed : Nat
  local_witness_to_flat_abs_closed : Nat
  local_value_on_s1_closed : Nat
  local_value_on_s2_closed : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_local_standard_outer_frontier : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def sec4Prop42Def23LocalOuterAuditAfterG284 :
    Sec4Prop42Def23LocalOuterAuditAfterG284 where
  def23_to_local_witness_closed := 1
  local_witness_to_abs_pack_closed := 1
  local_witness_to_flat_abs_closed := 1
  local_value_on_s1_closed := 1
  local_value_on_s2_closed := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_local_standard_outer_frontier := 1
  remaining_global_integrable_set_refactor_steps := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G284Prop42Def23LocalOuterPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g283 : Chapter4G283Prop42Def23LocalRowsPackage S
  audit : BishopC.Sec4Prop42Def23LocalOuterAuditAfterG284
  prop42_def23_value_connection_closed_this_step : Nat
  remaining_local_standard_outer_frontier : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def chapter4G284Prop42Def23LocalOuterPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G284Prop42Def23LocalOuterPackage S where
  g283 := chapter4G283Prop42Def23LocalRowsPackage S
  audit := BishopC.sec4Prop42Def23LocalOuterAuditAfterG284
  prop42_def23_value_connection_closed_this_step := 1
  remaining_local_standard_outer_frontier := 1
  remaining_global_integrable_set_refactor_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G284. -/
def bishopRegularSeqChapter4Prop42Def23LocalOuterProgressAfterG284 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G284: connected Definition-2.3 characteristic witnesses and local \
    Definition-1.6 f-witnesses to the verified Proposition-4.2 flat-absolute \
    and value-identification lemmas on both S1 and S2. Countdown: 1 analytic \
    local standard outer-convergence theorem remains, then 1 global refactor \
    moves the Def23 surface into the IntegrableSet1 constructors."


end BishopCReal
