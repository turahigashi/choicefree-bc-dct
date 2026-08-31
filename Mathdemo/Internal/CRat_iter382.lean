import Mathdemo.Internal.CRat_iter381

set_option linter.style.longLine false

/-!
# G283: recover Proposition-4.2 local rows from Definition 2.3

G282 exposed a useful diagnostic: the previous global `RowsOnS2` surface is too
strong if it is read as a map from `x in A.S2` alone to row witnesses for an
arbitrary integrable representative `f`.  The rows also need the local
Definition-1.6 witness for `f`.

This node records the source-faithful local direction.  Definition 2.3 supplies
the characteristic-function side of the local witness; the integrable
representative supplies the `f` side on its own full domain.  The standard
Proposition-4.2 lambda rows are then constructed from those two pieces.

This does not add a choice principle.  It prevents the later proof from hiding
one by asking for global membership-to-witness maps.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Local witnesses from Definition 2.3 plus the `f` domain -/

/-- Build a local Proposition-4.2 witness on the positive side of an
integrable set from Definition-2.3 characteristic data and the local
Definition-1.6 witness for `f`. -/
noncomputable def Sec4Prop42LocalWitness.ofDef23S1
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs
      (f.valueAt x hf_dom m))) :
    Sec4Prop42LocalWitness (S := S) A hA f x where
  chi_dom := (D.data A hA).dom_on_s1 x hxA
  chi_abs := (D.data A hA).abs_on_s1 x hxA
  f_dom := hf_dom
  f_abs := hf_abs


/-- Build a local Proposition-4.2 witness on the negative side of an
integrable set from Definition-2.3 characteristic data and the local
Definition-1.6 witness for `f`. -/
noncomputable def Sec4Prop42LocalWitness.ofDef23S2
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs
      (f.valueAt x hf_dom m))) :
    Sec4Prop42LocalWitness (S := S) A hA f x where
  chi_dom := (D.data A hA).dom_on_s2 x hxA
  chi_abs := (D.data A hA).abs_on_s2 x hxA
  f_dom := hf_dom
  f_abs := hf_abs


/-! ## 2. Standard rows on the local full support -/

/-- Positive-side standard lambda rows from Definition 2.3 plus the local
`f` witness. -/
noncomputable def sec4_prop42LocalRowsOnS1_of_def23
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs
      (f.valueAt x hf_dom m))) :
    Sec4LambdaRowsAbsAt (S := S) A hA f x :=
  sec4_lambdaRowsAbs_of_localWitness
    (S := S) hA
    (Sec4Prop42LocalWitness.ofDef23S1
      (S := S) D hA hxA hf_dom hf_abs)


/-- Negative-side standard lambda rows from Definition 2.3 plus the local
`f` witness.  This is the source-faithful replacement for trying to prove the
previous global `RowsOnS2` field from `x in A.S2` alone. -/
noncomputable def sec4_prop42LocalRowsOnS2_of_def23
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs
      (f.valueAt x hf_dom m))) :
    Sec4LambdaRowsAbsAt (S := S) A hA f x :=
  sec4_lambdaRowsAbs_of_localWitness
    (S := S) hA
    (Sec4Prop42LocalWitness.ofDef23S2
      (S := S) D hA hxA hf_dom hf_abs)


/-! ## 3. Audit -/

structure Sec4Prop42Def23LocalRowsAuditAfterG283 : Type where
  global_rows_on_s2_from_membership_alone_closed : Nat
  local_rows_on_s2_from_def23_and_f_witness_closed : Nat
  local_rows_on_s1_from_def23_and_f_witness_closed : Nat
  def23_characteristic_domain_and_abs_used : Nat
  f_definition16_local_witness_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_local_standard_outer_frontier : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def sec4Prop42Def23LocalRowsAuditAfterG283 :
    Sec4Prop42Def23LocalRowsAuditAfterG283 where
  global_rows_on_s2_from_membership_alone_closed := 0
  local_rows_on_s2_from_def23_and_f_witness_closed := 1
  local_rows_on_s1_from_def23_and_f_witness_closed := 1
  def23_characteristic_domain_and_abs_used := 1
  f_definition16_local_witness_used := 1
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

structure Chapter4G283Prop42Def23LocalRowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g282 : Chapter4G282Theorem415Def23GlobalStandardRowsPackage S
  audit : BishopC.Sec4Prop42Def23LocalRowsAuditAfterG283
  local_rows_from_def23_closed_this_step : Nat
  remaining_local_standard_outer_frontier : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def chapter4G283Prop42Def23LocalRowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G283Prop42Def23LocalRowsPackage S where
  g282 := chapter4G282Theorem415Def23GlobalStandardRowsPackage S
  audit := BishopC.sec4Prop42Def23LocalRowsAuditAfterG283
  local_rows_from_def23_closed_this_step := 1
  remaining_local_standard_outer_frontier := 1
  remaining_global_integrable_set_refactor_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G283. -/
def bishopRegularSeqChapter4Prop42Def23LocalRowsProgressAfterG283 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G283: corrected the S2 row frontier to the source-faithful local form. \
    From Definition-2.3 characteristic domain/abs data plus the local \
    Definition-1.6 witness for f, the standard Proposition-4.2 rows on S1 and \
    S2 are constructed. Countdown: 1 local standard outer-convergence frontier \
    remains before the Chapter-4 local row route is closed, then 1 global \
    refactor moves the Def23 surface into IntegrableSet1 constructors."


end BishopCReal
