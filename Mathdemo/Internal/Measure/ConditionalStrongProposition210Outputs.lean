import Mathdemo.Internal.Measure.BaseProposition210WrappersDef23

set_option linter.style.longLine false

/-!
# G298: conditional strong Proposition-2.10 outputs

G297 returned the existing base `IntegrableSet1` Proposition-2.10 outputs from
strong Definition-2.3 input hypotheses.  The missing data for a strong output
is exactly the sidewise domain and absolute-convergence information for the
final countable representative.

This node makes that frontier explicit.  It defines witness records for the
countable union/intersection outputs and upgrades the G297 base wrappers to
`IntegrableSet1WithDef23` when such witnesses are supplied.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Output witness records -/

/-- The missing Definition-2.3 side data for the Proposition-2.10(b) countable
union output produced by `prop_2_10_b_ofWithDef23`. -/
structure Prop210BWithDef23OutputWitness
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) : Type _ where
  dom_on_s1 :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      forall m : Nat,
        x ∈ ((prop_2_10_b_ofWithDef23 (S := S) A HA h_conv).rep.fn m).dom
  dom_on_s2 :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      forall m : Nat,
        x ∈ ((prop_2_10_b_ofWithDef23 (S := S) A HA h_conv).rep.fn m).dom
  abs_on_s1 :
    forall (x : X) (hx : x ∈ (BSet.bigOr A).S1),
      RSeq.SeriesSum
        (fun m =>
          COF.abs
            ((prop_2_10_b_ofWithDef23 (S := S) A HA h_conv).rep.valueAt
              x (dom_on_s1 x hx) m))
  abs_on_s2 :
    forall (x : X) (hx : x ∈ (BSet.bigOr A).S2),
      RSeq.SeriesSum
        (fun m =>
          COF.abs
            ((prop_2_10_b_ofWithDef23 (S := S) A HA h_conv).rep.valueAt
              x (dom_on_s2 x hx) m))


/-- The missing Definition-2.3 side data for the Proposition-2.10(c) countable
intersection output produced by `prop_2_10_c_ofWithDef23`. -/
structure Prop210CWithDef23OutputWitness
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) : Type _ where
  dom_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      forall m : Nat,
        x ∈ ((prop_2_10_c_ofWithDef23 (S := S) A HA h_lim).rep.fn m).dom
  dom_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      forall m : Nat,
        x ∈ ((prop_2_10_c_ofWithDef23 (S := S) A HA h_lim).rep.fn m).dom
  abs_on_s1 :
    forall (x : X) (hx : x ∈ (BSet.bigAnd A).S1),
      RSeq.SeriesSum
        (fun m =>
          COF.abs
            ((prop_2_10_c_ofWithDef23 (S := S) A HA h_lim).rep.valueAt
              x (dom_on_s1 x hx) m))
  abs_on_s2 :
    forall (x : X) (hx : x ∈ (BSet.bigAnd A).S2),
      RSeq.SeriesSum
        (fun m =>
          COF.abs
            ((prop_2_10_c_ofWithDef23 (S := S) A HA h_lim).rep.valueAt
              x (dom_on_s2 x hx) m))


/-! ## 2. Conditional strong outputs -/

/-- Strong Proposition-2.10(b) output, conditional on explicit final side
domain/absolute-convergence witnesses. -/
noncomputable def prop_2_10_b_withDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base))
    (W : Prop210BWithDef23OutputWitness (S := S) A HA h_conv) :
    IntegrableSet1WithDef23 (S := S) (BSet.bigOr A) where
  base := prop_2_10_b_ofWithDef23 (S := S) A HA h_conv
  dom_on_s1 := W.dom_on_s1
  dom_on_s2 := W.dom_on_s2
  abs_on_s1 := W.abs_on_s1
  abs_on_s2 := W.abs_on_s2


@[simp] theorem prop_2_10_b_withDef23_base
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base))
    (W : Prop210BWithDef23OutputWitness (S := S) A HA h_conv) :
    (prop_2_10_b_withDef23 (S := S) A HA h_conv W).base =
      prop_2_10_b_ofWithDef23 (S := S) A HA h_conv :=
  rfl


theorem prop_2_10_b_measure_withDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base))
    (W : Prop210BWithDef23OutputWitness (S := S) A HA h_conv) :
    Le (measure1 S (prop_2_10_b_withDef23 (S := S) A HA h_conv W).base)
      h_conv.sum := by
  exact prop_2_10_b_measure_ofWithDef23 (S := S) A HA h_conv


/-- Strong Proposition-2.10(c) output, conditional on explicit final side
domain/absolute-convergence witnesses. -/
noncomputable def prop_2_10_c_withDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β)
    (W : Prop210CWithDef23OutputWitness (S := S) A HA h_lim) :
    IntegrableSet1WithDef23 (S := S) (BSet.bigAnd A) where
  base := prop_2_10_c_ofWithDef23 (S := S) A HA h_lim
  dom_on_s1 := W.dom_on_s1
  dom_on_s2 := W.dom_on_s2
  abs_on_s1 := W.abs_on_s1
  abs_on_s2 := W.abs_on_s2


@[simp] theorem prop_2_10_c_withDef23_base
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β)
    (W : Prop210CWithDef23OutputWitness (S := S) A HA h_lim) :
    (prop_2_10_c_withDef23 (S := S) A HA h_lim W).base =
      prop_2_10_c_ofWithDef23 (S := S) A HA h_lim :=
  rfl


theorem prop_2_10_c_measure_withDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β)
    (W : Prop210CWithDef23OutputWitness (S := S) A HA h_lim) :
    measure1 S (prop_2_10_c_withDef23 (S := S) A HA h_lim W).base =
      h_lim.fst := by
  exact prop_2_10_c_measure_ofWithDef23 (S := S) A HA h_lim


/-! ## 3. Audit -/

structure Sec2Def23ConditionalProp210OutputAuditAfterG298 : Type where
  union_output_witness_record_added : Nat
  intersection_output_witness_record_added : Nat
  conditional_strong_outputs_added : Nat
  measure_theorems_lifted_to_strong_outputs : Nat
  final_side_witnesses_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat

def sec2Def23ConditionalProp210OutputAuditAfterG298 :
    Sec2Def23ConditionalProp210OutputAuditAfterG298 where
  union_output_witness_record_added := 1
  intersection_output_witness_record_added := 1
  conditional_strong_outputs_added := 2
  measure_theorems_lifted_to_strong_outputs := 2
  final_side_witnesses_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G298Def23ConditionalProp210OutputPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g297 : Chapter4G297Def23Prop210BaseWrapperPackage S
  audit : BishopC.Sec2Def23ConditionalProp210OutputAuditAfterG298
  conditional_strong_outputs_added_this_step : Nat
  remaining_final_side_witness_problem : Nat

def chapter4G298Def23ConditionalProp210OutputPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G298Def23ConditionalProp210OutputPackage S where
  g297 := chapter4G297Def23Prop210BaseWrapperPackage S
  audit := BishopC.sec2Def23ConditionalProp210OutputAuditAfterG298
  conditional_strong_outputs_added_this_step := 2
  remaining_final_side_witness_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G298. -/
def bishopRegularSeqChapter4Def23ConditionalProp210OutputProgressAfterG298 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G298: made the remaining strong Proposition-2.10 output obligation \
    explicit as final sidewise domain/absolute-convergence witness records, \
    and upgraded the G297 base outputs to IntegrableSet1WithDef23 when those \
    records are supplied."


end BishopCReal
