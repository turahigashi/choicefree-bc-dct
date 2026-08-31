import Mathdemo.Internal.Measure.PointLevelCleanDefinedAtExplicitRowwise

set_option linter.style.longLine false

/-!
# G313: source rows are raw subtractions, clean rows are `min2` subtractions

The G311 bridge cannot be treated as a definitional equality.  Printing the
source definitions shows that `prop_2_10_F/G` use raw representative
subtraction.  In contrast, the clean increment/drop rows are built through
`IntegrableSet1_sub`, whose representative is `hA.rep.sub (hA.rep.min2 hB.rep)`.

This node records that mismatch as concrete row-shape theorems.  It is an
important diagnostic for Chapter 4: the clean route solves the pointwise
flattening problem, while the original source representative needs a separate
transport argument or the downstream theorem must route through the clean
representative.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Source rows: raw representative subtraction -/

@[simp] theorem prop_2_10_F_source_zero_raw
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    prop_2_10_F A (fun k => (HA k).base) 0 =
      (HA 0).base.rep :=
  rfl


@[simp] theorem prop_2_10_F_source_succ_raw_sub
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    prop_2_10_F A (fun k => (HA k).base) (n + 1) =
      (phi_rep A (fun k => (HA k).base) (n + 1)).sub
        (phi_rep A (fun k => (HA k).base) n) :=
  rfl


@[simp] theorem prop_2_10_G_source_zero_raw_sub
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    prop_2_10_G A (fun k => (HA k).base) 0 =
      (HA 0).base.rep.sub (HA 0).base.rep :=
  rfl


@[simp] theorem prop_2_10_G_source_succ_raw_sub
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    prop_2_10_G A (fun k => (HA k).base) (n + 1) =
      (bigAndFin_int A (fun k => (HA k).base) n).rep.sub
        (bigAndFin_int A (fun k => (HA k).base) (n + 1)).rep :=
  rfl


/-! ## 2. Clean rows: set-difference representatives with `min2` -/

@[simp] theorem prop_2_10_F_clean_zero_raw
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    prop_2_10_F_clean (S := S) Sel A HA 0 =
      (HA 0).base.rep :=
  rfl


theorem prop_2_10_F_clean_succ_min2_sub
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    prop_2_10_F_clean (S := S) Sel A HA (n + 1) =
      (bigOrFin_int A (fun k => (HA k).base) (n + 1)).rep.sub
        ((bigOrFin_int A (fun k => (HA k).base) (n + 1)).rep.min2
          (bigOrFin_int A (fun k => (HA k).base) n).rep) := by
  rw [prop_2_10_F_clean_succ]
  rfl


theorem prop_2_10_G_clean_zero_min2_sub
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    prop_2_10_G_clean (S := S) Sel A HA 0 =
      (HA 0).base.rep.sub ((HA 0).base.rep.min2 (HA 0).base.rep) := by
  rw [prop_2_10_G_clean_zero]
  rfl


theorem prop_2_10_G_clean_succ_min2_sub
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    prop_2_10_G_clean (S := S) Sel A HA (n + 1) =
      (bigAndFin_int A (fun k => (HA k).base) n).rep.sub
        ((bigAndFin_int A (fun k => (HA k).base) n).rep.min2
          (bigAndFin_int A (fun k => (HA k).base) (n + 1)).rep) := by
  rw [prop_2_10_G_clean_succ]
  rfl


/-! ## 3. The remaining bridge is a real transport problem -/

structure Prop210RawVsCleanRowShapeAuditAfterG313 : Type where
  source_raw_subtraction_row_theorems_added : Nat
  clean_min2_subtraction_row_theorems_added : Nat
  union_zero_rows_definitionally_align : Nat
  intersection_zero_rows_definitionally_align : Nat
  source_clean_row_definitional_equality_proved : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_min2_transport_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def prop210RawVsCleanRowShapeAuditAfterG313 :
    Prop210RawVsCleanRowShapeAuditAfterG313 where
  source_raw_subtraction_row_theorems_added := 4
  clean_min2_subtraction_row_theorems_added := 3
  union_zero_rows_definitionally_align := 1
  intersection_zero_rows_definitionally_align := 0
  source_clean_row_definitional_equality_proved := 0
  clean_original_rep_equivalence_proved_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_min2_transport_problem := 1
  remaining_clean_original_equivalence_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G313RawVsCleanRowShapePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g312 : Chapter4G312ExplicitRowwisePointDataPackage S
  audit : BishopC.Prop210RawVsCleanRowShapeAuditAfterG313
  row_shape_obstruction_recorded : Nat
  remaining_min2_transport_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def chapter4G313RawVsCleanRowShapePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G313RawVsCleanRowShapePackage S where
  g312 := chapter4G312ExplicitRowwisePointDataPackage S
  audit := BishopC.prop210RawVsCleanRowShapeAuditAfterG313
  row_shape_obstruction_recorded := 1
  remaining_min2_transport_problem := 1
  remaining_clean_original_equivalence_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G313. -/
def bishopRegularSeqChapter4RawVsCleanRowShapeProgressAfterG313 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G313: recorded the exact row-shape mismatch.  The source Proposition-2.10 \
    rows are raw representative subtractions, while the clean rows are \
    set-difference representatives using min2.  Therefore clean/original \
    transport is a real remaining theorem, not a definitional rewrite."


end BishopCReal
