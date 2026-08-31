import Mathdemo.Internal.Measure.FromOriginalRowFlattenabilitySplitMajorants

set_option linter.style.longLine false

/-!
# G305: public row-to-flat theorem and clean Proposition-2.10 rows

G304 proved that ordinary `PointwiseFlattenable F x` supplies the split
majorants required by the actual `seriesSumRep_L1` implementation.  This node
exposes that result under the direct public theorem that downstream code wants,
and starts the clean Proposition-2.10 route:

* `seriesSumRep_L1_definedAt_of_pointwiseFlattenable` is the row-to-flat bridge;
* `prop_2_10_F_clean` uses the increment sets
  `B_0, B_{n+1} \ B_n`;
* `prop_2_10_G_clean` uses the drop sets
  `A_0 \ A_0, C_n \ C_{n+1}`;
* clean final representatives are made available separately from the original
  difference representatives.

This does not claim that the clean representatives have already been identified
with the original `prop_2_10_rep` / `prop_2_10_c_rep`.  It deliberately splits
the remaining work into (1) clean-row pointwise majorants and (2) source
equivalence with the original telescoping formulation.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Public row-to-flat theorem -/

/-- Direct public row-to-flat bridge for `seriesSumRep_L1`.

If every original row is pointwise absolutely summable at `x`, and the row
absolute sums are dominated by a summable majorant, then the flattened
representative built by `seriesSumRep_L1` is pointwise defined at `x`. -/
def seriesSumRep_L1_definedAt_of_pointwiseFlattenable
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    {x : X}
    (P : PointwiseFlattenable (S := S) F x) :
    RepDefinedAt (S := S) (seriesSumRep_L1 F hsum) x :=
  seriesSumRep_L1_definedAt_of_pointwiseData (S := S) F hsum
    ((SeriesSumRepL1SplitMajorants.ofPointwiseFlattenable
      (S := S) (hsum := hsum) P).toPointwiseData)


/-- Alias using the informal name from the proof discussion: row-level absolute
data transported to the flattened representative. -/
def rowToFlat_definedAt
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    {x : X}
    (P : PointwiseFlattenable (S := S) F x) :
    RepDefinedAt (S := S) (seriesSumRep_L1 F hsum) x :=
  seriesSumRep_L1_definedAt_of_pointwiseFlattenable
    (S := S) F hsum P


/-! ## 2. Clean Proposition-2.10 source rows -/

/-- Clean union-increment rows for Proposition 2.10:
`B_0, B_{n+1} \ B_n`, represented by the characteristic representative of the
increment set rather than by subtracting two finite-union representatives. -/
noncomputable def prop_2_10_F_clean
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    Nat → IntegrableRep S :=
  fun m =>
    (BSetBinarySideSelectorSurface.bigOrFinIncrementWithDef23
      (S := S) Sel A HA m).base.rep


@[simp] theorem prop_2_10_F_clean_zero
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    prop_2_10_F_clean (S := S) Sel A HA 0 =
      (HA 0).base.rep :=
  rfl


@[simp] theorem prop_2_10_F_clean_succ
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    prop_2_10_F_clean (S := S) Sel A HA (n + 1) =
      (IntegrableSet1_sub
        (bigOrFin_int A (fun k => (HA k).base) (n + 1))
        (bigOrFin_int A (fun k => (HA k).base) n)).rep := by
  unfold prop_2_10_F_clean
  rw [BSetBinarySideSelectorSurface.bigOrFinIncrementWithDef23_base_succ]


/-- Clean intersection-drop rows for Proposition 2.10:
`A_0 \ A_0, C_n \ C_{n+1}`, represented by characteristic representatives of
the drop sets rather than by raw subtraction of the two finite-intersection
representatives. -/
noncomputable def prop_2_10_G_clean
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    Nat → IntegrableRep S :=
  fun m =>
    (BSetBinarySideSelectorSurface.bigAndFinDropWithDef23
      (S := S) Sel A HA m).base.rep


@[simp] theorem prop_2_10_G_clean_zero
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    prop_2_10_G_clean (S := S) Sel A HA 0 =
      (IntegrableSet1_sub (HA 0).base (HA 0).base).rep :=
  rfl


@[simp] theorem prop_2_10_G_clean_succ
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    prop_2_10_G_clean (S := S) Sel A HA (n + 1) =
      (IntegrableSet1_sub
        (bigAndFin_int A (fun k => (HA k).base) n)
        (bigAndFin_int A (fun k => (HA k).base) (n + 1))).rep := by
  unfold prop_2_10_G_clean
  rw [BSetBinarySideSelectorSurface.bigAndFinDropWithDef23_base_succ]


/-! ## 3. Clean final representatives -/

/-- Clean countable-union representative built from increment rows. -/
noncomputable def prop_2_10_rep_clean
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)) :
    IntegrableRep S :=
  seriesSumRep_L1 (prop_2_10_F_clean (S := S) Sel A HA) hsum


/-- Clean countable-intersection representative built from drop rows. -/
noncomputable def prop_2_10_c_rep_clean
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)) :
    IntegrableRep S :=
  (HA 0).base.rep.sub
    (seriesSumRep_L1 (prop_2_10_G_clean (S := S) Sel A HA) hsum)


/-! ## 4. Clean representatives use the public row-to-flat bridge -/

noncomputable def prop_2_10_rep_clean_definedAt_of_pointwiseFlattenable
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1))
    {x : X}
    (P : PointwiseFlattenable (S := S)
      (prop_2_10_F_clean (S := S) Sel A HA) x) :
    RepDefinedAt (S := S)
      (prop_2_10_rep_clean (S := S) Sel A HA hsum) x :=
  rowToFlat_definedAt (S := S)
    (prop_2_10_F_clean (S := S) Sel A HA) hsum P


noncomputable def prop_2_10_c_rep_clean_definedAt_of_pointwiseFlattenable
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1))
    {x : X}
    (hhead : RepDefinedAt (S := S) (HA 0).base.rep x)
    (P : PointwiseFlattenable (S := S)
      (prop_2_10_G_clean (S := S) Sel A HA) x) :
    RepDefinedAt (S := S)
      (prop_2_10_c_rep_clean (S := S) Sel A HA hsum) x :=
  RepDefinedAt.sub hhead
    (rowToFlat_definedAt (S := S)
      (prop_2_10_G_clean (S := S) Sel A HA) hsum P)


/-! ## 5. Audit -/

structure Sec2CleanProp210RowsAuditAfterG305 : Type where
  public_row_to_flat_bridge_added : Nat
  clean_union_increment_rows_added : Nat
  clean_intersection_drop_rows_added : Nat
  clean_final_representatives_added : Nat
  clean_definedAt_bridge_added : Nat
  original_difference_rows_replaced_this_step : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_clean_pointwise_majorant_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def sec2CleanProp210RowsAuditAfterG305 :
    Sec2CleanProp210RowsAuditAfterG305 where
  public_row_to_flat_bridge_added := 1
  clean_union_increment_rows_added := 1
  clean_intersection_drop_rows_added := 1
  clean_final_representatives_added := 2
  clean_definedAt_bridge_added := 2
  original_difference_rows_replaced_this_step := 0
  clean_original_rep_equivalence_proved_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_clean_pointwise_majorant_problem := 1
  remaining_clean_original_equivalence_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G305CleanProp210RowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g304 : Chapter4G304OriginalPointwisePackage S
  audit : BishopC.Sec2CleanProp210RowsAuditAfterG305
  row_to_flat_public_bridge_available : Nat
  clean_prop210_rows_available : Nat
  remaining_clean_pointwise_majorant_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def chapter4G305CleanProp210RowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G305CleanProp210RowsPackage S where
  g304 := chapter4G304OriginalPointwisePackage S
  audit := BishopC.sec2CleanProp210RowsAuditAfterG305
  row_to_flat_public_bridge_available := 1
  clean_prop210_rows_available := 1
  remaining_clean_pointwise_majorant_problem := 1
  remaining_clean_original_equivalence_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G305. -/
def bishopRegularSeqChapter4CleanProp210RowsProgressAfterG305 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G305: exposed the direct row-to-flat theorem for seriesSumRep_L1 and \
    introduced clean Proposition-2.10 increment/drop representative families. \
    Remaining: construct their pointwise majorants and identify the clean \
    representatives with the original telescoping source representatives."


end BishopCReal
