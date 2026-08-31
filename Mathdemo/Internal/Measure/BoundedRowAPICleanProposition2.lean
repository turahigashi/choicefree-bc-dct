import Mathdemo.Internal.Measure.PublicRowFlatTheoremCleanProposition

set_option linter.style.longLine false

/-!
# G306: bounded-row API for clean Proposition-2.10 majorants

G305 introduced the clean increment/drop rows.  The next mathematical datum is
not merely that each clean row is pointwise defined, but that its representative
absolute sum is bounded by a summable majorant.  This node packages that
bounded-row datum and gives direct adapters back to `PointwiseFlattenable` and
to the clean Proposition-2.10 representatives.

The actual finite-support majorants for union/intersection sides are still a
separate source-construction task.  This file makes the target shape precise.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pointwise absolute bounds -/

/-- A pointwise absolute-convergence witness together with a bound on its
absolute sum. -/
structure RepAbsBound
    (r : IntegrableRep S) (x : X) (b : R) : Type _ where
  abs : RepDefinedAt (S := S) r x
  abs_le : Le abs.sum b


/-- A clean characteristic representative invariant: on the positive side its
absolute representative sum is bounded by `1`, and on the negative side by
`0`.  The latter is intentionally strong; it is exactly the extra
representative-level cleanliness needed to make eventually-zero arguments work
after flattening. -/
structure CleanCharacteristicRep
    (A : BSet X) (r : IntegrableRep S) : Type _ where
  bound_on_s1 :
    forall x : X, x ∈ A.S1 ->
      RepAbsBound (S := S) r x (1 : R)
  bound_on_s2 :
    forall x : X, x ∈ A.S2 ->
      RepAbsBound (S := S) r x (0 : R)


/-- Rowwise absolute bounds by a summable majorant. -/
structure PointwiseRowAbsBounded
    (F : Nat → IntegrableRep S) (x : X) : Type _ where
  majorant : Nat → R
  majorant_sum : RSeq.SeriesSum majorant
  row_bound :
    forall i : Nat, RepAbsBound (S := S) (F i) x (majorant i)


namespace PointwiseRowAbsBounded

/-- Bounded-row data is exactly the majorant data expected by
`PointwiseFlattenable`. -/
def toPointwiseFlattenable
    {F : Nat → IntegrableRep S} {x : X}
    (B : PointwiseRowAbsBounded (S := S) F x) :
    PointwiseFlattenable (S := S) F x where
  row_abs := fun i => (B.row_bound i).abs
  majorant := B.majorant
  majorant_sum := B.majorant_sum
  row_abs_le := fun i => (B.row_bound i).abs_le


end PointwiseRowAbsBounded

/-! ## 2. Clean Proposition-2.10 bounded-row witnesses -/

structure Prop210BCleanPointwiseMajorantWitness
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)) : Type _ where
  row_bounds_on_s1 :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      PointwiseRowAbsBounded (S := S)
        (prop_2_10_F_clean (S := S) Sel A HA) x
  row_bounds_on_s2 :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      PointwiseRowAbsBounded (S := S)
        (prop_2_10_F_clean (S := S) Sel A HA) x


namespace Prop210BCleanPointwiseMajorantWitness

noncomputable def definedAt_on_s1
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210BCleanPointwiseMajorantWitness (S := S) Sel A HA hsum)
    (x : X) (hx : x ∈ (BSet.bigOr A).S1) :
    RepDefinedAt (S := S)
      (prop_2_10_rep_clean (S := S) Sel A HA hsum) x :=
  prop_2_10_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA hsum
    ((W.row_bounds_on_s1 x hx).toPointwiseFlattenable)


noncomputable def definedAt_on_s2
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210BCleanPointwiseMajorantWitness (S := S) Sel A HA hsum)
    (x : X) (hx : x ∈ (BSet.bigOr A).S2) :
    RepDefinedAt (S := S)
      (prop_2_10_rep_clean (S := S) Sel A HA hsum) x :=
  prop_2_10_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA hsum
    ((W.row_bounds_on_s2 x hx).toPointwiseFlattenable)


end Prop210BCleanPointwiseMajorantWitness

structure Prop210CCleanPointwiseMajorantWitness
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)) : Type _ where
  head_abs_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      RepDefinedAt (S := S) (HA 0).base.rep x
  row_bounds_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      PointwiseRowAbsBounded (S := S)
        (prop_2_10_G_clean (S := S) Sel A HA) x
  row_bounds_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      PointwiseRowAbsBounded (S := S)
        (prop_2_10_G_clean (S := S) Sel A HA) x


namespace Prop210CCleanPointwiseMajorantWitness

noncomputable def definedAt_on_s1
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210CCleanPointwiseMajorantWitness (S := S) Sel A HA hsum)
    (x : X) (hx : x ∈ (BSet.bigAnd A).S1) :
    RepDefinedAt (S := S)
      (prop_2_10_c_rep_clean (S := S) Sel A HA hsum) x := by
  let hx0 : x ∈ (A 0).S1 := Set.mem_iInter.mp hx 0
  let h0 : RepDefinedAt (S := S) (HA 0).base.rep x :=
    ⟨(HA 0).dom_on_s1 x hx0, (HA 0).abs_on_s1 x hx0⟩
  exact prop_2_10_c_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA hsum h0
    ((W.row_bounds_on_s1 x hx).toPointwiseFlattenable)


noncomputable def definedAt_on_s2
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210CCleanPointwiseMajorantWitness (S := S) Sel A HA hsum)
    (x : X) (hx : x ∈ (BSet.bigAnd A).S2) :
    RepDefinedAt (S := S)
      (prop_2_10_c_rep_clean (S := S) Sel A HA hsum) x :=
  prop_2_10_c_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA hsum
    (W.head_abs_on_s2 x hx)
    ((W.row_bounds_on_s2 x hx).toPointwiseFlattenable)


end Prop210CCleanPointwiseMajorantWitness

/-! ## 3. Audit -/

structure Sec2CleanPointwiseMajorantAuditAfterG306 : Type where
  rep_abs_bound_record_added : Nat
  clean_characteristic_bound_record_added : Nat
  bounded_rows_to_pointwise_flattenable_added : Nat
  clean_union_majorant_witness_record_added : Nat
  clean_intersection_majorant_witness_record_added : Nat
  clean_definedAt_side_adapters_added : Nat
  finite_support_majorants_constructed_this_step : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_finite_support_majorant_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def sec2CleanPointwiseMajorantAuditAfterG306 :
    Sec2CleanPointwiseMajorantAuditAfterG306 where
  rep_abs_bound_record_added := 1
  clean_characteristic_bound_record_added := 1
  bounded_rows_to_pointwise_flattenable_added := 1
  clean_union_majorant_witness_record_added := 1
  clean_intersection_majorant_witness_record_added := 1
  clean_definedAt_side_adapters_added := 4
  finite_support_majorants_constructed_this_step := 0
  clean_original_rep_equivalence_proved_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_finite_support_majorant_problem := 1
  remaining_clean_original_equivalence_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G306CleanPointwiseMajorantPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g305 : Chapter4G305CleanProp210RowsPackage S
  audit : BishopC.Sec2CleanPointwiseMajorantAuditAfterG306
  clean_bounded_row_api_available : Nat
  clean_side_definedAt_adapters_available : Nat
  remaining_finite_support_majorant_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def chapter4G306CleanPointwiseMajorantPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G306CleanPointwiseMajorantPackage S where
  g305 := chapter4G305CleanProp210RowsPackage S
  audit := BishopC.sec2CleanPointwiseMajorantAuditAfterG306
  clean_bounded_row_api_available := 1
  clean_side_definedAt_adapters_available := 1
  remaining_finite_support_majorant_problem := 1
  remaining_clean_original_equivalence_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G306. -/
def bishopRegularSeqChapter4CleanPointwiseMajorantProgressAfterG306 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G306: packaged representative absolute-sum bounds and bounded-row \
    majorants for the clean Proposition-2.10 route.  Remaining: construct the \
    finite-support majorants from clean characteristic data and identify the \
    clean representatives with the original telescoping representatives."


end BishopCReal
