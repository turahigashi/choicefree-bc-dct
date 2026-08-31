import Mathdemo.Internal.Measure.BoundedRowAPICleanProposition2

set_option linter.style.longLine false

/-!
# G307: clean side-classified rows

G306 fixed the bounded-row target.  This node adds the generic constructor that
will produce those bounded rows from clean characteristic representatives plus
Type-coded side classification.  The induced majorant is the `0/1` side
majorant: `1` on rows where `x` is on the positive side of the clean increment,
`0` on rows where it is on the negative side.

The remaining Proposition-2.10 task is now specifically to construct the
side-classification data and prove its `0/1` majorant is summable, which is the
finite-support/eventual-zero part of the source proof.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Generic clean classified rows -/

/-- A Type-coded side classifier for a row family of complemented sets. -/
def RowSideClassifier
    (E : Nat → BSet X) (x : X) : Type _ :=
  forall i : Nat, PSum (x ∈ (E i).S1) (x ∈ (E i).S2)


/-- The `0/1` majorant induced by a side classifier. -/
def rowSideMajorant
    (E : Nat → BSet X) (x : X)
    (side : RowSideClassifier E x) : Nat → R :=
  fun i =>
    match side i with
    | PSum.inl _ => 1
    | PSum.inr _ => 0


/-- Clean representatives for every row, a Type-coded side choice at `x`, and
summability of the resulting `0/1` side majorant. -/
structure CleanSideClassifiedRows
    (E : Nat → BSet X)
    (F : Nat → IntegrableRep S)
    (x : X) : Type _ where
  clean :
    forall i : Nat, CleanCharacteristicRep (S := S) (E i) (F i)
  side : RowSideClassifier E x
  side_majorant_sum :
    RSeq.SeriesSum (rowSideMajorant (R := R) E x side)


namespace CleanSideClassifiedRows

/-- Clean side-classified rows give the bounded-row majorant expected by G306. -/
def toPointwiseRowAbsBounded
    {E : Nat → BSet X}
    {F : Nat → IntegrableRep S}
    {x : X}
    (C : CleanSideClassifiedRows (S := S) E F x) :
    PointwiseRowAbsBounded (S := S) F x where
  majorant := rowSideMajorant (R := R) E x C.side
  majorant_sum := C.side_majorant_sum
  row_bound := by
    intro i
    unfold rowSideMajorant
    cases hside : C.side i with
    | inl h =>
        change RepAbsBound (S := S) (F i) x (1 : R)
        exact (C.clean i).bound_on_s1 x h
    | inr h =>
        change RepAbsBound (S := S) (F i) x (0 : R)
        exact (C.clean i).bound_on_s2 x h


end CleanSideClassifiedRows

/-! ## 2. Proposition-2.10 clean classified-row surfaces -/

structure Prop210BCleanClassifiedRowsWitness
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)) : Type _ where
  classified_on_s1 :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      CleanSideClassifiedRows (S := S)
        (bigOrFinIncrementSet A)
        (prop_2_10_F_clean (S := S) Sel A HA)
        x
  classified_on_s2 :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      CleanSideClassifiedRows (S := S)
        (bigOrFinIncrementSet A)
        (prop_2_10_F_clean (S := S) Sel A HA)
        x


namespace Prop210BCleanClassifiedRowsWitness

noncomputable def toPointwiseMajorantWitness
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210BCleanClassifiedRowsWitness (S := S) Sel A HA hsum) :
    Prop210BCleanPointwiseMajorantWitness (S := S) Sel A HA hsum where
  row_bounds_on_s1 := by
    intro x hx
    exact (W.classified_on_s1 x hx).toPointwiseRowAbsBounded
  row_bounds_on_s2 := by
    intro x hx
    exact (W.classified_on_s2 x hx).toPointwiseRowAbsBounded


end Prop210BCleanClassifiedRowsWitness

structure Prop210CCleanClassifiedRowsWitness
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)) : Type _ where
  head_abs_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      RepDefinedAt (S := S) (HA 0).base.rep x
  classified_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      CleanSideClassifiedRows (S := S)
        (bigAndFinDropSet A)
        (prop_2_10_G_clean (S := S) Sel A HA)
        x
  classified_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      CleanSideClassifiedRows (S := S)
        (bigAndFinDropSet A)
        (prop_2_10_G_clean (S := S) Sel A HA)
        x


namespace Prop210CCleanClassifiedRowsWitness

noncomputable def toPointwiseMajorantWitness
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210CCleanClassifiedRowsWitness (S := S) Sel A HA hsum) :
    Prop210CCleanPointwiseMajorantWitness (S := S) Sel A HA hsum where
  head_abs_on_s2 := W.head_abs_on_s2
  row_bounds_on_s1 := by
    intro x hx
    exact (W.classified_on_s1 x hx).toPointwiseRowAbsBounded
  row_bounds_on_s2 := by
    intro x hx
    exact (W.classified_on_s2 x hx).toPointwiseRowAbsBounded


end Prop210CCleanClassifiedRowsWitness

/-! ## 3. Audit -/

structure Sec2CleanSideClassifiedRowsAuditAfterG307 : Type where
  row_side_classifier_added : Nat
  row_side_majorant_added : Nat
  clean_classified_rows_record_added : Nat
  classified_rows_to_bounded_rows_added : Nat
  prop210_clean_classified_witness_records_added : Nat
  prop210_classified_to_majorant_adapters_added : Nat
  side_classification_constructed_this_step : Nat
  finite_support_majorants_constructed_this_step : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_side_classification_problem : Nat
  remaining_finite_support_majorant_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def sec2CleanSideClassifiedRowsAuditAfterG307 :
    Sec2CleanSideClassifiedRowsAuditAfterG307 where
  row_side_classifier_added := 1
  row_side_majorant_added := 1
  clean_classified_rows_record_added := 1
  classified_rows_to_bounded_rows_added := 1
  prop210_clean_classified_witness_records_added := 2
  prop210_classified_to_majorant_adapters_added := 2
  side_classification_constructed_this_step := 0
  finite_support_majorants_constructed_this_step := 0
  clean_original_rep_equivalence_proved_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_side_classification_problem := 1
  remaining_finite_support_majorant_problem := 1
  remaining_clean_original_equivalence_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G307CleanSideClassifiedRowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g306 : Chapter4G306CleanPointwiseMajorantPackage S
  audit : BishopC.Sec2CleanSideClassifiedRowsAuditAfterG307
  clean_side_classified_rows_api_available : Nat
  remaining_side_classification_problem : Nat
  remaining_finite_support_majorant_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def chapter4G307CleanSideClassifiedRowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G307CleanSideClassifiedRowsPackage S where
  g306 := chapter4G306CleanPointwiseMajorantPackage S
  audit := BishopC.sec2CleanSideClassifiedRowsAuditAfterG307
  clean_side_classified_rows_api_available := 1
  remaining_side_classification_problem := 1
  remaining_finite_support_majorant_problem := 1
  remaining_clean_original_equivalence_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G307. -/
def bishopRegularSeqChapter4CleanSideClassifiedRowsProgressAfterG307 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G307: added the clean side-classified row API.  Clean characteristic row \
    bounds plus Type-coded side choices and summability of the induced 0/1 \
    majorant now produce the bounded-row data needed by rowToFlat.  Remaining: \
    build side classifiers, finite-support sums, and clean/original \
    equivalence for Proposition 2.10."


end BishopCReal
