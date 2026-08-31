import Mathdemo.Internal.Measure.CleanSideClassifiedRows

set_option linter.style.longLine false

/-!
# G308: concrete side classifiers from pointwise side data

G307 left the finite-support work behind the abstract `RowSideClassifier`.
This node constructs the row side classifier for the clean Proposition-2.10
increment/drop families from explicit Type-coded side data for the source
sets `A_i` at the point `x`.

This deliberately does not extract a witness from raw membership in
`BSet.bigOr A` or `BSet.bigAnd A`.  For the union-inside and
intersection-outside cases, the required hit index is source data that must be
kept explicitly in later nodes.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pointwise side data for source rows -/

/-- Type-coded side choices for every source row `A_i` at a fixed point. -/
def BSetPointSideData
    (A : Nat → BSet X) (x : X) : Type _ :=
  forall i : Nat, PSum (x ∈ (A i).S1) (x ∈ (A i).S2)


/-- A Type-coded hit of the positive side of some source row.  This is the
constructive replacement for extracting `∃ k, x ∈ (A k).S1` from
`x ∈ (BSet.bigOr A).S1`. -/
structure BigOrS1Hit
    (A : Nat → BSet X) (x : X) : Type _ where
  index : Nat
  mem : x ∈ (A index).S1


/-- A Type-coded hit of the negative side of some source row.  This is the
constructive replacement for extracting `∃ k, x ∈ (A k).S2` from
`x ∈ (BSet.bigAnd A).S2`. -/
structure BigAndS2Hit
    (A : Nat → BSet X) (x : X) : Type _ where
  index : Nat
  mem : x ∈ (A index).S2


/-! ## 2. Side algebra for finite constructors -/

/-- Type-coded side classification for relative subtraction from side
classifications of the two inputs. -/
def bsetSubSide
    {A B : BSet X} {x : X}
    (sa : PSum (x ∈ A.S1) (x ∈ A.S2))
    (sb : PSum (x ∈ B.S1) (x ∈ B.S2)) :
    PSum (x ∈ (BSet.sub A B).S1) (x ∈ (BSet.sub A B).S2) :=
  match sa, sb with
  | PSum.inl ha, PSum.inr hb =>
      PSum.inl (by
        change x ∈ A.S1 ∩ B.S2
        exact ⟨ha, hb⟩)
  | PSum.inl ha, PSum.inl hb =>
      PSum.inr (SubS2Case.toMem (SubS2Case.both ha hb))
  | PSum.inr ha, PSum.inr hb =>
      PSum.inr (SubS2Case.toMem (SubS2Case.neither ha hb))
  | PSum.inr ha, PSum.inl hb =>
      PSum.inr (SubS2Case.toMem (SubS2Case.leftFalse ha hb))


/-- Side classification of a finite union prefix from source row side data. -/
def bigOrFinSide
    (A : Nat → BSet X) {x : X}
    (sideA : BSetPointSideData A x) :
    forall n : Nat, PSum (x ∈ (bigOrFin A n).S1) (x ∈ (bigOrFin A n).S2)
| 0 => sideA 0
| n + 1 =>
    match bigOrFinSide A sideA n, sideA (n + 1) with
    | PSum.inl hp, PSum.inl hq =>
        PSum.inl (OrS1Case.toMem (OrS1Case.both hp hq))
    | PSum.inl hp, PSum.inr hq =>
        PSum.inl (OrS1Case.toMem (OrS1Case.leftOnly hp hq))
    | PSum.inr hp, PSum.inl hq =>
        PSum.inl (OrS1Case.toMem (OrS1Case.rightOnly hp hq))
    | PSum.inr hp, PSum.inr hq =>
        PSum.inr ⟨hp, hq⟩


/-- Side classification of a finite intersection prefix from source row side
data. -/
def bigAndFinSide
    (A : Nat → BSet X) {x : X}
    (sideA : BSetPointSideData A x) :
    forall n : Nat, PSum (x ∈ (bigAndFin A n).S1) (x ∈ (bigAndFin A n).S2)
| 0 => sideA 0
| n + 1 =>
    match bigAndFinSide A sideA n, sideA (n + 1) with
    | PSum.inl hp, PSum.inl hq =>
        PSum.inl ⟨hp, hq⟩
    | PSum.inl hp, PSum.inr hq =>
        PSum.inr (AndS2Case.toMem (AndS2Case.leftOnly hp hq))
    | PSum.inr hp, PSum.inl hq =>
        PSum.inr (AndS2Case.toMem (AndS2Case.rightOnly hp hq))
    | PSum.inr hp, PSum.inr hq =>
        PSum.inr (AndS2Case.toMem (AndS2Case.neither hp hq))


/-! ## 3. Clean Proposition-2.10 row side classifiers -/

/-- The clean union-increment rows have a concrete row-side classifier once
the source rows have Type-coded side data. -/
def bigOrFinIncrementSideClassifier
    (A : Nat → BSet X) {x : X}
    (sideA : BSetPointSideData A x) :
    RowSideClassifier (bigOrFinIncrementSet A) x
| 0 => sideA 0
| n + 1 =>
    bsetSubSide
      (bigOrFinSide A sideA (n + 1))
      (bigOrFinSide A sideA n)


/-- The clean intersection-drop rows have a concrete row-side classifier once
the source rows have Type-coded side data. -/
def bigAndFinDropSideClassifier
    (A : Nat → BSet X) {x : X}
    (sideA : BSetPointSideData A x) :
    RowSideClassifier (bigAndFinDropSet A) x
| 0 =>
    bsetSubSide (sideA 0) (sideA 0)
| n + 1 =>
    bsetSubSide
      (bigAndFinSide A sideA n)
      (bigAndFinSide A sideA (n + 1))


/-! ## 4. Point-data packages for the remaining finite-support step -/

structure BigOrPointSideData
    (A : Nat → BSet X) (x : X) : Type _ where
  sideA : BSetPointSideData A x
  hit : BigOrS1Hit A x


structure BigOrPointOutsideData
    (A : Nat → BSet X) (x : X) : Type _ where
  sideA : BSetPointSideData A x
  all_s2 : forall i : Nat, x ∈ (A i).S2


structure BigAndPointInsideData
    (A : Nat → BSet X) (x : X) : Type _ where
  sideA : BSetPointSideData A x
  all_s1 : forall i : Nat, x ∈ (A i).S1


structure BigAndPointOutsideData
    (A : Nat → BSet X) (x : X) : Type _ where
  sideA : BSetPointSideData A x
  hit : BigAndS2Hit A x


namespace BigOrPointSideData

def rowSide
    {A : Nat → BSet X} {x : X}
    (D : BigOrPointSideData A x) :
    RowSideClassifier (bigOrFinIncrementSet A) x :=
  bigOrFinIncrementSideClassifier A D.sideA


end BigOrPointSideData

namespace BigOrPointOutsideData

def rowSide
    {A : Nat → BSet X} {x : X}
    (D : BigOrPointOutsideData A x) :
    RowSideClassifier (bigOrFinIncrementSet A) x :=
  bigOrFinIncrementSideClassifier A D.sideA


end BigOrPointOutsideData

namespace BigAndPointInsideData

def rowSide
    {A : Nat → BSet X} {x : X}
    (D : BigAndPointInsideData A x) :
    RowSideClassifier (bigAndFinDropSet A) x :=
  bigAndFinDropSideClassifier A D.sideA


end BigAndPointInsideData

namespace BigAndPointOutsideData

def rowSide
    {A : Nat → BSet X} {x : X}
    (D : BigAndPointOutsideData A x) :
    RowSideClassifier (bigAndFinDropSet A) x :=
  bigAndFinDropSideClassifier A D.sideA


end BigAndPointOutsideData

/-! ## 5. Audit -/

structure Sec2CleanSideClassifierConstructionAuditAfterG308 : Type where
  source_point_side_data_added : Nat
  union_hit_data_added : Nat
  intersection_hit_data_added : Nat
  finite_union_prefix_classifier_added : Nat
  finite_intersection_prefix_classifier_added : Nat
  clean_union_increment_classifier_added : Nat
  clean_intersection_drop_classifier_added : Nat
  point_data_packages_added : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  finite_support_majorants_constructed_this_step : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  remaining_finite_support_majorant_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def sec2CleanSideClassifierConstructionAuditAfterG308 :
    Sec2CleanSideClassifierConstructionAuditAfterG308 where
  source_point_side_data_added := 1
  union_hit_data_added := 1
  intersection_hit_data_added := 1
  finite_union_prefix_classifier_added := 1
  finite_intersection_prefix_classifier_added := 1
  clean_union_increment_classifier_added := 1
  clean_intersection_drop_classifier_added := 1
  point_data_packages_added := 4
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  finite_support_majorants_constructed_this_step := 0
  clean_original_rep_equivalence_proved_this_step := 0
  remaining_finite_support_majorant_problem := 1
  remaining_clean_original_equivalence_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G308CleanSideClassifierConstructionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g307 : Chapter4G307CleanSideClassifiedRowsPackage S
  audit : BishopC.Sec2CleanSideClassifierConstructionAuditAfterG308
  source_point_side_classifier_available : Nat
  clean_row_side_classifiers_constructed_from_point_data : Nat
  remaining_finite_support_majorant_problem : Nat
  remaining_clean_original_equivalence_problem : Nat

def chapter4G308CleanSideClassifierConstructionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G308CleanSideClassifierConstructionPackage S where
  g307 := chapter4G307CleanSideClassifiedRowsPackage S
  audit := BishopC.sec2CleanSideClassifierConstructionAuditAfterG308
  source_point_side_classifier_available := 1
  clean_row_side_classifiers_constructed_from_point_data := 2
  remaining_finite_support_majorant_problem := 1
  remaining_clean_original_equivalence_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G308. -/
def bishopRegularSeqChapter4CleanSideClassifierConstructionProgressAfterG308 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G308: constructed clean Proposition-2.10 row side classifiers from \
    explicit source-row side data, without extracting indices or cases from \
    raw Prop membership.  Remaining: prove finite-support summability of the \
    induced 0/1 majorants and connect clean rows back to the source \
    telescoping representatives."


end BishopCReal

