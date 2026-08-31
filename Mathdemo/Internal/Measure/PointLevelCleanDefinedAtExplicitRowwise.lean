import Mathdemo.Internal.Measure.CleanRouteBridgeSourceRepresentatives

set_option linter.style.longLine false

/-!
# G312: point-level clean `definedAt` from explicit rowwise side data

The key constructive distinction is that bare membership in the final
countable union/intersection is not the same as rowwise side data for every
source set `A_i`.  G308--G310 used explicit Type-coded point data, but the
global witness records still had fields indexed by final-side membership.

This node exposes the safer point-level API directly: given explicit rowwise
side data (and the relevant hit/all-side data), build `PointwiseFlattenable`
and `RepDefinedAt` for the clean Proposition-2.10 representative at that point.
No final membership is used to extract row data.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pointwise definedness of a characteristic representative from a side -/

def integrableSet1WithDef23_repDefinedAt_of_side
    {A : BSet X}
    (H : IntegrableSet1WithDef23 (S := S) A)
    {x : X}
    (side : PSum (x ∈ A.S1) (x ∈ A.S2)) :
    RepDefinedAt (S := S) H.base.rep x :=
  match side with
  | PSum.inl h => ⟨H.dom_on_s1 x h, H.abs_on_s1 x h⟩
  | PSum.inr h => ⟨H.dom_on_s2 x h, H.abs_on_s2 x h⟩


/-! ## 2. Union point-level API -/

namespace BigOrPointSideData

noncomputable def toCleanSideClassifiedRows
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigOrPointSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i)) :
    CleanSideClassifiedRows (S := S)
      (bigOrFinIncrementSet A)
      (prop_2_10_F_clean (S := S) Sel A HA)
      x where
  clean := clean_rows
  side := D.finiteRowSide
  side_majorant_sum := D.finiteRowSideMajorantSum


noncomputable def toPointwiseFlattenable
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigOrPointSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i)) :
    PointwiseFlattenable (S := S)
      (prop_2_10_F_clean (S := S) Sel A HA) x :=
  (D.toCleanSideClassifiedRows (S := S) (Sel := Sel) (HA := HA)
    clean_rows).toPointwiseRowAbsBounded.toPointwiseFlattenable


noncomputable def cleanRepDefinedAt
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigOrPointSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i))
    (clean_hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)) :
    RepDefinedAt (S := S)
      (prop_2_10_rep_clean (S := S) Sel A HA clean_hsum) x :=
  prop_2_10_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA clean_hsum
    (D.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA)
      clean_rows)


end BigOrPointSideData

namespace BigOrPointOutsideData

noncomputable def toCleanSideClassifiedRows
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigOrPointOutsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i)) :
    CleanSideClassifiedRows (S := S)
      (bigOrFinIncrementSet A)
      (prop_2_10_F_clean (S := S) Sel A HA)
      x where
  clean := clean_rows
  side := D.zeroRowSide
  side_majorant_sum := D.zeroRowSideMajorantSum


noncomputable def toPointwiseFlattenable
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigOrPointOutsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i)) :
    PointwiseFlattenable (S := S)
      (prop_2_10_F_clean (S := S) Sel A HA) x :=
  (D.toCleanSideClassifiedRows (S := S) (Sel := Sel) (HA := HA)
    clean_rows).toPointwiseRowAbsBounded.toPointwiseFlattenable


noncomputable def cleanRepDefinedAt
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigOrPointOutsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i))
    (clean_hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)) :
    RepDefinedAt (S := S)
      (prop_2_10_rep_clean (S := S) Sel A HA clean_hsum) x :=
  prop_2_10_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA clean_hsum
    (D.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA)
      clean_rows)


end BigOrPointOutsideData

/-! ## 3. Intersection point-level API -/

namespace BigAndPointInsideData

noncomputable def toCleanSideClassifiedRows
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigAndPointInsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i)) :
    CleanSideClassifiedRows (S := S)
      (bigAndFinDropSet A)
      (prop_2_10_G_clean (S := S) Sel A HA)
      x where
  clean := clean_rows
  side := D.zeroRowSide
  side_majorant_sum := D.zeroRowSideMajorantSum


noncomputable def toPointwiseFlattenable
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigAndPointInsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i)) :
    PointwiseFlattenable (S := S)
      (prop_2_10_G_clean (S := S) Sel A HA) x :=
  (D.toCleanSideClassifiedRows (S := S) (Sel := Sel) (HA := HA)
    clean_rows).toPointwiseRowAbsBounded.toPointwiseFlattenable


noncomputable def cleanRepDefinedAt
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigAndPointInsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i))
    (clean_hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)) :
    RepDefinedAt (S := S)
      (prop_2_10_c_rep_clean (S := S) Sel A HA clean_hsum) x :=
  prop_2_10_c_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA clean_hsum
    ⟨(HA 0).dom_on_s1 x (D.all_s1 0),
      (HA 0).abs_on_s1 x (D.all_s1 0)⟩
    (D.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA)
      clean_rows)


end BigAndPointInsideData

namespace BigAndPointOutsideData

def headRepDefinedAt
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigAndPointOutsideData A x) :
    RepDefinedAt (S := S) (HA 0).base.rep x :=
  integrableSet1WithDef23_repDefinedAt_of_side
    (S := S) (HA 0) (D.sideA 0)


noncomputable def toCleanSideClassifiedRows
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigAndPointOutsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i)) :
    CleanSideClassifiedRows (S := S)
      (bigAndFinDropSet A)
      (prop_2_10_G_clean (S := S) Sel A HA)
      x where
  clean := clean_rows
  side := D.finiteRowSide
  side_majorant_sum := D.finiteRowSideMajorantSum


noncomputable def toPointwiseFlattenable
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigAndPointOutsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i)) :
    PointwiseFlattenable (S := S)
      (prop_2_10_G_clean (S := S) Sel A HA) x :=
  (D.toCleanSideClassifiedRows (S := S) (Sel := Sel) (HA := HA)
    clean_rows).toPointwiseRowAbsBounded.toPointwiseFlattenable


noncomputable def cleanRepDefinedAt
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : BigAndPointOutsideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i))
    (clean_hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)) :
    RepDefinedAt (S := S)
      (prop_2_10_c_rep_clean (S := S) Sel A HA clean_hsum) x :=
  prop_2_10_c_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA clean_hsum
    (D.headRepDefinedAt (S := S) (HA := HA))
    (D.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA)
      clean_rows)


end BigAndPointOutsideData

/-! ## 4. Audit -/

structure Sec2ExplicitRowwisePointDataAuditAfterG312 : Type where
  characteristic_rep_definedAt_from_side_added : Nat
  union_point_level_flattenable_api_added : Nat
  union_point_level_clean_definedAt_api_added : Nat
  intersection_point_level_flattenable_api_added : Nat
  intersection_point_level_clean_definedAt_api_added : Nat
  final_membership_to_rowwise_data_extraction_used : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  remaining_clean_original_equivalence_problem : Nat
  remaining_final_domain_to_rowwise_data_problem : Nat

def sec2ExplicitRowwisePointDataAuditAfterG312 :
    Sec2ExplicitRowwisePointDataAuditAfterG312 where
  characteristic_rep_definedAt_from_side_added := 1
  union_point_level_flattenable_api_added := 2
  union_point_level_clean_definedAt_api_added := 2
  intersection_point_level_flattenable_api_added := 2
  intersection_point_level_clean_definedAt_api_added := 2
  final_membership_to_rowwise_data_extraction_used := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  clean_original_rep_equivalence_proved_this_step := 0
  remaining_clean_original_equivalence_problem := 1
  remaining_final_domain_to_rowwise_data_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G312ExplicitRowwisePointDataPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g311 : Chapter4G311CleanToSourceBridgePackage S
  audit : BishopC.Sec2ExplicitRowwisePointDataAuditAfterG312
  explicit_rowwise_point_data_api_available : Nat
  remaining_clean_original_equivalence_problem : Nat
  remaining_final_domain_to_rowwise_data_problem : Nat

def chapter4G312ExplicitRowwisePointDataPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G312ExplicitRowwisePointDataPackage S where
  g311 := chapter4G311CleanToSourceBridgePackage S
  audit := BishopC.sec2ExplicitRowwisePointDataAuditAfterG312
  explicit_rowwise_point_data_api_available := 1
  remaining_clean_original_equivalence_problem := 1
  remaining_final_domain_to_rowwise_data_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G312. -/
def bishopRegularSeqChapter4ExplicitRowwisePointDataProgressAfterG312 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G312: exposed the safe point-level API from explicit rowwise Type-coded \
    side data to PointwiseFlattenable and RepDefinedAt for the clean \
    Proposition-2.10 representatives.  No final membership is used to extract \
    row data.  Remaining: prove the final-domain-to-rowwise-data bridge where \
    the source definitions provide it, and prove clean/original representative \
    transport."


end BishopCReal
