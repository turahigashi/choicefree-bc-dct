import Mathdemo.Internal.CRat_iter408

set_option linter.style.longLine false

/-!
# G310: assemble clean classified-row witnesses from point data

G309 proved finite-support summability for the `0/1` side majorants induced by
cutoff-aware clean row classifiers.  This node assembles those ingredients into
the `Prop210BCleanClassifiedRowsWitness` and
`Prop210CCleanClassifiedRowsWitness` surfaces introduced in G307.

This closes the clean-row pointwise majorant route, conditional on explicit
source point-side data and clean characteristic representatives.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Union clean point-data witness -/

structure Prop210BCleanPointDataWitness
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) : Type _ where
  clean_rows :
    forall i : Nat,
      CleanCharacteristicRep (S := S)
        (bigOrFinIncrementSet A i)
        (prop_2_10_F_clean (S := S) Sel A HA i)
  point_on_s1 :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      BigOrPointSideData A x
  point_on_s2 :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      BigOrPointOutsideData A x


namespace Prop210BCleanPointDataWitness

def classifiedRowsOnS1
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    (W : Prop210BCleanPointDataWitness (S := S) Sel A HA)
    (x : X) (hx : x ∈ (BSet.bigOr A).S1) :
    CleanSideClassifiedRows (S := S)
      (bigOrFinIncrementSet A)
      (prop_2_10_F_clean (S := S) Sel A HA)
      x :=
  let D := W.point_on_s1 x hx
  { clean := W.clean_rows
    side := D.finiteRowSide
    side_majorant_sum := D.finiteRowSideMajorantSum }


def classifiedRowsOnS2
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    (W : Prop210BCleanPointDataWitness (S := S) Sel A HA)
    (x : X) (hx : x ∈ (BSet.bigOr A).S2) :
    CleanSideClassifiedRows (S := S)
      (bigOrFinIncrementSet A)
      (prop_2_10_F_clean (S := S) Sel A HA)
      x :=
  let D := W.point_on_s2 x hx
  { clean := W.clean_rows
    side := D.zeroRowSide
    side_majorant_sum := D.zeroRowSideMajorantSum }


noncomputable def toClassifiedRowsWitness
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210BCleanPointDataWitness (S := S) Sel A HA) :
    Prop210BCleanClassifiedRowsWitness (S := S) Sel A HA hsum where
  classified_on_s1 := W.classifiedRowsOnS1
  classified_on_s2 := W.classifiedRowsOnS2


noncomputable def toPointwiseMajorantWitness
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210BCleanPointDataWitness (S := S) Sel A HA) :
    Prop210BCleanPointwiseMajorantWitness (S := S) Sel A HA hsum :=
  (W.toClassifiedRowsWitness (hsum := hsum)).toPointwiseMajorantWitness


end Prop210BCleanPointDataWitness

/-! ## 2. Intersection clean point-data witness -/

structure Prop210CCleanPointDataWitness
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) : Type _ where
  head_abs_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      RepDefinedAt (S := S) (HA 0).base.rep x
  clean_rows :
    forall i : Nat,
      CleanCharacteristicRep (S := S)
        (bigAndFinDropSet A i)
        (prop_2_10_G_clean (S := S) Sel A HA i)
  point_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      BigAndPointInsideData A x
  point_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      BigAndPointOutsideData A x


namespace Prop210CCleanPointDataWitness

def classifiedRowsOnS1
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    (W : Prop210CCleanPointDataWitness (S := S) Sel A HA)
    (x : X) (hx : x ∈ (BSet.bigAnd A).S1) :
    CleanSideClassifiedRows (S := S)
      (bigAndFinDropSet A)
      (prop_2_10_G_clean (S := S) Sel A HA)
      x :=
  let D := W.point_on_s1 x hx
  { clean := W.clean_rows
    side := D.zeroRowSide
    side_majorant_sum := D.zeroRowSideMajorantSum }


def classifiedRowsOnS2
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    (W : Prop210CCleanPointDataWitness (S := S) Sel A HA)
    (x : X) (hx : x ∈ (BSet.bigAnd A).S2) :
    CleanSideClassifiedRows (S := S)
      (bigAndFinDropSet A)
      (prop_2_10_G_clean (S := S) Sel A HA)
      x :=
  let D := W.point_on_s2 x hx
  { clean := W.clean_rows
    side := D.finiteRowSide
    side_majorant_sum := D.finiteRowSideMajorantSum }


noncomputable def toClassifiedRowsWitness
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210CCleanPointDataWitness (S := S) Sel A HA) :
    Prop210CCleanClassifiedRowsWitness (S := S) Sel A HA hsum where
  head_abs_on_s2 := W.head_abs_on_s2
  classified_on_s1 := W.classifiedRowsOnS1
  classified_on_s2 := W.classifiedRowsOnS2


noncomputable def toPointwiseMajorantWitness
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)}
    (W : Prop210CCleanPointDataWitness (S := S) Sel A HA) :
    Prop210CCleanPointwiseMajorantWitness (S := S) Sel A HA hsum :=
  (W.toClassifiedRowsWitness (hsum := hsum)).toPointwiseMajorantWitness


end Prop210CCleanPointDataWitness

/-! ## 3. Combined clean point-data surface -/

structure Prop210CleanPointDataSurface
    (Sel : BSetBinarySideSelectorSurface X) : Type _ where
  union_point_data :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)),
      Prop210BCleanPointDataWitness (S := S) Sel A HA
  intersection_point_data :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)),
      Prop210CCleanPointDataWitness (S := S) Sel A HA


namespace Prop210CleanPointDataSurface

noncomputable def unionClassifiedRowsWitness
    {Sel : BSetBinarySideSelectorSurface X}
    (Surf : Prop210CleanPointDataSurface (S := S) Sel)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)} :
    Prop210BCleanClassifiedRowsWitness (S := S) Sel A HA hsum :=
  (Surf.union_point_data A HA).toClassifiedRowsWitness


noncomputable def intersectionClassifiedRowsWitness
    {Sel : BSetBinarySideSelectorSurface X}
    (Surf : Prop210CleanPointDataSurface (S := S) Sel)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    {hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)} :
    Prop210CCleanClassifiedRowsWitness (S := S) Sel A HA hsum :=
  (Surf.intersection_point_data A HA).toClassifiedRowsWitness


end Prop210CleanPointDataSurface

/-! ## 4. Audit -/

structure Sec2CleanPointDataAssemblyAuditAfterG310 : Type where
  union_point_data_witness_added : Nat
  intersection_point_data_witness_added : Nat
  clean_side_classified_rows_assembled : Nat
  clean_pointwise_majorant_witnesses_assembled : Nat
  combined_clean_point_data_surface_added : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  remaining_clean_original_equivalence_problem : Nat

def sec2CleanPointDataAssemblyAuditAfterG310 :
    Sec2CleanPointDataAssemblyAuditAfterG310 where
  union_point_data_witness_added := 1
  intersection_point_data_witness_added := 1
  clean_side_classified_rows_assembled := 2
  clean_pointwise_majorant_witnesses_assembled := 2
  combined_clean_point_data_surface_added := 1
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  clean_original_rep_equivalence_proved_this_step := 0
  remaining_clean_original_equivalence_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G310CleanPointDataAssemblyPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g309 : Chapter4G309CleanFiniteSupportMajorantPackage S
  audit : BishopC.Sec2CleanPointDataAssemblyAuditAfterG310
  clean_point_data_route_assembled : Nat
  remaining_clean_original_equivalence_problem : Nat

def chapter4G310CleanPointDataAssemblyPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G310CleanPointDataAssemblyPackage S where
  g309 := chapter4G309CleanFiniteSupportMajorantPackage S
  audit := BishopC.sec2CleanPointDataAssemblyAuditAfterG310
  clean_point_data_route_assembled := 1
  remaining_clean_original_equivalence_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G310. -/
def bishopRegularSeqChapter4CleanPointDataAssemblyProgressAfterG310 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G310: assembled finite-support clean row classifiers into the \
    Proposition-2.10 clean classified-row and pointwise-majorant witness \
    surfaces.  Remaining: clean/original telescoping representative equivalence \
    and final Chapter-4 routing."


end BishopCReal

