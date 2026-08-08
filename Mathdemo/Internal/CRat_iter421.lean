import Mathdemo.Internal.CRat_iter412

set_option linter.style.longLine false

/-!
# G315: explicit side data gives finite-support clean majorants

This node stays on the rep-carrying route rooted at `CRat_iter412`.

It records the part of the clean-characteristic route that is already available
from G308--G312: explicit rowwise side data plus an explicit final-side case
gives the finite-support pointwise flattenability needed by `rowToFlat`.

It deliberately does not claim an unconditional construction of
`CleanCharacteristicRep` for the clean set-difference rows.  The current public
API gives the clean rows as `IntegrableSet1_sub`/`min2` representatives, but it
does not expose the representative-level zero bound

```
  RepAbsBound row x 0
```

on the negative side.  That bound is exactly the remaining clean-row frontier.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Final side data without extracting witnesses from membership -/

/-- Type-coded union-side data at a point.  The positive case carries the
first-row hit data needed for finite support; the negative case carries all
rowwise negative-side data. -/
inductive UnionSideData (A : Nat -> BSet X) (x : X) : Type _ where
  | inside : (K : Nat) -> x ∈ (A K).S1 -> UnionSideData A x
  | outside : (forall i : Nat, x ∈ (A i).S2) -> UnionSideData A x


/-- Type-coded intersection-side data at a point.  The positive case carries
all rowwise positive-side data; the negative case carries an explicit negative
hit index. -/
inductive InterSideData (A : Nat -> BSet X) (x : X) : Type _ where
  | inside : (forall i : Nat, x ∈ (A i).S1) -> InterSideData A x
  | outside : (K : Nat) -> x ∈ (A K).S2 -> InterSideData A x


namespace UnionSideData

/-- Convert union-side data plus full rowwise side data into the G308 point-data
packages.  This is data movement only; no final membership proof is analyzed. -/
def toPointPackage
    {A : Nat -> BSet X} {x : X}
    (D : UnionSideData A x)
    (sideA : BSetPointSideData A x) :
    PSum (BigOrPointSideData A x) (BigOrPointOutsideData A x) :=
  match D with
  | inside K h =>
      PSum.inl
        { sideA := sideA
          hit := { index := K, mem := h } }
  | outside all_s2 =>
      PSum.inr
        { sideA := sideA
          all_s2 := all_s2 }


/-- Union clean rows are pointwise flattenable from explicit side data, once the
clean-characteristic row representatives are available. -/
noncomputable def toPointwiseFlattenable
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat -> BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : UnionSideData A x)
    (sideA : BSetPointSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i)) :
    PointwiseFlattenable (S := S)
      (prop_2_10_F_clean (S := S) Sel A HA) x :=
  match D.toPointPackage sideA with
  | PSum.inl Din =>
      Din.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA) clean_rows
  | PSum.inr Dout =>
      Dout.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA) clean_rows


end UnionSideData

namespace InterSideData

/-- Convert intersection-side data plus full rowwise side data into the G308
point-data packages.  This keeps the negative hit index as Type data. -/
def toPointPackage
    {A : Nat -> BSet X} {x : X}
    (D : InterSideData A x)
    (sideA : BSetPointSideData A x) :
    PSum (BigAndPointInsideData A x) (BigAndPointOutsideData A x) :=
  match D with
  | inside all_s1 =>
      PSum.inl
        { sideA := sideA
          all_s1 := all_s1 }
  | outside K h =>
      PSum.inr
        { sideA := sideA
          hit := { index := K, mem := h } }


/-- Intersection clean drop rows are pointwise flattenable from explicit side
data, once the clean-characteristic drop representatives are available. -/
noncomputable def toPointwiseFlattenable
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat -> BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {x : X}
    (D : InterSideData A x)
    (sideA : BSetPointSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i)) :
    PointwiseFlattenable (S := S)
      (prop_2_10_G_clean (S := S) Sel A HA) x :=
  match D.toPointPackage sideA with
  | PSum.inl Din =>
      Din.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA) clean_rows
  | PSum.inr Dout =>
      Dout.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA) clean_rows


end InterSideData

/-! ## 2. Public wrappers named for the Prop.2.10 route -/

noncomputable def prop_2_10_F_pointwiseFlattenable_of_unionSide
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat -> BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    {x : X}
    (sideA : BSetPointSideData A x)
    (D : UnionSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i)) :
    PointwiseFlattenable (S := S)
      (prop_2_10_F_clean (S := S) Sel A HA) x :=
  D.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA) sideA clean_rows


noncomputable def prop_2_10_G_pointwiseFlattenable_of_interSide
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat -> BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    {x : X}
    (sideA : BSetPointSideData A x)
    (D : InterSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i)) :
    PointwiseFlattenable (S := S)
      (prop_2_10_G_clean (S := S) Sel A HA) x :=
  D.toPointwiseFlattenable (S := S) (Sel := Sel) (HA := HA) sideA clean_rows


noncomputable def prop_2_10_rep_clean_definedAt_of_unionSide
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat -> BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (clean_hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1))
    {x : X}
    (sideA : BSetPointSideData A x)
    (D : UnionSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigOrFinIncrementSet A i)
          (prop_2_10_F_clean (S := S) Sel A HA i)) :
    RepDefinedAt (S := S)
      (prop_2_10_rep_clean (S := S) Sel A HA clean_hsum) x :=
  prop_2_10_rep_clean_definedAt_of_pointwiseFlattenable
    (S := S) Sel A HA clean_hsum
    (prop_2_10_F_pointwiseFlattenable_of_unionSide
      (S := S) Sel A HA sideA D clean_rows)


noncomputable def prop_2_10_c_rep_clean_definedAt_of_interSide
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat -> BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (clean_hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1))
    {x : X}
    (sideA : BSetPointSideData A x)
    (D : InterSideData A x)
    (clean_rows :
      forall i : Nat,
        CleanCharacteristicRep (S := S)
          (bigAndFinDropSet A i)
          (prop_2_10_G_clean (S := S) Sel A HA i)) :
    RepDefinedAt (S := S)
      (prop_2_10_c_rep_clean (S := S) Sel A HA clean_hsum) x :=
  match D.toPointPackage sideA with
  | PSum.inl Din =>
      Din.cleanRepDefinedAt (S := S) (Sel := Sel) (HA := HA)
        clean_rows clean_hsum
  | PSum.inr Dout =>
      Dout.cleanRepDefinedAt (S := S) (Sel := Sel) (HA := HA)
        clean_rows clean_hsum


/-! ## 3. Audit -/

structure Prop210CleanSideFiniteMajorantAuditAfterG315 : Type where
  union_side_data_added : Nat
  intersection_side_data_added : Nat
  union_finite_support_pointwiseFlattenable_connected : Nat
  intersection_finite_support_pointwiseFlattenable_connected : Nat
  clean_definedAt_connected_from_side_data : Nat
  clean_increment_rep_unconditional : Nat
  clean_drop_rep_unconditional : Nat
  drop_tail_abs_zero_from_current_api : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_clean_characteristic_rep_frontier : Nat

def prop210CleanSideFiniteMajorantAuditAfterG315 :
    Prop210CleanSideFiniteMajorantAuditAfterG315 where
  union_side_data_added := 1
  intersection_side_data_added := 1
  union_finite_support_pointwiseFlattenable_connected := 1
  intersection_finite_support_pointwiseFlattenable_connected := 1
  clean_definedAt_connected_from_side_data := 1
  clean_increment_rep_unconditional := 0
  clean_drop_rep_unconditional := 0
  drop_tail_abs_zero_from_current_api := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_clean_characteristic_rep_frontier := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G315CleanSideFiniteMajorantPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g313 : Chapter4G313RawVsCleanRowShapePackage S
  audit : BishopC.Prop210CleanSideFiniteMajorantAuditAfterG315
  side_data_to_finite_majorant_connected : Nat
  clean_characteristic_rows_unconditional : Nat
  remaining_clean_characteristic_rep_frontier : Nat

def chapter4G315CleanSideFiniteMajorantPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G315CleanSideFiniteMajorantPackage S where
  g313 := chapter4G313RawVsCleanRowShapePackage S
  audit := BishopC.prop210CleanSideFiniteMajorantAuditAfterG315
  side_data_to_finite_majorant_connected := 1
  clean_characteristic_rows_unconditional := 0
  remaining_clean_characteristic_rep_frontier := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G315. -/
def bishopRegularSeqChapter4CleanSideFiniteMajorantProgressAfterG315 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G315: added explicit UnionSideData/InterSideData wrappers that connect \
    rowwise Type-coded side data to the existing finite-support clean \
    PointwiseFlattenable and clean definedAt APIs.  The current API still does \
    not discharge CleanCharacteristicRep for min2 set-difference rows: the \
    representative-level S2 abs<=0 tail bound remains the frontier."


end BishopCReal
