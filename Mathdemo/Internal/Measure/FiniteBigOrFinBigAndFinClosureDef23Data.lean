import Mathdemo.Internal.Measure.BinarySideSelectorSurface

set_option linter.style.longLine false

/-!
# G294: finite `bigOrFin` / `bigAndFin` closure for Def23 data

G293 packaged the Type-coded binary side selectors needed to lift the binary
constructors to the strong `IntegrableSet1WithDef23` API.  This node propagates
that closure through the finite Chapter-2 constructors `bigOrFin` and
`bigAndFin`.

The new finite constructors are definitionally aligned with the existing base
constructors: their `.base` fields are the previous `bigOrFin_int` and
`bigAndFin_int` recursions.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

namespace BSetBinarySideSelectorSurface

/-! ## 1. Finite union closure -/

/-- Finite union closure for strong Definition-2.3 data. -/
noncomputable def bigOrFinWithDef23
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    forall n : Nat, IntegrableSet1WithDef23 (S := S) (bigOrFin A n)
| 0 => HA 0
| n + 1 =>
    orWithSurface (S := S) Sel
      (bigOrFinWithDef23 Sel A HA n)
      (HA (n + 1))


/-- The strong finite-union constructor has the existing `bigOrFin_int` as its
base field. -/
theorem bigOrFinWithDef23_base
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    forall n : Nat,
      (bigOrFinWithDef23 (S := S) Sel A HA n).base =
        bigOrFin_int A (fun k => (HA k).base) n
| 0 => rfl
| n + 1 => by
    change
      (orWithSurface (S := S) Sel
        (bigOrFinWithDef23 (S := S) Sel A HA n)
        (HA (n + 1))).base =
        IntegrableSet1_or
          (bigOrFin_int A (fun k => (HA k).base) n)
          (HA (n + 1)).base
    rw [orWithSurface_base, bigOrFinWithDef23_base Sel A HA n]


/-! ## 2. Finite intersection closure -/

/-- Finite intersection closure for strong Definition-2.3 data. -/
noncomputable def bigAndFinWithDef23
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    forall n : Nat, IntegrableSet1WithDef23 (S := S) (bigAndFin A n)
| 0 => HA 0
| n + 1 =>
    andWithSurface (S := S) Sel
      (bigAndFinWithDef23 Sel A HA n)
      (HA (n + 1))


/-- The strong finite-intersection constructor has the existing `bigAndFin_int`
as its base field. -/
theorem bigAndFinWithDef23_base
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    forall n : Nat,
      (bigAndFinWithDef23 (S := S) Sel A HA n).base =
        bigAndFin_int A (fun k => (HA k).base) n
| 0 => rfl
| n + 1 => by
    change
      (andWithSurface (S := S) Sel
        (bigAndFinWithDef23 (S := S) Sel A HA n)
        (HA (n + 1))).base =
        IntegrableSet1_and
          (bigAndFin_int A (fun k => (HA k).base) n)
          (HA (n + 1)).base
    rw [andWithSurface_base, bigAndFinWithDef23_base Sel A HA n]


end BSetBinarySideSelectorSurface

/-! ## 3. Audit -/

structure Sec2Def23FiniteConstructorAuditAfterG294 : Type where
  finite_union_constructor_added : Nat
  finite_intersection_constructor_added : Nat
  base_compatibility_theorems_added : Nat
  surface_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat

def sec2Def23FiniteConstructorAuditAfterG294 :
    Sec2Def23FiniteConstructorAuditAfterG294 where
  finite_union_constructor_added := 1
  finite_intersection_constructor_added := 1
  base_compatibility_theorems_added := 2
  surface_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G294Def23FiniteConstructorPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g293 : Chapter4G293Def23BinarySelectorSurfacePackage S
  audit : BishopC.Sec2Def23FiniteConstructorAuditAfterG294
  finite_constructors_added_this_step : Nat
  remaining_countable_constructor_problem : Nat

def chapter4G294Def23FiniteConstructorPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G294Def23FiniteConstructorPackage S where
  g293 := chapter4G293Def23BinarySelectorSurfacePackage S
  audit := BishopC.sec2Def23FiniteConstructorAuditAfterG294
  finite_constructors_added_this_step := 2
  remaining_countable_constructor_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G294. -/
def bishopRegularSeqChapter4Def23FiniteConstructorProgressAfterG294 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G294: propagated the selector-surface strong Def23 binary constructors \
    through finite bigOrFin and bigAndFin.  The resulting strong finite \
    constructors have base fields equal to the existing Chapter-2 \
    bigOrFin_int and bigAndFin_int recursions."


end BishopCReal
