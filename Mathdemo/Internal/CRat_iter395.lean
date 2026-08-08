import Mathdemo.Internal.CRat_iter394

set_option linter.style.longLine false

/-!
# G296: sequence surfaces for finite Proposition-2.10 increments

G295 added the individual finite step-difference constructors.  This node
packages those step differences into `Nat → BSet` families with strong
Definition-2.3 data at every index.

The purpose is modest: it provides the sequence-level surface needed before
attempting a countable closure argument.  It still does not construct the
global side-selector surface and does not identify these set families with the
analytic `prop_2_10_F` / `prop_2_10_G` representatives.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Set-level increment/decrement families -/

/-- Set family for the finite union increments used in Proposition 2.10:
`A_0`, then `(A_0 ∪ ... ∪ A_m) - (A_0 ∪ ... ∪ A_{m-1})`. -/
def bigOrFinIncrementSet (A : Nat → BSet X) : Nat → BSet X
| 0 => A 0
| n + 1 => BSet.sub (bigOrFin A (n + 1)) (bigOrFin A n)


/-- Set family for the finite intersection drops used in Proposition 2.10:
`A_0 - A_0`, then `(A_0 ∩ ... ∩ A_{m-1}) - (A_0 ∩ ... ∩ A_m)`. -/
def bigAndFinDropSet (A : Nat → BSet X) : Nat → BSet X
| 0 => BSet.sub (A 0) (A 0)
| n + 1 => BSet.sub (bigAndFin A n) (bigAndFin A (n + 1))


namespace BSetBinarySideSelectorSurface

/-! ## 2. Strong Def23 data for the families -/

/-- Strong Definition-2.3 data for every finite union increment. -/
noncomputable def bigOrFinIncrementWithDef23
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    forall m : Nat, IntegrableSet1WithDef23 (S := S) (bigOrFinIncrementSet A m)
| 0 => HA 0
| n + 1 => bigOrFinStepDiffWithDef23 (S := S) Sel A HA n


@[simp] theorem bigOrFinIncrementWithDef23_base_zero
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    (bigOrFinIncrementWithDef23 (S := S) Sel A HA 0).base =
      (HA 0).base :=
  rfl


@[simp] theorem bigOrFinIncrementWithDef23_base_succ
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    (bigOrFinIncrementWithDef23 (S := S) Sel A HA (n + 1)).base =
      IntegrableSet1_sub
        (bigOrFin_int A (fun k => (HA k).base) (n + 1))
        (bigOrFin_int A (fun k => (HA k).base) n) := by
  rw [bigOrFinIncrementWithDef23, bigOrFinStepDiffWithDef23_base]


/-- Strong Definition-2.3 data for every finite intersection drop. -/
noncomputable def bigAndFinDropWithDef23
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    forall m : Nat, IntegrableSet1WithDef23 (S := S) (bigAndFinDropSet A m)
| 0 => subWithSurface (S := S) Sel (HA 0) (HA 0)
| n + 1 => bigAndFinStepDiffWithDef23 (S := S) Sel A HA n


@[simp] theorem bigAndFinDropWithDef23_base_zero
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)) :
    (bigAndFinDropWithDef23 (S := S) Sel A HA 0).base =
      IntegrableSet1_sub (HA 0).base (HA 0).base :=
  rfl


@[simp] theorem bigAndFinDropWithDef23_base_succ
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    (bigAndFinDropWithDef23 (S := S) Sel A HA (n + 1)).base =
      IntegrableSet1_sub
        (bigAndFin_int A (fun k => (HA k).base) n)
        (bigAndFin_int A (fun k => (HA k).base) (n + 1)) := by
  rw [bigAndFinDropWithDef23, bigAndFinStepDiffWithDef23_base]


end BSetBinarySideSelectorSurface

/-! ## 3. Audit -/

structure Sec2Def23IncrementFamilyAuditAfterG296 : Type where
  union_increment_family_added : Nat
  intersection_drop_family_added : Nat
  strong_family_constructors_added : Nat
  base_compatibility_theorems_added : Nat
  surface_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  analytic_rep_identification_attempted_this_step : Nat

def sec2Def23IncrementFamilyAuditAfterG296 :
    Sec2Def23IncrementFamilyAuditAfterG296 where
  union_increment_family_added := 1
  intersection_drop_family_added := 1
  strong_family_constructors_added := 2
  base_compatibility_theorems_added := 4
  surface_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  analytic_rep_identification_attempted_this_step := 0


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G296Def23IncrementFamilyPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g295 : Chapter4G295Def23FiniteDifferencePackage S
  audit : BishopC.Sec2Def23IncrementFamilyAuditAfterG296
  sequence_families_added_this_step : Nat
  remaining_countable_constructor_problem : Nat

def chapter4G296Def23IncrementFamilyPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G296Def23IncrementFamilyPackage S where
  g295 := chapter4G295Def23FiniteDifferencePackage S
  audit := BishopC.sec2Def23IncrementFamilyAuditAfterG296
  sequence_families_added_this_step := 2
  remaining_countable_constructor_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G296. -/
def bishopRegularSeqChapter4Def23IncrementFamilyProgressAfterG296 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G296: packaged the finite union increments and intersection drops into \
    Nat-indexed BSet families, and supplied selector-surface strong Def23 data \
    for each term.  This prepares the countable closure route without yet \
    identifying the families with the analytic prop_2_10_F/G representatives."


end BishopCReal
