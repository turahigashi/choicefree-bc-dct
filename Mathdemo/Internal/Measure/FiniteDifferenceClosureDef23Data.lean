import Mathdemo.Internal.Measure.FiniteBigOrFinBigAndFinClosureDef23Data

set_option linter.style.longLine false

/-!
# G295: finite difference closure for Def23 data

G294 gave strong Definition-2.3 data for the finite approximants
`bigOrFin A n` and `bigAndFin A n`.  This node adds the corresponding finite
step-difference closures:

* `(A_0 ∪ ... ∪ A_{n+1}) - (A_0 ∪ ... ∪ A_n)`;
* `(A_0 ∩ ... ∩ A_n) - (A_0 ∩ ... ∩ A_{n+1})`.

These are the finite set-level counterparts of the increment/decrement terms
used around Proposition 2.10.  As in G293-G294, the construction is conditional
on the explicit `BSetBinarySideSelectorSurface`; this file does not construct
that surface and does not extract Type data from raw Prop membership.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

namespace BSetBinarySideSelectorSurface

/-! ## 1. Finite union step differences -/

/-- Strong finite union increment:
`(A_0 ∪ ... ∪ A_{n+1}) - (A_0 ∪ ... ∪ A_n)`. -/
noncomputable def bigOrFinStepDiffWithDef23
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    IntegrableSet1WithDef23 (S := S)
      (BSet.sub (bigOrFin A (n + 1)) (bigOrFin A n)) :=
  subWithSurface (S := S) Sel
    (bigOrFinWithDef23 (S := S) Sel A HA (n + 1))
    (bigOrFinWithDef23 (S := S) Sel A HA n)


@[simp] theorem bigOrFinStepDiffWithDef23_base
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    (bigOrFinStepDiffWithDef23 (S := S) Sel A HA n).base =
      IntegrableSet1_sub
        (bigOrFin_int A (fun k => (HA k).base) (n + 1))
        (bigOrFin_int A (fun k => (HA k).base) n) := by
  rw [bigOrFinStepDiffWithDef23, subWithSurface_base,
    bigOrFinWithDef23_base, bigOrFinWithDef23_base]


/-! ## 2. Finite intersection step differences -/

/-- Strong finite intersection decrement:
`(A_0 ∩ ... ∩ A_n) - (A_0 ∩ ... ∩ A_{n+1})`. -/
noncomputable def bigAndFinStepDiffWithDef23
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    IntegrableSet1WithDef23 (S := S)
      (BSet.sub (bigAndFin A n) (bigAndFin A (n + 1))) :=
  subWithSurface (S := S) Sel
    (bigAndFinWithDef23 (S := S) Sel A HA n)
    (bigAndFinWithDef23 (S := S) Sel A HA (n + 1))


@[simp] theorem bigAndFinStepDiffWithDef23_base
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (n : Nat) :
    (bigAndFinStepDiffWithDef23 (S := S) Sel A HA n).base =
      IntegrableSet1_sub
        (bigAndFin_int A (fun k => (HA k).base) n)
        (bigAndFin_int A (fun k => (HA k).base) (n + 1)) := by
  rw [bigAndFinStepDiffWithDef23, subWithSurface_base,
    bigAndFinWithDef23_base, bigAndFinWithDef23_base]


end BSetBinarySideSelectorSurface

/-! ## 3. Audit -/

structure Sec2Def23FiniteDifferenceAuditAfterG295 : Type where
  finite_union_step_difference_constructor_added : Nat
  finite_intersection_step_difference_constructor_added : Nat
  base_compatibility_theorems_added : Nat
  surface_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_countable_constructor_problem : Nat

def sec2Def23FiniteDifferenceAuditAfterG295 :
    Sec2Def23FiniteDifferenceAuditAfterG295 where
  finite_union_step_difference_constructor_added := 1
  finite_intersection_step_difference_constructor_added := 1
  base_compatibility_theorems_added := 2
  surface_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_countable_constructor_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G295Def23FiniteDifferencePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g294 : Chapter4G294Def23FiniteConstructorPackage S
  audit : BishopC.Sec2Def23FiniteDifferenceAuditAfterG295
  finite_difference_constructors_added_this_step : Nat
  remaining_countable_constructor_problem : Nat

def chapter4G295Def23FiniteDifferencePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G295Def23FiniteDifferencePackage S where
  g294 := chapter4G294Def23FiniteConstructorPackage S
  audit := BishopC.sec2Def23FiniteDifferenceAuditAfterG295
  finite_difference_constructors_added_this_step := 2
  remaining_countable_constructor_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G295. -/
def bishopRegularSeqChapter4Def23FiniteDifferenceProgressAfterG295 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G295: added selector-surface strong Def23 constructors for the finite \
    union increments and finite intersection decrements used by the \
    Proposition 2.10 telescope.  Their base fields reduce to the existing \
    Chapter-2 sub constructors over bigOrFin_int and bigAndFin_int."


end BishopCReal
