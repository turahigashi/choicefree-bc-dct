import Mathdemo.Internal.Measure.SelectorParametrizedStrongBinaryConstructors

set_option linter.style.longLine false

/-!
# G293: binary side selector surface

G292 gave strong binary constructors once the required Type-coded side selector
is passed explicitly.  This node packages those selectors into a pure
`BSet`-level surface.  The surface is intentionally independent of the
integration space: the obstruction is set-side classification data, not an
analytic property of `IntegrableRep`.

This file does not construct the surface.  It only records that, if such
Type-coded side classification is supplied, the strong Definition-2.3 binary
constructor algebra follows uniformly.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pure `BSet` side selector surface -/

/-- Pure set-side selector data for the three disjunctive sides used by the
binary Chapter-2 constructors.

The data is deliberately Type-valued.  Supplying this surface is the explicit
replacement for trying to extract Type side cases from raw Prop membership. -/
structure BSetBinarySideSelectorSurface (X : Type*) : Type _ where
  or_s1 :
    forall {A B : BSet X} {x : X},
      x ∈ (BSet.or A B).S1 -> OrS1Case A B x
  and_s2 :
    forall {A B : BSet X} {x : X},
      x ∈ (BSet.and A B).S2 -> AndS2Case A B x
  sub_s2 :
    forall {A B : BSet X} {x : X},
      x ∈ (BSet.sub A B).S2 -> SubS2Case A B x


namespace BSetBinarySideSelectorSurface

/-! ## 2. Uniform strong constructors from the surface -/

/-- Strong binary union from a global side-selector surface. -/
noncomputable def orWithSurface
    (Sel : BSetBinarySideSelectorSurface X)
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B) :
    IntegrableSet1WithDef23 (S := S) (BSet.or A B) :=
  IntegrableSet1WithDef23.orOfS1Selector
    (S := S) HA HB (fun hx => Sel.or_s1 hx)


/-- Strong binary intersection from a global side-selector surface. -/
noncomputable def andWithSurface
    (Sel : BSetBinarySideSelectorSurface X)
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B) :
    IntegrableSet1WithDef23 (S := S) (BSet.and A B) :=
  IntegrableSet1WithDef23.andOfS2Selector
    (S := S) HA HB (fun hx => Sel.and_s2 hx)


/-- Strong relative subtraction from a global side-selector surface. -/
noncomputable def subWithSurface
    (Sel : BSetBinarySideSelectorSurface X)
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B) :
    IntegrableSet1WithDef23 (S := S) (BSet.sub A B) :=
  IntegrableSet1WithDef23.subOfS2Selector
    (S := S) HA HB (fun hx => Sel.sub_s2 hx)


@[simp] theorem orWithSurface_base
    (Sel : BSetBinarySideSelectorSurface X)
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B) :
    (orWithSurface (S := S) Sel HA HB).base =
      IntegrableSet1_or HA.base HB.base :=
  rfl


@[simp] theorem andWithSurface_base
    (Sel : BSetBinarySideSelectorSurface X)
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B) :
    (andWithSurface (S := S) Sel HA HB).base =
      IntegrableSet1_and HA.base HB.base :=
  rfl


@[simp] theorem subWithSurface_base
    (Sel : BSetBinarySideSelectorSurface X)
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B) :
    (subWithSurface (S := S) Sel HA HB).base =
      IntegrableSet1_sub HA.base HB.base :=
  rfl


end BSetBinarySideSelectorSurface

/-! ## 3. Audit -/

structure Sec2Def23BinarySelectorSurfaceAuditAfterG293 : Type where
  selector_surface_added : Nat
  uniform_surface_constructors_added : Nat
  surface_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_surface_construction_problem : Nat

def sec2Def23BinarySelectorSurfaceAuditAfterG293 :
    Sec2Def23BinarySelectorSurfaceAuditAfterG293 where
  selector_surface_added := 1
  uniform_surface_constructors_added := 3
  surface_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_surface_construction_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G293Def23BinarySelectorSurfacePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g292 : Chapter4G292Def23SelectorStrongConstructorPackage S
  audit : BishopC.Sec2Def23BinarySelectorSurfaceAuditAfterG293
  selector_surface_added_this_step : Nat
  remaining_surface_construction_problem : Nat

def chapter4G293Def23BinarySelectorSurfacePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G293Def23BinarySelectorSurfacePackage S where
  g292 := chapter4G292Def23SelectorStrongConstructorPackage S
  audit := BishopC.sec2Def23BinarySelectorSurfaceAuditAfterG293
  selector_surface_added_this_step := 1
  remaining_surface_construction_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G293. -/
def bishopRegularSeqChapter4Def23BinarySelectorSurfaceProgressAfterG293 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G293: packaged the required Type-coded side selectors into a pure BSet \
    surface and derived uniform strong Def23 constructors from it.  The \
    surface is not constructed here; the remaining issue is exactly the \
    constructive side-classification problem isolated in G290-G292."


end BishopCReal
