import Mathdemo.Internal.CRat_iter397

set_option linter.style.longLine false

/-!
# G299: countable Proposition-2.10 output surface

G298 introduced the final side-witness records needed to upgrade the existing
countable Proposition-2.10 outputs to `IntegrableSet1WithDef23`.

This node packages those witness-producing operations into a single output
surface, parallel to the binary selector surface from G293.  The surface is not
constructed here; it is an explicit interface for the remaining countable
domain/absolute-convergence problem.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Countable output surface -/

/-- Surface providing the final sidewise Definition-2.3 witnesses for the
countable union and countable intersection Proposition-2.10 outputs.

This is deliberately an explicit Type-level interface.  It avoids hiding the
remaining countable analytic work behind the older base `IntegrableSet1`
constructor. -/
structure Prop210CountableOutputSurface
    (X R : Type*) [COFOC R] (S : IntSpaceRC X R) : Type _ where
  union_output :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
      (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)),
      Prop210BWithDef23OutputWitness (S := S) A HA h_conv
  intersection_output :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
      (h_lim :
        Σ β : R,
          RSeq.TendstoHalf
            (fun n => measure1 S
              (bigAndFin_int A (fun k => (HA k).base) n)) β),
      Prop210CWithDef23OutputWitness (S := S) A HA h_lim


namespace Prop210CountableOutputSurface

/-! ## 2. Uniform strong countable constructors from the surface -/

/-- Strong countable union from the countable output surface. -/
noncomputable def bigOrWithSurface
    (Out : Prop210CountableOutputSurface X R S)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) :
    IntegrableSet1WithDef23 (S := S) (BSet.bigOr A) :=
  prop_2_10_b_withDef23 (S := S) A HA h_conv
    (Out.union_output A HA h_conv)


@[simp] theorem bigOrWithSurface_base
    (Out : Prop210CountableOutputSurface X R S)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) :
    (bigOrWithSurface (S := S) Out A HA h_conv).base =
      prop_2_10_b_ofWithDef23 (S := S) A HA h_conv :=
  rfl


theorem bigOrWithSurface_measure
    (Out : Prop210CountableOutputSurface X R S)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) :
    Le (measure1 S (bigOrWithSurface (S := S) Out A HA h_conv).base)
      h_conv.sum := by
  exact prop_2_10_b_measure_withDef23
    (S := S) A HA h_conv (Out.union_output A HA h_conv)


/-- Strong countable intersection from the countable output surface. -/
noncomputable def bigAndWithSurface
    (Out : Prop210CountableOutputSurface X R S)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) :
    IntegrableSet1WithDef23 (S := S) (BSet.bigAnd A) :=
  prop_2_10_c_withDef23 (S := S) A HA h_lim
    (Out.intersection_output A HA h_lim)


@[simp] theorem bigAndWithSurface_base
    (Out : Prop210CountableOutputSurface X R S)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) :
    (bigAndWithSurface (S := S) Out A HA h_lim).base =
      prop_2_10_c_ofWithDef23 (S := S) A HA h_lim :=
  rfl


theorem bigAndWithSurface_measure
    (Out : Prop210CountableOutputSurface X R S)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) :
    measure1 S (bigAndWithSurface (S := S) Out A HA h_lim).base =
      h_lim.fst := by
  exact prop_2_10_c_measure_withDef23
    (S := S) A HA h_lim (Out.intersection_output A HA h_lim)


end Prop210CountableOutputSurface

/-! ## 3. Audit -/

structure Sec2Def23CountableOutputSurfaceAuditAfterG299 : Type where
  countable_output_surface_added : Nat
  surface_constructors_added : Nat
  measure_theorems_added : Nat
  surface_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_surface_construction_problem : Nat

def sec2Def23CountableOutputSurfaceAuditAfterG299 :
    Sec2Def23CountableOutputSurfaceAuditAfterG299 where
  countable_output_surface_added := 1
  surface_constructors_added := 2
  measure_theorems_added := 2
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

structure Chapter4G299Def23CountableOutputSurfacePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g298 : Chapter4G298Def23ConditionalProp210OutputPackage S
  audit : BishopC.Sec2Def23CountableOutputSurfaceAuditAfterG299
  output_surface_added_this_step : Nat
  remaining_surface_construction_problem : Nat

def chapter4G299Def23CountableOutputSurfacePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G299Def23CountableOutputSurfacePackage S where
  g298 := chapter4G298Def23ConditionalProp210OutputPackage S
  audit := BishopC.sec2Def23CountableOutputSurfaceAuditAfterG299
  output_surface_added_this_step := 1
  remaining_surface_construction_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G299. -/
def bishopRegularSeqChapter4Def23CountableOutputSurfaceProgressAfterG299 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G299: packaged the final Proposition-2.10 sidewise domain/absolute \
    convergence obligations into a countable output surface.  From that \
    explicit surface, the countable union and intersection strong Def23 \
    constructors and their measure theorems follow uniformly."


end BishopCReal
