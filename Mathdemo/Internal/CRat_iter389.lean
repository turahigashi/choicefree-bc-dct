import Mathdemo.Internal.CRat_iter388

set_option linter.style.longLine false

/-!
# G290: binary constructor frontier for Definition-2.3 local data

G288 introduced the strong local API `IntegrableSet1WithDef23`, whose
absolute-convergence fields return actual `RSeq.SeriesSum` data.  G289 added
the forward transport lemmas needed by the Chapter-2 binary constructors.

Attempting to build `IntegrableSet1WithDef23 (BSet.or A B)` directly exposes a
constructive boundary: membership in `(A or B).S1` is a Prop-valued disjunction,
whereas `RSeq.SeriesSum` is Type-valued data with a modulus.  Eliminating that
disjunction into `SeriesSum` would be a Prop-to-Type extraction.  This node
therefore records the conservative, choice-free repair: keep domain fields as
ordinary Prop-valued data, and lower the absolute-convergence fields to
`Nonempty (RSeq.SeriesSum ...)`.  The resulting Prop-level API is closed under
the binary constructors without adding choice.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Prop-level Definition-2.3 absolute-convergence API -/

/-- A choice-free Prop-level variant of the local Definition-2.3 API.

The domain fields remain the same.  The absolute-convergence fields are lowered
to `Nonempty` so that disjunctive side membership can be eliminated only into
Prop.  This avoids extracting a concrete convergence modulus from a proof-only
case split. -/
structure IntegrableSet1WithDef23PropAbs
    (S : IntSpaceRC X R) (A : BSet X) : Type _ where
  base : IntegrableSet1 S A
  dom_on_s1 :
    forall x : X, x ∈ A.S1 ->
      forall m : Nat, x ∈ (base.rep.fn m).dom
  dom_on_s2 :
    forall x : X, x ∈ A.S2 ->
      forall m : Nat, x ∈ (base.rep.fn m).dom
  abs_on_s1 :
    forall x : X, x ∈ A.S1 ->
      Nonempty (RSeq.SeriesSum (fun m => COF.abs (((base.rep.fn m).toFun x))))
  abs_on_s2 :
    forall x : X, x ∈ A.S2 ->
      Nonempty (RSeq.SeriesSum (fun m => COF.abs (((base.rep.fn m).toFun x))))


namespace IntegrableSet1WithDef23PropAbs

/-- Every strong local Definition-2.3 object gives the Prop-level variant. -/
def ofStrong
    {A : BSet X} (H : IntegrableSet1WithDef23 (S := S) A) :
    IntegrableSet1WithDef23PropAbs (S := S) A where
  base := H.base
  dom_on_s1 := H.dom_on_s1
  dom_on_s2 := H.dom_on_s2
  abs_on_s1 := fun x hx => ⟨H.abs_on_s1 x hx⟩
  abs_on_s2 := fun x hx => ⟨H.abs_on_s2 x hx⟩


/-! ## 2. Side extraction for `or` -/

theorem or_s1_left_dom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.or A B).S1) :
    forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
  intro k
  rcases hx with (hx11 | hx12) | hx21
  · exact HA.dom_on_s1 x hx11.1 k
  · exact HA.dom_on_s1 x hx12.1 k
  · exact HA.dom_on_s2 x hx21.1 k


theorem or_s1_right_dom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.or A B).S1) :
    forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
  intro k
  rcases hx with (hx11 | hx12) | hx21
  · exact HB.dom_on_s1 x hx11.2 k
  · exact HB.dom_on_s2 x hx12.2 k
  · exact HB.dom_on_s1 x hx21.2 k


theorem or_s1_left_abs_exists
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.or A B).S1) :
    Nonempty (RSeq.SeriesSum (fun k => COF.abs ((HA.base.rep.fn k).toFun x))) := by
  rcases hx with (hx11 | hx12) | hx21
  · exact HA.abs_on_s1 x hx11.1
  · exact HA.abs_on_s1 x hx12.1
  · exact HA.abs_on_s2 x hx21.1


theorem or_s1_right_abs_exists
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.or A B).S1) :
    Nonempty (RSeq.SeriesSum (fun k => COF.abs ((HB.base.rep.fn k).toFun x))) := by
  rcases hx with (hx11 | hx12) | hx21
  · exact HB.abs_on_s1 x hx11.2
  · exact HB.abs_on_s2 x hx12.2
  · exact HB.abs_on_s1 x hx21.2


/-! ## 3. Prop-level strengthened `or` constructor -/

/-- Binary union preserves the Prop-level Definition-2.3 API. -/
noncomputable def or
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B) :
    IntegrableSet1WithDef23PropAbs (S := S) (BSet.or A B) where
  base := IntegrableSet1_or HA.base HB.base
  dom_on_s1 := by
    intro x hx m
    have hAdom := or_s1_left_dom (S := S) HA HB hx
    have hBdom := or_s1_right_dom (S := S) HA HB hx
    change x ∈ (((HA.base.rep.add HB.base.rep).sub
      (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).dom
    exact sub_dom_of_left_right
      (add_dom_of_left_right hAdom hBdom)
      (min2_dom_of_left_right hAdom hBdom) m
  dom_on_s2 := by
    intro x hx m
    have hAdom : forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
      intro k
      exact HA.dom_on_s2 x hx.1 k
    have hBdom : forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
      intro k
      exact HB.dom_on_s2 x hx.2 k
    change x ∈ (((HA.base.rep.add HB.base.rep).sub
      (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).dom
    exact sub_dom_of_left_right
      (add_dom_of_left_right hAdom hBdom)
      (min2_dom_of_left_right hAdom hBdom) m
  abs_on_s1 := by
    intro x hx
    rcases or_s1_left_abs_exists (S := S) HA HB hx with ⟨hAabs⟩
    rcases or_s1_right_abs_exists (S := S) HA HB hx with ⟨hBabs⟩
    exact ⟨by
      change RSeq.SeriesSum
        (fun m => COF.abs ((((HA.base.rep.add HB.base.rep).sub
          (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).toFun x))
      exact sub_absSeriesSum_of_left_right
        (add_absSeriesSum_of_left_right hAabs hBabs)
        (min2_absSeriesSum_of_left_right hAabs hBabs)⟩
  abs_on_s2 := by
    intro x hx
    rcases HA.abs_on_s2 x hx.1 with ⟨hAabs⟩
    rcases HB.abs_on_s2 x hx.2 with ⟨hBabs⟩
    exact ⟨by
      change RSeq.SeriesSum
        (fun m => COF.abs ((((HA.base.rep.add HB.base.rep).sub
          (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).toFun x))
      exact sub_absSeriesSum_of_left_right
        (add_absSeriesSum_of_left_right hAabs hBabs)
        (min2_absSeriesSum_of_left_right hAabs hBabs)⟩


@[simp] theorem or_base
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B) :
    (or (S := S) HA HB).base = IntegrableSet1_or HA.base HB.base :=
  rfl


/-! ## 4. Side extraction for `and` -/

theorem and_s2_left_dom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.and A B).S2) :
    forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
  intro k
  rcases hx with (hx12 | hx21) | hx22
  · exact HA.dom_on_s1 x hx12.1 k
  · exact HA.dom_on_s2 x hx21.1 k
  · exact HA.dom_on_s2 x hx22.1 k


theorem and_s2_right_dom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.and A B).S2) :
    forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
  intro k
  rcases hx with (hx12 | hx21) | hx22
  · exact HB.dom_on_s2 x hx12.2 k
  · exact HB.dom_on_s1 x hx21.2 k
  · exact HB.dom_on_s2 x hx22.2 k


theorem and_s2_left_abs_exists
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.and A B).S2) :
    Nonempty (RSeq.SeriesSum (fun k => COF.abs ((HA.base.rep.fn k).toFun x))) := by
  rcases hx with (hx12 | hx21) | hx22
  · exact HA.abs_on_s1 x hx12.1
  · exact HA.abs_on_s2 x hx21.1
  · exact HA.abs_on_s2 x hx22.1


theorem and_s2_right_abs_exists
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.and A B).S2) :
    Nonempty (RSeq.SeriesSum (fun k => COF.abs ((HB.base.rep.fn k).toFun x))) := by
  rcases hx with (hx12 | hx21) | hx22
  · exact HB.abs_on_s2 x hx12.2
  · exact HB.abs_on_s1 x hx21.2
  · exact HB.abs_on_s2 x hx22.2


/-! ## 5. Prop-level strengthened `and` constructor -/

/-- Binary intersection preserves the Prop-level Definition-2.3 API. -/
noncomputable def and
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B) :
    IntegrableSet1WithDef23PropAbs (S := S) (BSet.and A B) where
  base := IntegrableSet1_and HA.base HB.base
  dom_on_s1 := by
    intro x hx m
    have hAdom : forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
      intro k
      exact HA.dom_on_s1 x hx.1 k
    have hBdom : forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
      intro k
      exact HB.dom_on_s1 x hx.2 k
    change x ∈ ((IntegrableRep.min2 HA.base.rep HB.base.rep).fn m).dom
    exact min2_dom_of_left_right hAdom hBdom m
  dom_on_s2 := by
    intro x hx m
    have hAdom := and_s2_left_dom (S := S) HA HB hx
    have hBdom := and_s2_right_dom (S := S) HA HB hx
    change x ∈ ((IntegrableRep.min2 HA.base.rep HB.base.rep).fn m).dom
    exact min2_dom_of_left_right hAdom hBdom m
  abs_on_s1 := by
    intro x hx
    rcases HA.abs_on_s1 x hx.1 with ⟨hAabs⟩
    rcases HB.abs_on_s1 x hx.2 with ⟨hBabs⟩
    exact ⟨by
      change RSeq.SeriesSum
        (fun m => COF.abs (((IntegrableRep.min2 HA.base.rep HB.base.rep).fn m).toFun x))
      exact min2_absSeriesSum_of_left_right hAabs hBabs⟩
  abs_on_s2 := by
    intro x hx
    rcases and_s2_left_abs_exists (S := S) HA HB hx with ⟨hAabs⟩
    rcases and_s2_right_abs_exists (S := S) HA HB hx with ⟨hBabs⟩
    exact ⟨by
      change RSeq.SeriesSum
        (fun m => COF.abs (((IntegrableRep.min2 HA.base.rep HB.base.rep).fn m).toFun x))
      exact min2_absSeriesSum_of_left_right hAabs hBabs⟩


@[simp] theorem and_base
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B) :
    (and (S := S) HA HB).base = IntegrableSet1_and HA.base HB.base :=
  rfl


/-! ## 6. Side extraction for relative `sub` -/

theorem sub_s2_left_dom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.sub A B).S2) :
    forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
  intro k
  rcases hx with (hx11 | hx22) | hx21
  · exact HA.dom_on_s1 x hx11.1 k
  · exact HA.dom_on_s2 x hx22.1 k
  · exact HA.dom_on_s2 x hx21.1 k


theorem sub_s2_right_dom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.sub A B).S2) :
    forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
  intro k
  rcases hx with (hx11 | hx22) | hx21
  · exact HB.dom_on_s1 x hx11.2 k
  · exact HB.dom_on_s2 x hx22.2 k
  · exact HB.dom_on_s1 x hx21.2 k


theorem sub_s2_left_abs_exists
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.sub A B).S2) :
    Nonempty (RSeq.SeriesSum (fun k => COF.abs ((HA.base.rep.fn k).toFun x))) := by
  rcases hx with (hx11 | hx22) | hx21
  · exact HA.abs_on_s1 x hx11.1
  · exact HA.abs_on_s2 x hx22.1
  · exact HA.abs_on_s2 x hx21.1


theorem sub_s2_right_abs_exists
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B)
    {x : X}
    (hx : x ∈ (BSet.sub A B).S2) :
    Nonempty (RSeq.SeriesSum (fun k => COF.abs ((HB.base.rep.fn k).toFun x))) := by
  rcases hx with (hx11 | hx22) | hx21
  · exact HB.abs_on_s1 x hx11.2
  · exact HB.abs_on_s2 x hx22.2
  · exact HB.abs_on_s1 x hx21.2


/-! ## 7. Prop-level strengthened relative subtraction constructor -/

/-- Relative subtraction preserves the Prop-level Definition-2.3 API. -/
noncomputable def sub
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B) :
    IntegrableSet1WithDef23PropAbs (S := S) (BSet.sub A B) where
  base := IntegrableSet1_sub HA.base HB.base
  dom_on_s1 := by
    intro x hx m
    have hAdom : forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
      intro k
      exact HA.dom_on_s1 x hx.1 k
    have hBdom : forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
      intro k
      exact HB.dom_on_s2 x hx.2 k
    change x ∈ ((HA.base.rep.sub
      (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).dom
    exact sub_dom_of_left_right hAdom (min2_dom_of_left_right hAdom hBdom) m
  dom_on_s2 := by
    intro x hx m
    have hAdom := sub_s2_left_dom (S := S) HA HB hx
    have hBdom := sub_s2_right_dom (S := S) HA HB hx
    change x ∈ ((HA.base.rep.sub
      (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).dom
    exact sub_dom_of_left_right hAdom (min2_dom_of_left_right hAdom hBdom) m
  abs_on_s1 := by
    intro x hx
    rcases HA.abs_on_s1 x hx.1 with ⟨hAabs⟩
    rcases HB.abs_on_s2 x hx.2 with ⟨hBabs⟩
    exact ⟨by
      change RSeq.SeriesSum
        (fun m => COF.abs (((HA.base.rep.sub
          (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).toFun x))
      exact sub_absSeriesSum_of_left_right hAabs
        (min2_absSeriesSum_of_left_right hAabs hBabs)⟩
  abs_on_s2 := by
    intro x hx
    rcases sub_s2_left_abs_exists (S := S) HA HB hx with ⟨hAabs⟩
    rcases sub_s2_right_abs_exists (S := S) HA HB hx with ⟨hBabs⟩
    exact ⟨by
      change RSeq.SeriesSum
        (fun m => COF.abs (((HA.base.rep.sub
          (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).toFun x))
      exact sub_absSeriesSum_of_left_right hAabs
        (min2_absSeriesSum_of_left_right hAabs hBabs)⟩


@[simp] theorem sub_base
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23PropAbs (S := S) A)
    (HB : IntegrableSet1WithDef23PropAbs (S := S) B) :
    (sub (S := S) HA HB).base = IntegrableSet1_sub HA.base HB.base :=
  rfl


end IntegrableSet1WithDef23PropAbs

/-! ## 8. Audit -/

structure Sec2Def23BinaryConstructorFrontierAuditAfterG290 : Type where
  direct_type_abs_constructor_added : Nat
  prop_abs_constructor_added : Nat
  prop_to_type_obstruction_recorded : Nat
  broad_base_structure_modified : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_global_base_refactor_steps : Nat

def sec2Def23BinaryConstructorFrontierAuditAfterG290 :
    Sec2Def23BinaryConstructorFrontierAuditAfterG290 where
  direct_type_abs_constructor_added := 0
  prop_abs_constructor_added := 3
  prop_to_type_obstruction_recorded := 1
  broad_base_structure_modified := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_global_base_refactor_steps := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G290Def23BinaryConstructorFrontierPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g289 : Chapter4G289Def23ConstructorTransportPackage S
  audit : BishopC.Sec2Def23BinaryConstructorFrontierAuditAfterG290
  prop_abs_binary_constructors_added_this_step : Nat
  remaining_global_base_refactor_steps : Nat

def chapter4G290Def23BinaryConstructorFrontierPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G290Def23BinaryConstructorFrontierPackage S where
  g289 := chapter4G289Def23ConstructorTransportPackage S
  audit := BishopC.sec2Def23BinaryConstructorFrontierAuditAfterG290
  prop_abs_binary_constructors_added_this_step := 3
  remaining_global_base_refactor_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G290. -/
def bishopRegularSeqChapter4Def23BinaryConstructorFrontierProgressAfterG290 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G290: formalized the binary-constructor frontier for local Definition-2.3 \
    data.  Direct Type-valued abs constructors for disjunctive sides would \
    require Prop-to-Type extraction, so this node adds the choice-free \
    Nonempty/Prop-level API and proves closure for or, and, and relative sub."


end BishopCReal
