import Mathdemo.Internal.CRat_iter390

set_option linter.style.longLine false

/-!
# G292: selector-parametrized strong binary constructors

G290 established the choice-free `Nonempty`/Prop-level constructor API.  G291
added Type-coded side certificates that recover actual `SeriesSum` data when a
specific side case is available.

This node puts those pieces together.  It gives strong
`IntegrableSet1WithDef23` constructors for `or`, `and`, and relative `sub`,
but only when the missing disjunctive side case is supplied as explicit Type
data by a selector argument.  The selector is not constructed here; this node
therefore does not perform raw Prop-to-Type extraction and does not add choice.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

namespace IntegrableSet1WithDef23

/-! ## 1. Strong `or` from an explicit positive-side selector -/

/-- Strong binary union from explicit Type-coded positive-side cases. -/
noncomputable def orOfS1Selector
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    (s1Case : forall {x : X}, x ∈ (BSet.or A B).S1 -> OrS1Case A B x) :
    IntegrableSet1WithDef23 (S := S) (BSet.or A B) where
  base := IntegrableSet1_or HA.base HB.base
  dom_on_s1 := by
    intro x hx m
    change x ∈ (((HA.base.rep.add HB.base.rep).sub
      (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).dom
    exact OrS1Case.outputDom (S := S) HA HB (s1Case hx) m
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
    change RSeq.SeriesSum
      (fun m => COF.abs ((((HA.base.rep.add HB.base.rep).sub
        (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).toFun x))
    exact OrS1Case.outputAbs (S := S) HA HB (s1Case hx)
  abs_on_s2 := by
    intro x hx
    have hAabs : RSeq.SeriesSum
        (fun k => COF.abs ((HA.base.rep.fn k).toFun x)) :=
      HA.abs_on_s2 x hx.1
    have hBabs : RSeq.SeriesSum
        (fun k => COF.abs ((HB.base.rep.fn k).toFun x)) :=
      HB.abs_on_s2 x hx.2
    change RSeq.SeriesSum
      (fun m => COF.abs ((((HA.base.rep.add HB.base.rep).sub
        (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).toFun x))
    exact sub_absSeriesSum_of_left_right
      (add_absSeriesSum_of_left_right hAabs hBabs)
      (min2_absSeriesSum_of_left_right hAabs hBabs)


@[simp] theorem orOfS1Selector_base
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    (s1Case : forall {x : X}, x ∈ (BSet.or A B).S1 -> OrS1Case A B x) :
    (orOfS1Selector (S := S) HA HB s1Case).base =
      IntegrableSet1_or HA.base HB.base :=
  rfl


/-! ## 2. Strong `and` from an explicit negative-side selector -/

/-- Strong binary intersection from explicit Type-coded negative-side cases. -/
noncomputable def andOfS2Selector
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    (s2Case : forall {x : X}, x ∈ (BSet.and A B).S2 -> AndS2Case A B x) :
    IntegrableSet1WithDef23 (S := S) (BSet.and A B) where
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
    change x ∈ ((IntegrableRep.min2 HA.base.rep HB.base.rep).fn m).dom
    exact AndS2Case.outputDom (S := S) HA HB (s2Case hx) m
  abs_on_s1 := by
    intro x hx
    have hAabs : RSeq.SeriesSum
        (fun k => COF.abs ((HA.base.rep.fn k).toFun x)) :=
      HA.abs_on_s1 x hx.1
    have hBabs : RSeq.SeriesSum
        (fun k => COF.abs ((HB.base.rep.fn k).toFun x)) :=
      HB.abs_on_s1 x hx.2
    change RSeq.SeriesSum
      (fun m => COF.abs (((IntegrableRep.min2 HA.base.rep HB.base.rep).fn m).toFun x))
    exact min2_absSeriesSum_of_left_right hAabs hBabs
  abs_on_s2 := by
    intro x hx
    change RSeq.SeriesSum
      (fun m => COF.abs (((IntegrableRep.min2 HA.base.rep HB.base.rep).fn m).toFun x))
    exact AndS2Case.outputAbs (S := S) HA HB (s2Case hx)


@[simp] theorem andOfS2Selector_base
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    (s2Case : forall {x : X}, x ∈ (BSet.and A B).S2 -> AndS2Case A B x) :
    (andOfS2Selector (S := S) HA HB s2Case).base =
      IntegrableSet1_and HA.base HB.base :=
  rfl


/-! ## 3. Strong relative `sub` from an explicit negative-side selector -/

/-- Strong relative subtraction from explicit Type-coded negative-side cases. -/
noncomputable def subOfS2Selector
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    (s2Case : forall {x : X}, x ∈ (BSet.sub A B).S2 -> SubS2Case A B x) :
    IntegrableSet1WithDef23 (S := S) (BSet.sub A B) where
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
    change x ∈ ((HA.base.rep.sub
      (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).dom
    exact SubS2Case.outputDom (S := S) HA HB (s2Case hx) m
  abs_on_s1 := by
    intro x hx
    have hAabs : RSeq.SeriesSum
        (fun k => COF.abs ((HA.base.rep.fn k).toFun x)) :=
      HA.abs_on_s1 x hx.1
    have hBabs : RSeq.SeriesSum
        (fun k => COF.abs ((HB.base.rep.fn k).toFun x)) :=
      HB.abs_on_s2 x hx.2
    change RSeq.SeriesSum
      (fun m => COF.abs (((HA.base.rep.sub
        (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).toFun x))
    exact sub_absSeriesSum_of_left_right hAabs
      (min2_absSeriesSum_of_left_right hAabs hBabs)
  abs_on_s2 := by
    intro x hx
    change RSeq.SeriesSum
      (fun m => COF.abs (((HA.base.rep.sub
        (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).toFun x))
    exact SubS2Case.outputAbs (S := S) HA HB (s2Case hx)


@[simp] theorem subOfS2Selector_base
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    (s2Case : forall {x : X}, x ∈ (BSet.sub A B).S2 -> SubS2Case A B x) :
    (subOfS2Selector (S := S) HA HB s2Case).base =
      IntegrableSet1_sub HA.base HB.base :=
  rfl


end IntegrableSet1WithDef23

/-! ## 4. Audit -/

structure Sec2Def23SelectorStrongConstructorAuditAfterG292 : Type where
  selector_parametrized_strong_constructors_added : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  broad_base_structure_modified : Nat
  external_choice_principle_added : Nat
  remaining_selector_construction_problem : Nat

def sec2Def23SelectorStrongConstructorAuditAfterG292 :
    Sec2Def23SelectorStrongConstructorAuditAfterG292 where
  selector_parametrized_strong_constructors_added := 3
  raw_prop_membership_to_type_extraction_used := 0
  broad_base_structure_modified := 0
  external_choice_principle_added := 0
  remaining_selector_construction_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G292Def23SelectorStrongConstructorPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g291 : Chapter4G291Def23TypeCodedSideCertificatePackage S
  audit : BishopC.Sec2Def23SelectorStrongConstructorAuditAfterG292
  selector_parametrized_strong_constructors_added_this_step : Nat
  remaining_selector_construction_problem : Nat

def chapter4G292Def23SelectorStrongConstructorPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G292Def23SelectorStrongConstructorPackage S where
  g291 := chapter4G291Def23TypeCodedSideCertificatePackage S
  audit := BishopC.sec2Def23SelectorStrongConstructorAuditAfterG292
  selector_parametrized_strong_constructors_added_this_step := 3
  remaining_selector_construction_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G292. -/
def bishopRegularSeqChapter4Def23SelectorStrongConstructorProgressAfterG292 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G292: added strong IntegrableSet1WithDef23 constructors for or, and, and \
    relative sub, parameterized by explicit Type-coded side selectors.  This \
    recovers the strong API when side data is supplied, while preserving the \
    G290/G291 frontier that raw Prop membership alone cannot produce SeriesSum \
    data without an additional selector."


end BishopCReal
