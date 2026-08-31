import Mathdemo.Internal.Measure.BinaryConstructorFrontierDefinition23

set_option linter.style.longLine false

/-!
# G291: Type-coded side certificates for binary Definition-2.3 data

G290 showed the obstruction: a raw proof `x in (A or B).S1` is Prop-valued and
cannot be case-split to produce concrete `RSeq.SeriesSum` data.  This node adds
the constructive replacement for places that truly need Type data: explicit
Type-coded side certificates for the disjunctive sides of the binary
constructors.

With these certificates, actual domain and absolute-convergence data can be
transported without choice.  This does not yet rewrite the broad
`IntegrableSet1` structure; it records the source-faithful interface needed for
the next refactor.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Type-coded side certificates -/

/-- Type-coded cases for the positive side of `A or B`. -/
inductive OrS1Case (A B : BSet X) (x : X) : Type _ where
  | both : x ∈ A.S1 -> x ∈ B.S1 -> OrS1Case A B x
  | leftOnly : x ∈ A.S1 -> x ∈ B.S2 -> OrS1Case A B x
  | rightOnly : x ∈ A.S2 -> x ∈ B.S1 -> OrS1Case A B x


/-- Type-coded cases for the negative side of `A and B`. -/
inductive AndS2Case (A B : BSet X) (x : X) : Type _ where
  | leftOnly : x ∈ A.S1 -> x ∈ B.S2 -> AndS2Case A B x
  | rightOnly : x ∈ A.S2 -> x ∈ B.S1 -> AndS2Case A B x
  | neither : x ∈ A.S2 -> x ∈ B.S2 -> AndS2Case A B x


/-- Type-coded cases for the negative side of `A sub B`. -/
inductive SubS2Case (A B : BSet X) (x : X) : Type _ where
  | both : x ∈ A.S1 -> x ∈ B.S1 -> SubS2Case A B x
  | neither : x ∈ A.S2 -> x ∈ B.S2 -> SubS2Case A B x
  | leftFalse : x ∈ A.S2 -> x ∈ B.S1 -> SubS2Case A B x


namespace OrS1Case

def toMem {A B : BSet X} {x : X} (c : OrS1Case A B x) :
    x ∈ (BSet.or A B).S1 := by
  cases c with
  | both ha hb => exact Or.inl (Or.inl ⟨ha, hb⟩)
  | leftOnly ha hb => exact Or.inl (Or.inr ⟨ha, hb⟩)
  | rightOnly ha hb => exact Or.inr ⟨ha, hb⟩


theorem leftDom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    {x : X} (c : OrS1Case A B x) :
    forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
  intro k
  cases c with
  | both ha hb => exact HA.dom_on_s1 x ha k
  | leftOnly ha hb => exact HA.dom_on_s1 x ha k
  | rightOnly ha hb => exact HA.dom_on_s2 x ha k


theorem rightDom
    {A B : BSet X}
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : OrS1Case A B x) :
    forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
  intro k
  cases c with
  | both ha hb => exact HB.dom_on_s1 x hb k
  | leftOnly ha hb => exact HB.dom_on_s2 x hb k
  | rightOnly ha hb => exact HB.dom_on_s1 x hb k


def leftAbs
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    {x : X} (c : OrS1Case A B x) :
    Sec4RepAbsAt HA.base.rep x := by
  cases c with
  | both ha hb => exact ⟨HA.dom_on_s1 x ha, HA.abs_on_s1 x ha⟩
  | leftOnly ha hb => exact ⟨HA.dom_on_s1 x ha, HA.abs_on_s1 x ha⟩
  | rightOnly ha hb => exact ⟨HA.dom_on_s2 x ha, HA.abs_on_s2 x ha⟩


def rightAbs
    {A B : BSet X}
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : OrS1Case A B x) :
    Sec4RepAbsAt HB.base.rep x := by
  cases c with
  | both ha hb => exact ⟨HB.dom_on_s1 x hb, HB.abs_on_s1 x hb⟩
  | leftOnly ha hb => exact ⟨HB.dom_on_s2 x hb, HB.abs_on_s2 x hb⟩
  | rightOnly ha hb => exact ⟨HB.dom_on_s1 x hb, HB.abs_on_s1 x hb⟩


theorem outputDom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : OrS1Case A B x) :
    forall m : Nat,
      x ∈ (((HA.base.rep.add HB.base.rep).sub
        (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).dom :=
  sub_dom_of_left_right
    (add_dom_of_left_right (leftDom (S := S) HA c) (rightDom (S := S) HB c))
    (min2_dom_of_left_right (leftDom (S := S) HA c) (rightDom (S := S) HB c))


noncomputable def outputAbs
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : OrS1Case A B x) :
    Sec4RepAbsAt ((HA.base.rep.add HB.base.rep).sub
      (IntegrableRep.min2 HA.base.rep HB.base.rep)) x :=
  sub_absSeriesSum_of_left_right
    (add_absSeriesSum_of_left_right (leftAbs (S := S) HA c) (rightAbs (S := S) HB c))
    (min2_absSeriesSum_of_left_right (leftAbs (S := S) HA c) (rightAbs (S := S) HB c))


end OrS1Case

namespace AndS2Case

def toMem {A B : BSet X} {x : X} (c : AndS2Case A B x) :
    x ∈ (BSet.and A B).S2 := by
  cases c with
  | leftOnly ha hb => exact Or.inl (Or.inl ⟨ha, hb⟩)
  | rightOnly ha hb => exact Or.inl (Or.inr ⟨ha, hb⟩)
  | neither ha hb => exact Or.inr ⟨ha, hb⟩


theorem leftDom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    {x : X} (c : AndS2Case A B x) :
    forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
  intro k
  cases c with
  | leftOnly ha hb => exact HA.dom_on_s1 x ha k
  | rightOnly ha hb => exact HA.dom_on_s2 x ha k
  | neither ha hb => exact HA.dom_on_s2 x ha k


theorem rightDom
    {A B : BSet X}
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : AndS2Case A B x) :
    forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
  intro k
  cases c with
  | leftOnly ha hb => exact HB.dom_on_s2 x hb k
  | rightOnly ha hb => exact HB.dom_on_s1 x hb k
  | neither ha hb => exact HB.dom_on_s2 x hb k


def leftAbs
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    {x : X} (c : AndS2Case A B x) :
    Sec4RepAbsAt HA.base.rep x := by
  cases c with
  | leftOnly ha hb => exact ⟨HA.dom_on_s1 x ha, HA.abs_on_s1 x ha⟩
  | rightOnly ha hb => exact ⟨HA.dom_on_s2 x ha, HA.abs_on_s2 x ha⟩
  | neither ha hb => exact ⟨HA.dom_on_s2 x ha, HA.abs_on_s2 x ha⟩


def rightAbs
    {A B : BSet X}
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : AndS2Case A B x) :
    Sec4RepAbsAt HB.base.rep x := by
  cases c with
  | leftOnly ha hb => exact ⟨HB.dom_on_s2 x hb, HB.abs_on_s2 x hb⟩
  | rightOnly ha hb => exact ⟨HB.dom_on_s1 x hb, HB.abs_on_s1 x hb⟩
  | neither ha hb => exact ⟨HB.dom_on_s2 x hb, HB.abs_on_s2 x hb⟩


theorem outputDom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : AndS2Case A B x) :
    forall m : Nat,
      x ∈ ((IntegrableRep.min2 HA.base.rep HB.base.rep).fn m).dom :=
  min2_dom_of_left_right (leftDom (S := S) HA c) (rightDom (S := S) HB c)


noncomputable def outputAbs
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : AndS2Case A B x) :
    Sec4RepAbsAt (IntegrableRep.min2 HA.base.rep HB.base.rep) x :=
  min2_absSeriesSum_of_left_right (leftAbs (S := S) HA c) (rightAbs (S := S) HB c)


end AndS2Case

namespace SubS2Case

def toMem {A B : BSet X} {x : X} (c : SubS2Case A B x) :
    x ∈ (BSet.sub A B).S2 := by
  cases c with
  | both ha hb => exact Or.inl (Or.inl ⟨ha, hb⟩)
  | neither ha hb => exact Or.inl (Or.inr ⟨ha, hb⟩)
  | leftFalse ha hb => exact Or.inr ⟨ha, hb⟩


theorem leftDom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    {x : X} (c : SubS2Case A B x) :
    forall k : Nat, x ∈ (HA.base.rep.fn k).dom := by
  intro k
  cases c with
  | both ha hb => exact HA.dom_on_s1 x ha k
  | neither ha hb => exact HA.dom_on_s2 x ha k
  | leftFalse ha hb => exact HA.dom_on_s2 x ha k


theorem rightDom
    {A B : BSet X}
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : SubS2Case A B x) :
    forall k : Nat, x ∈ (HB.base.rep.fn k).dom := by
  intro k
  cases c with
  | both ha hb => exact HB.dom_on_s1 x hb k
  | neither ha hb => exact HB.dom_on_s2 x hb k
  | leftFalse ha hb => exact HB.dom_on_s1 x hb k


def leftAbs
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    {x : X} (c : SubS2Case A B x) :
    Sec4RepAbsAt HA.base.rep x := by
  cases c with
  | both ha hb => exact ⟨HA.dom_on_s1 x ha, HA.abs_on_s1 x ha⟩
  | neither ha hb => exact ⟨HA.dom_on_s2 x ha, HA.abs_on_s2 x ha⟩
  | leftFalse ha hb => exact ⟨HA.dom_on_s2 x ha, HA.abs_on_s2 x ha⟩


def rightAbs
    {A B : BSet X}
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : SubS2Case A B x) :
    Sec4RepAbsAt HB.base.rep x := by
  cases c with
  | both ha hb => exact ⟨HB.dom_on_s1 x hb, HB.abs_on_s1 x hb⟩
  | neither ha hb => exact ⟨HB.dom_on_s2 x hb, HB.abs_on_s2 x hb⟩
  | leftFalse ha hb => exact ⟨HB.dom_on_s1 x hb, HB.abs_on_s1 x hb⟩


theorem outputDom
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : SubS2Case A B x) :
    forall m : Nat,
      x ∈ ((HA.base.rep.sub
        (IntegrableRep.min2 HA.base.rep HB.base.rep)).fn m).dom :=
  sub_dom_of_left_right
    (leftDom (S := S) HA c)
    (min2_dom_of_left_right (leftDom (S := S) HA c) (rightDom (S := S) HB c))


noncomputable def outputAbs
    {A B : BSet X}
    (HA : IntegrableSet1WithDef23 (S := S) A)
    (HB : IntegrableSet1WithDef23 (S := S) B)
    {x : X} (c : SubS2Case A B x) :
    Sec4RepAbsAt (HA.base.rep.sub
      (IntegrableRep.min2 HA.base.rep HB.base.rep)) x :=
  sub_absSeriesSum_of_left_right
    (leftAbs (S := S) HA c)
    (min2_absSeriesSum_of_left_right (leftAbs (S := S) HA c) (rightAbs (S := S) HB c))


end SubS2Case

/-! ## 2. Audit -/

structure Sec2Def23TypeCodedSideCertificateAuditAfterG291 : Type where
  type_coded_side_certificate_types_added : Nat
  actual_output_abs_constructors_added : Nat
  actual_output_dom_constructors_added : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_global_base_refactor_steps : Nat

def sec2Def23TypeCodedSideCertificateAuditAfterG291 :
    Sec2Def23TypeCodedSideCertificateAuditAfterG291 where
  type_coded_side_certificate_types_added := 3
  actual_output_abs_constructors_added := 3
  actual_output_dom_constructors_added := 3
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_global_base_refactor_steps := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G291Def23TypeCodedSideCertificatePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g290 : Chapter4G290Def23BinaryConstructorFrontierPackage S
  audit : BishopC.Sec2Def23TypeCodedSideCertificateAuditAfterG291
  type_coded_side_certificate_types_added_this_step : Nat
  remaining_global_base_refactor_steps : Nat

def chapter4G291Def23TypeCodedSideCertificatePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G291Def23TypeCodedSideCertificatePackage S where
  g290 := chapter4G290Def23BinaryConstructorFrontierPackage S
  audit := BishopC.sec2Def23TypeCodedSideCertificateAuditAfterG291
  type_coded_side_certificate_types_added_this_step := 3
  remaining_global_base_refactor_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G291. -/
def bishopRegularSeqChapter4Def23TypeCodedSideCertificateProgressAfterG291 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G291: added Type-coded side certificates for the disjunctive sides of \
    binary set constructors.  These certificates recover actual domain and \
    SeriesSum data without raw Prop-to-Type extraction, complementing the \
    Nonempty/Prop-level closure from G290."


end BishopCReal
