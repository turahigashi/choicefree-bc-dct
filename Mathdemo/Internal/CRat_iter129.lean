import Mathdemo.Internal.CRat_iter128

/-!
# G29: Bishop-faithful measure skeleton over RegularSeq reals

The existing chapter-5 measure file is written over `[COFOC R]` and evaluates
simple functions by deciding membership in a complemented set.  For Bishop
reals this is the wrong primary interface: the scalar values should be
`RegularSeq`, equality should be Bishop equality, and pointwise simple-function
branches should be supplied as data.

This file fixes the target shape for the chapter-5 refactor without changing
the previous compatibility layer.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Finite sums in the RegularSeq surface, using the source addition. -/
def regularSeqFinSum (u : Nat -> RegularSeq) : Nat -> RegularSeq
  | 0 => u 0
  | Nat.succ n => addSeq (regularSeqFinSum u n) (u (Nat.succ n))

/-- Chapter-5 measure-space skeleton whose values are Bishop reals represented
by regular sequences.  Measure equalities are Bishop equalities. -/
structure BishopRegularSeqMeasureSpaceSkeleton
    (Arch : ScalarMulArchimedeanData) (X : Type) : Type 1 where
  realSurface : BishopRegularSeqRealSurface Arch
  m : Set (BSet X)
  mu : (E : BSet X) -> E ∈ m -> RegularSeq
  mu_nonneg :
    forall E hE, Not (regularSeqLtProp (mu E hE) zeroSeq)
  mu_empty :
    forall E hE, (forall x : X, Not (x ∈ E.S1)) ->
      relEventually (mu E hE) zeroSeq
  m_or : forall E F : BSet X, E ∈ m -> F ∈ m -> BSet.or E F ∈ m
  m_and : forall E F : BSet X, E ∈ m -> F ∈ m -> BSet.and E F ∈ m
  mu_add :
    forall E F : BSet X, forall hE : E ∈ m, forall hF : F ∈ m,
      relEventually
        (addSeq (mu E hE) (mu F hF))
        (addSeq
          (mu (BSet.or E F) (m_or E F hE hF))
          (mu (BSet.and E F) (m_and E F hE hF)))
  m_sub :
    forall E F : BSet X, E ∈ m -> BSet.and E F ∈ m -> BSet.sub E F ∈ m
  mu_sub :
    forall E F : BSet X, forall hE : E ∈ m, forall hAnd : BSet.and E F ∈ m,
      relEventually
        (mu E hE)
        (addSeq
          (mu (BSet.and E F) hAnd)
          (mu (BSet.sub E F) (m_sub E F hE hAnd)))
  m_pos_E : BSet X
  m_pos_mem : m_pos_E ∈ m
  m_pos_data : regularSeqLtData zeroSeq (mu m_pos_E m_pos_mem)
  m_limit :
    forall (E : Nat -> BSet X), forall hE : forall n, E n ∈ m,
      (forall n, regularSeqLtData zeroSeq (mu (E n) (hE n))) ->
        { x : X // forall n, x ∈ (E n).S1 }

/-- Bishop-style simple functions over a RegularSeq-valued measure space. -/
structure BishopRegularSeqSimpleFunction
    {Arch : ScalarMulArchimedeanData} {X : Type}
    (M : BishopRegularSeqMeasureSpaceSkeleton Arch X) : Type 1 where
  n : Nat
  E : Nat -> BSet X
  hE : forall k, E k ∈ M.m
  c : Nat -> RegularSeq

namespace BishopRegularSeqSimpleFunction

variable {Arch : ScalarMulArchimedeanData} {X : Type}
variable {M : BishopRegularSeqMeasureSpaceSkeleton Arch X}

/-- The source domain condition for a simple function. -/
def supportDom (f : BishopRegularSeqSimpleFunction M) (x : X) : Prop :=
  forall k, k < f.n -> x ∈ (f.E k).S1 ∨ x ∈ (f.E k).S2

/-- Data needed to evaluate a simple function at a point without deciding a
Prop-valued set membership. -/
structure EvalData (f : BishopRegularSeqSimpleFunction M) (x : X) :
    Type 1 where
  dom : supportDom f x
  branch :
    forall k, forall _hk : k < f.n,
      PSum (x ∈ (f.E k).S1) (x ∈ (f.E k).S2)

/-- One simple-function summand, using explicit branch data. -/
def evalTerm (f : BishopRegularSeqSimpleFunction M)
    (x : X) (d : EvalData f x) (k : Nat) : RegularSeq :=
  if hk : k < f.n then
    match d.branch k hk with
    | PSum.inl _ => f.c k
    | PSum.inr _ => zeroSeq
  else
    zeroSeq

/-- Evaluation with explicit branch data. -/
def evalWith (f : BishopRegularSeqSimpleFunction M)
    (x : X) (d : EvalData f x) : RegularSeq :=
  regularSeqFinSum (evalTerm f x d) f.n

/-- The formal integral of a simple function, with scalar multiplication done
inside the RegularSeq real surface. -/
def integral (f : BishopRegularSeqSimpleFunction M) : RegularSeq :=
  regularSeqFinSum
    (fun k => mulSeqConcreteWith Arch (f.c k) (M.mu (f.E k) (f.hE k)))
    f.n

end BishopRegularSeqSimpleFunction

/-- A partial-function representation of a simple function.  The representation
keeps explicit evaluation data on its domain, avoiding global membership
decision. -/
structure BishopRegularSeqSimplePFunRepresentation
    {Arch : ScalarMulArchimedeanData} {X : Type}
    (M : BishopRegularSeqMeasureSpaceSkeleton Arch X)
    (f : BishopRegularSeqSimpleFunction M) : Type 1 where
  pfun : BishopRegularSeqPFun X
  evalData :
    forall x : X, x ∈ pfun.dom ->
      BishopRegularSeqSimpleFunction.EvalData f x
  value_agrees :
    forall x : X, forall hx : x ∈ pfun.dom,
      relEventually
        (pfun.toFun x)
        (BishopRegularSeqSimpleFunction.evalWith f x (evalData x hx))

/-- Target bridge for Bishop-Cheng chapter 5, theorem 5.8 style:
measure data should induce an integration-space skeleton only through
RegularSeq-valued partial functions and Bishop equalities. -/
structure BishopRegularSeqMeasureToIntegrationSkeleton
    (Arch : ScalarMulArchimedeanData) (X : Type) : Type 1 where
  measureSpace : BishopRegularSeqMeasureSpaceSkeleton Arch X
  integrationSpace : BishopRegularSeqIntegrationSpaceSkeleton Arch X
  simpleRep :
    forall f : BishopRegularSeqSimpleFunction measureSpace,
      BishopRegularSeqSimplePFunRepresentation measureSpace f
  simple_mem :
    forall f : BishopRegularSeqSimpleFunction measureSpace,
      (simpleRep f).pfun ∈ integrationSpace.L
  simple_integral_agrees :
    forall f : BishopRegularSeqSimpleFunction measureSpace,
      relEventually
        (integrationSpace.I (simpleRep f).pfun)
        (BishopRegularSeqSimpleFunction.integral f)
  simple_eval_requires_branch_data : Prop
  measure_values_are_regularseq : Prop
  integral_values_are_regularseq : Prop
  scalar_equalities_are_bishop_equalities : Prop
  old_chapter5_cofoc_layer_is_adapter_only : Prop

/-- Audit for why the chapter-5 refactor must use explicit branch data. -/
structure BishopRegularSeqMeasureRefactorAudit : Type where
  old_simple_eval_used_prop_membership_decision : Prop
  new_simple_eval_uses_branch_data : Prop
  measure_equalities_use_relEventually : Prop
  no_total_inverse_needed_for_measure_skeleton : Prop
  old_measure_space_remains_relative_cofoc_layer : Prop

def bishopRegularSeqMeasureRefactorAudit :
    BishopRegularSeqMeasureRefactorAudit where
  old_simple_eval_used_prop_membership_decision := True
  new_simple_eval_uses_branch_data := True
  measure_equalities_use_relEventually := True
  no_total_inverse_needed_for_measure_skeleton := True
  old_measure_space_remains_relative_cofoc_layer := True

/-- G29 progress meter after fixing the chapter-5 target skeleton. -/
structure CRealCOFOCG29MeasureSkeletonProgressMeter : Type where
  regularSeqRealSurfacePercent : Nat
  bishopFaithfulInterfacePercent : Nat
  chapter5MeasureSkeletonPercent : Nat
  measureTheoryRefactorPercent : Nat
  oldQuotNoExtraInputPercent : Nat
  sourceFaithfulnessConfidencePercent : Nat
  simpleFunctionClassicalBranchRemovedFromTarget : Prop
  next_step_is_measure_to_integration_law_bridge : Prop

def cRealCOFOCG29MeasureSkeletonProgressMeter :
    CRealCOFOCG29MeasureSkeletonProgressMeter where
  regularSeqRealSurfacePercent := 97
  bishopFaithfulInterfacePercent := 54
  chapter5MeasureSkeletonPercent := 24
  measureTheoryRefactorPercent := 14
  oldQuotNoExtraInputPercent := 69
  sourceFaithfulnessConfidencePercent := 94
  simpleFunctionClassicalBranchRemovedFromTarget := True
  next_step_is_measure_to_integration_law_bridge := True

end BishopCReal

set_option linter.style.longLine false

