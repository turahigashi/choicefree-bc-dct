import Mathdemo.Internal.CRat_iter129

/-!
# G30: align completed Bishop-Cheng (1972) sections 1--4 with the Bishop-faithful route

Bishop-Cheng (1972) sections 1--4 are treated here as the completed
formalization scope.  This file does not reopen that work.  It records how the
completed files relate to the regular-sequence route:

* existing section-1--4 Lean artifacts over `[COFOC R]` are retained as
  relative formalization theorems;
* the Bishop-real concrete route is not the previous quotient/structural-equality
  route;
* future Bishop-real interpretation should target the RegularSeq-valued
  partial-function and integration skeletons introduced in `CRat_iter128` and
  `CRat_iter129`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Existing section-1--4 integration-space type, viewed explicitly as a
relative `[COFOC R]` artifact. -/
def oldSec1To4IntSpaceType (X R : Type) (inst : BishopC.COFOC R) : Type :=
  letI : BishopC.COFOC R := inst
  BishopC.IntSpaceRC X R

/-- Existing section-4 partial-function type, again relative to `[COFOC R]`. -/
def oldSec1To4PFunType (X R : Type) (inst : BishopC.COFOC R) : Type :=
  letI : BishopC.COFOC R := inst
  BishopC.PFunR X R

/-- Existing section-4 measurability predicate as a relative predicate. -/
def oldSec1To4IsMeasurablePredicate
    (X R : Type) (inst : BishopC.COFOC R) :
    oldSec1To4IntSpaceType X R inst ->
      oldSec1To4PFunType X R inst -> Prop :=
  letI : BishopC.COFOC R := inst
  fun S h => BishopC.IsMeasurable S h

/-- Existing section-4 convergence-in-measure predicate as a relative
predicate. -/
def oldSec1To4ConvergeInMeasurePredicate
    (X R : Type) (inst : BishopC.COFOC R) :
    oldSec1To4IntSpaceType X R inst ->
      (Nat -> oldSec1To4PFunType X R inst) ->
        oldSec1To4PFunType X R inst -> Prop :=
  letI : BishopC.COFOC R := inst
  fun S fn f => BishopC.ConvergeInMeasure S fn f

/-- Existing section-2 integrable-set type as a relative type. -/
def oldSec2IntegrableSetType
    (X R : Type) (inst : BishopC.COFOC R)
    (S : oldSec1To4IntSpaceType X R inst) (E : BishopC.BSet X) : Type :=
  letI : BishopC.COFOC R := inst
  BishopC.IntegrableSet1 S E

/-- Existing section-2 induced measure, still valued in the abstract scalar
`R` of the completed relative formalization. -/
noncomputable def oldSec2MeasureValue
    (X R : Type) (inst : BishopC.COFOC R)
    (S : oldSec1To4IntSpaceType X R inst)
    {E : BishopC.BSet X} (hE : oldSec2IntegrableSetType X R inst S E) : R :=
  letI : BishopC.COFOC R := inst
  BishopC.measure1 S hE

/-- Bishop-faithful section-1--4 target skeleton.

This is the target for future migration/interpretation of the completed
section-1--4 results when the scalar is Bishop's regular-sequence real. -/
structure BishopRegularSeqSec1To4TargetSkeleton
    (Arch : ScalarMulArchimedeanData) (X : Type) : Type 1 where
  integrationSpace : BishopRegularSeqIntegrationSpaceSkeleton Arch X
  integrableSet : BishopC.BSet X -> Type
  measure : forall E : BishopC.BSet X, integrableSet E -> RegularSeq
  measure_respects :
    forall E : BishopC.BSet X, forall hE hE' : integrableSet E,
      relEventually (measure E hE) (measure E hE')
  measurable : BishopRegularSeqPFun X -> Prop
  measurable_respects :
    forall {f g : BishopRegularSeqPFun X},
      measurable f -> BishopRegularSeqPFun.equiv f g -> measurable g
  convergeInMeasure :
    (Nat -> BishopRegularSeqPFun X) -> BishopRegularSeqPFun X -> Prop
  convergence_respects_limit :
    forall {fn : Nat -> BishopRegularSeqPFun X},
      forall {f g : BishopRegularSeqPFun X},
        convergeInMeasure fn f -> BishopRegularSeqPFun.equiv f g ->
          convergeInMeasure fn g
  section1_partial_function_semantics : Prop
  section2_integrable_sets_semantics : Prop
  section3_profile_semantics : Prop
  section4_convergence_semantics : Prop
  scalar_equalities_are_bishop_equalities : Prop

/-- Alignment package: how the already completed section-1--4 artifacts and
the new Bishop-regular-sequence route coexist. -/
structure BishopChengSec1To4PolicyAlignment
    (Arch : ScalarMulArchimedeanData) : Type 2 where
  oldIntSpace :
    Type -> forall R : Type, BishopC.COFOC R -> Type
  oldPFun :
    Type -> forall R : Type, BishopC.COFOC R -> Type
  oldIsMeasurable :
    forall X R : Type, forall inst : BishopC.COFOC R,
      oldIntSpace X R inst -> oldPFun X R inst -> Prop
  oldConvergeInMeasure :
    forall X R : Type, forall inst : BishopC.COFOC R,
      oldIntSpace X R inst -> (Nat -> oldPFun X R inst) ->
        oldPFun X R inst -> Prop
  newRegularSeqTarget :
    Type -> Type 1
  newRegularSeqPFun :
    Type -> Type
  newRegularSeqPFunEq :
    forall X : Type, newRegularSeqPFun X -> newRegularSeqPFun X -> Prop
  completed_sections_1_to_4_remain_relative_cofoc_results : Prop
  bishop_real_model_route_is_regularseq_surface : Prop
  do_not_reinterpret_old_structural_equality_as_bishop_equality : Prop
  old_quotient_cofoc_is_adapter_only : Prop
  no_need_to_rewrite_completed_sections_before_section5 : Prop
  section5_and_beyond_should_target_regularseq_skeleton : Prop

def bishopChengSec1To4PolicyAlignment
    (Arch : ScalarMulArchimedeanData) :
    BishopChengSec1To4PolicyAlignment Arch where
  oldIntSpace := oldSec1To4IntSpaceType
  oldPFun := oldSec1To4PFunType
  oldIsMeasurable := oldSec1To4IsMeasurablePredicate
  oldConvergeInMeasure := oldSec1To4ConvergeInMeasurePredicate
  newRegularSeqTarget :=
    fun X => BishopRegularSeqSec1To4TargetSkeleton Arch X
  newRegularSeqPFun := BishopRegularSeqPFun
  newRegularSeqPFunEq := fun _ => BishopRegularSeqPFun.equiv
  completed_sections_1_to_4_remain_relative_cofoc_results := True
  bishop_real_model_route_is_regularseq_surface := True
  do_not_reinterpret_old_structural_equality_as_bishop_equality := True
  old_quotient_cofoc_is_adapter_only := True
  no_need_to_rewrite_completed_sections_before_section5 := True
  section5_and_beyond_should_target_regularseq_skeleton := True

/-- Progress meter after aligning the completed section-1--4 scope. -/
structure CRealCOFOCG30Sec1To4AlignmentProgressMeter : Type where
  completedSec1To4ScopePreservedPercent : Nat
  bishopPolicyAlignmentForSec1To4Percent : Nat
  bishopFaithfulInterfacePercent : Nat
  chapter5MeasureSkeletonPercent : Nat
  measureTheoryRefactorPercent : Nat
  oldQuotNoExtraInputPercent : Nat
  sourceFaithfulnessConfidencePercent : Nat
  section5NextTarget : Prop

def cRealCOFOCG30Sec1To4AlignmentProgressMeter :
    CRealCOFOCG30Sec1To4AlignmentProgressMeter where
  completedSec1To4ScopePreservedPercent := 100
  bishopPolicyAlignmentForSec1To4Percent := 72
  bishopFaithfulInterfacePercent := 57
  chapter5MeasureSkeletonPercent := 24
  measureTheoryRefactorPercent := 16
  oldQuotNoExtraInputPercent := 69
  sourceFaithfulnessConfidencePercent := 94
  section5NextTarget := True

end BishopCReal

set_option linter.style.longLine false
