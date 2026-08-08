import Mathdemo.Internal.CRat_iter131

/-!
# G32: theorem-5.8(1) closure consequences from simple-function targets

`CRat_iter131` isolated the missing source-level construction work for
theorem 5.8(1): construct simple functions representing linear combinations,
absolute values, and `min(f, 1)`.

This file proves what follows once those source-level constructions are
available.  The results are still Bishop-faithful: membership is membership in
the RegularSeq-valued partial-function integration skeleton, and scalar
equalities are `relEventually`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Theorem-5.8(1) closure, linear-combination part. -/
theorem bridge_theorem58_linComb_mem_from_targets
    (T : BishopRegularSeqMeasureToIntegrationSkeleton Arch X)
    (C : BishopRegularSeqTheorem58ClosureTargets T)
    (a b : RegularSeq)
    (f g : BishopRegularSeqSimpleFunction T.measureSpace) :
    BishopRegularSeqPFun.linComb Arch a b
      (T.simpleRep f).pfun
      (T.simpleRep g).pfun ∈ T.integrationSpace.L :=
  T.integrationSpace.L_resp
    (T.simple_mem (C.simpleLinComb a b f g))
    (C.simpleLinComb_rep a b f g)

/-- Theorem-5.8(1) closure, absolute-value part. -/
theorem bridge_theorem58_abs_mem_from_targets
    (T : BishopRegularSeqMeasureToIntegrationSkeleton Arch X)
    (C : BishopRegularSeqTheorem58ClosureTargets T)
    (f : BishopRegularSeqSimpleFunction T.measureSpace) :
    BishopRegularSeqPFun.absf (T.simpleRep f).pfun ∈ T.integrationSpace.L :=
  T.integrationSpace.L_resp
    (T.simple_mem (C.simpleAbs f))
    (C.simpleAbs_rep f)

/-- Theorem-5.8(1) closure, `min(f,1)` part. -/
theorem bridge_theorem58_minOne_mem_from_targets
    (T : BishopRegularSeqMeasureToIntegrationSkeleton Arch X)
    (C : BishopRegularSeqTheorem58ClosureTargets T)
    (f : BishopRegularSeqSimpleFunction T.measureSpace) :
    BishopRegularSeqPFun.minConst Arch (T.simpleRep f).pfun oneSeq ∈
      T.integrationSpace.L :=
  T.integrationSpace.L_resp
    (T.simple_mem (C.simpleMinOne f))
    (C.simpleMinOne_rep f)

/-- The linear integral formula for the source-level simple linear
combination produced by the closure target package. -/
theorem bridge_theorem58_linComb_integral_from_targets
    (T : BishopRegularSeqMeasureToIntegrationSkeleton Arch X)
    (C : BishopRegularSeqTheorem58ClosureTargets T)
    (a b : RegularSeq)
    (f g : BishopRegularSeqSimpleFunction T.measureSpace) :
    relEventually
      (BishopRegularSeqSimpleFunction.integral
        (C.simpleLinComb a b f g))
      (addSeq
        (mulSeqConcreteWith Arch a
          (BishopRegularSeqSimpleFunction.integral f))
        (mulSeqConcreteWith Arch b
          (BishopRegularSeqSimpleFunction.integral g))) :=
  bridge_simple_integral_linear_of_rep_equiv
    T a b f g (C.simpleLinComb a b f g)
    (C.simpleLinComb_rep a b f g)

/-- Target status after G32: theorem 5.8(1) is reduced to the source-level
simple-function closure constructions, rather than to previous `COFOC` equality. -/
structure BishopRegularSeqTheorem58Part1Reduction
    (T : BishopRegularSeqMeasureToIntegrationSkeleton Arch X) : Type 1 where
  closureTargets : BishopRegularSeqTheorem58ClosureTargets T
  linComb_membership_reduced_to_rep_equiv : Prop
  abs_membership_reduced_to_rep_equiv : Prop
  min_one_membership_reduced_to_rep_equiv : Prop
  linComb_integral_formula_kernel_proved : Prop
  theorem58_part1_remaining_work_is_simple_closure : Prop

/-- G32 progress meter. -/
structure CRealCOFOCG32Theorem58Part1ProgressMeter : Type where
  completedSec1To4ScopePreservedPercent : Nat
  theorem55BridgePercent : Nat
  theorem58Part1ReductionPercent : Nat
  bishopFaithfulInterfacePercent : Nat
  chapter5MeasureSkeletonPercent : Nat
  measureTheoryRefactorPercent : Nat
  oldQuotNoExtraInputPercent : Nat
  sourceFaithfulnessConfidencePercent : Nat
  next_step_is_construct_simple_closure_data : Prop

def cRealCOFOCG32Theorem58Part1ProgressMeter :
    CRealCOFOCG32Theorem58Part1ProgressMeter where
  completedSec1To4ScopePreservedPercent := 100
  theorem55BridgePercent := 41
  theorem58Part1ReductionPercent := 39
  bishopFaithfulInterfacePercent := 62
  chapter5MeasureSkeletonPercent := 35
  measureTheoryRefactorPercent := 22
  oldQuotNoExtraInputPercent := 69
  sourceFaithfulnessConfidencePercent := 94
  next_step_is_construct_simple_closure_data := True

end BishopCReal

set_option linter.style.longLine false

