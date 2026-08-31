import Mathdemo.Internal.Real.AlignCompletedBishopCheng1972Sections

/-!
# G31: theorem-5.8 bridge laws over the RegularSeq measure skeleton

This file continues the Bishop-faithful route with Bishop-Cheng (1972)
sections 1--4 treated as completed relative `[COFOC R]` work.

The target here is chapter 5, theorem 5.8: a measure space induces an
integration space.  We do not re-open the previous quotient/`COFOC` layer.  Instead
we prove the first bridge consequences that are already available from the
RegularSeq skeleton:

* if two simple-function representations denote Bishop-equivalent partial
  functions, their formal integrals are Bishop equal;
* if a simple function represents a linear combination of two represented
  simple functions, its formal integral has the corresponding linear formula.

These are the RegularSeq/Bishop-equality forms of the theorem-5.5
well-definedness step and theorem-5.8(1) linearity step.
-/

namespace BishopCReal

open BishopC
open BishopCRat

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Partial-function linear combination with RegularSeq scalar coefficients. -/
def linComb (Arch : ScalarMulArchimedeanData)
    (a b : RegularSeq) (f g : BishopRegularSeqPFun X) :
    BishopRegularSeqPFun X :=
  add (smul Arch a f) (smul Arch b g)

end BishopRegularSeqPFun

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Theorem-5.5 bridge: once simple functions are represented as partial
functions, equality of those partial functions implies equality of their formal
simple integrals, in Bishop's `relEventually` sense. -/
theorem bridge_simple_integral_respects_rep_equiv
    (T : BishopRegularSeqMeasureToIntegrationSkeleton Arch X)
    {f g : BishopRegularSeqSimpleFunction T.measureSpace}
    (hfg :
      BishopRegularSeqPFun.equiv
        (T.simpleRep f).pfun
        (T.simpleRep g).pfun) :
    relEventually
      (BishopRegularSeqSimpleFunction.integral f)
      (BishopRegularSeqSimpleFunction.integral g) := by
  have hfI :
      relEventually
        (T.integrationSpace.I (T.simpleRep f).pfun)
        (BishopRegularSeqSimpleFunction.integral f) :=
    T.simple_integral_agrees f
  have hgI :
      relEventually
        (T.integrationSpace.I (T.simpleRep g).pfun)
        (BishopRegularSeqSimpleFunction.integral g) :=
    T.simple_integral_agrees g
  have hI :
      relEventually
        (T.integrationSpace.I (T.simpleRep f).pfun)
        (T.integrationSpace.I (T.simpleRep g).pfun) :=
    T.integrationSpace.I_resp (T.simple_mem f) hfg
  exact
    relEventually_trans
      (BishopRegularSeqSimpleFunction.integral f)
      (T.integrationSpace.I (T.simpleRep f).pfun)
      (BishopRegularSeqSimpleFunction.integral g)
      (relEventually_symm
        (T.integrationSpace.I (T.simpleRep f).pfun)
        (BishopRegularSeqSimpleFunction.integral f)
        hfI)
      (relEventually_trans
        (T.integrationSpace.I (T.simpleRep f).pfun)
        (T.integrationSpace.I (T.simpleRep g).pfun)
        (BishopRegularSeqSimpleFunction.integral g)
        hI
        hgI)

/-- Theorem-5.8(1) bridge: if a simple function represents
`a * f + b * g` at the partial-function level, its formal integral satisfies
the corresponding Bishop-equality linearity formula. -/
theorem bridge_simple_integral_linear_of_rep_equiv
    (T : BishopRegularSeqMeasureToIntegrationSkeleton Arch X)
    (a b : RegularSeq)
    (f g h : BishopRegularSeqSimpleFunction T.measureSpace)
    (hrep :
      BishopRegularSeqPFun.equiv
        (T.simpleRep h).pfun
        (BishopRegularSeqPFun.linComb Arch a b
          (T.simpleRep f).pfun
          (T.simpleRep g).pfun)) :
    relEventually
      (BishopRegularSeqSimpleFunction.integral h)
      (addSeq
        (mulSeqConcreteWith Arch a
          (BishopRegularSeqSimpleFunction.integral f))
        (mulSeqConcreteWith Arch b
          (BishopRegularSeqSimpleFunction.integral g))) := by
  let pf := (T.simpleRep f).pfun
  let pg := (T.simpleRep g).pfun
  let ph := (T.simpleRep h).pfun
  let af := BishopRegularSeqPFun.smul Arch a pf
  let bg := BishopRegularSeqPFun.smul Arch b pg
  have hhI :
      relEventually
        (T.integrationSpace.I ph)
        (BishopRegularSeqSimpleFunction.integral h) :=
    T.simple_integral_agrees h
  have hIrep :
      relEventually
        (T.integrationSpace.I ph)
        (T.integrationSpace.I (BishopRegularSeqPFun.add af bg)) :=
    T.integrationSpace.I_resp (T.simple_mem h) hrep
  have haf_mem : af ∈ T.integrationSpace.L :=
    T.integrationSpace.smul_mem a (T.simple_mem f)
  have hbg_mem : bg ∈ T.integrationSpace.L :=
    T.integrationSpace.smul_mem b (T.simple_mem g)
  have hIadd :
      relEventually
        (T.integrationSpace.I (BishopRegularSeqPFun.add af bg))
        (addSeq (T.integrationSpace.I af) (T.integrationSpace.I bg)) :=
    T.integrationSpace.I_add haf_mem hbg_mem
  have hIsmul_f :
      relEventually
        (T.integrationSpace.I af)
        (mulSeqConcreteWith Arch a (T.integrationSpace.I pf)) :=
    T.integrationSpace.I_smul a (T.simple_mem f)
  have hIsmul_g :
      relEventually
        (T.integrationSpace.I bg)
        (mulSeqConcreteWith Arch b (T.integrationSpace.I pg)) :=
    T.integrationSpace.I_smul b (T.simple_mem g)
  have hIlin_mid :
      relEventually
        (addSeq (T.integrationSpace.I af) (T.integrationSpace.I bg))
        (addSeq
          (mulSeqConcreteWith Arch a (T.integrationSpace.I pf))
          (mulSeqConcreteWith Arch b (T.integrationSpace.I pg))) :=
    addSeq_respects_eventually
      (T.integrationSpace.I af)
      (mulSeqConcreteWith Arch a (T.integrationSpace.I pf))
      (T.integrationSpace.I bg)
      (mulSeqConcreteWith Arch b (T.integrationSpace.I pg))
      hIsmul_f
      hIsmul_g
  have hfI :
      relEventually
        (T.integrationSpace.I pf)
        (BishopRegularSeqSimpleFunction.integral f) :=
    T.simple_integral_agrees f
  have hgI :
      relEventually
        (T.integrationSpace.I pg)
        (BishopRegularSeqSimpleFunction.integral g) :=
    T.simple_integral_agrees g
  have hmul_f :
      relEventually
        (mulSeqConcreteWith Arch a (T.integrationSpace.I pf))
        (mulSeqConcreteWith Arch a
          (BishopRegularSeqSimpleFunction.integral f)) :=
    mulSeqConcrete_respects_eventually Arch
      a a
      (T.integrationSpace.I pf)
      (BishopRegularSeqSimpleFunction.integral f)
      (relEventually_refl a)
      hfI
  have hmul_g :
      relEventually
        (mulSeqConcreteWith Arch b (T.integrationSpace.I pg))
        (mulSeqConcreteWith Arch b
          (BishopRegularSeqSimpleFunction.integral g)) :=
    mulSeqConcrete_respects_eventually Arch
      b b
      (T.integrationSpace.I pg)
      (BishopRegularSeqSimpleFunction.integral g)
      (relEventually_refl b)
      hgI
  have hIlin_final :
      relEventually
        (addSeq
          (mulSeqConcreteWith Arch a (T.integrationSpace.I pf))
          (mulSeqConcreteWith Arch b (T.integrationSpace.I pg)))
        (addSeq
          (mulSeqConcreteWith Arch a
            (BishopRegularSeqSimpleFunction.integral f))
          (mulSeqConcreteWith Arch b
            (BishopRegularSeqSimpleFunction.integral g))) :=
    addSeq_respects_eventually
      (mulSeqConcreteWith Arch a (T.integrationSpace.I pf))
      (mulSeqConcreteWith Arch a
        (BishopRegularSeqSimpleFunction.integral f))
      (mulSeqConcreteWith Arch b (T.integrationSpace.I pg))
      (mulSeqConcreteWith Arch b
        (BishopRegularSeqSimpleFunction.integral g))
      hmul_f
      hmul_g
  exact
    relEventually_trans
      (BishopRegularSeqSimpleFunction.integral h)
      (T.integrationSpace.I ph)
      (addSeq
        (mulSeqConcreteWith Arch a
          (BishopRegularSeqSimpleFunction.integral f))
        (mulSeqConcreteWith Arch b
          (BishopRegularSeqSimpleFunction.integral g)))
      (relEventually_symm
        (T.integrationSpace.I ph)
        (BishopRegularSeqSimpleFunction.integral h)
        hhI)
      (relEventually_trans
        (T.integrationSpace.I ph)
        (T.integrationSpace.I (BishopRegularSeqPFun.add af bg))
        (addSeq
          (mulSeqConcreteWith Arch a
            (BishopRegularSeqSimpleFunction.integral f))
          (mulSeqConcreteWith Arch b
            (BishopRegularSeqSimpleFunction.integral g)))
        hIrep
        (relEventually_trans
          (T.integrationSpace.I (BishopRegularSeqPFun.add af bg))
          (addSeq (T.integrationSpace.I af) (T.integrationSpace.I bg))
          (addSeq
            (mulSeqConcreteWith Arch a
              (BishopRegularSeqSimpleFunction.integral f))
            (mulSeqConcreteWith Arch b
              (BishopRegularSeqSimpleFunction.integral g)))
          hIadd
          (relEventually_trans
            (addSeq (T.integrationSpace.I af) (T.integrationSpace.I bg))
            (addSeq
              (mulSeqConcreteWith Arch a (T.integrationSpace.I pf))
              (mulSeqConcreteWith Arch b (T.integrationSpace.I pg)))
            (addSeq
              (mulSeqConcreteWith Arch a
                (BishopRegularSeqSimpleFunction.integral f))
              (mulSeqConcreteWith Arch b
                (BishopRegularSeqSimpleFunction.integral g)))
            hIlin_mid
            hIlin_final)))

/-- Extra source-level law data still needed to complete theorem 5.8 itself:
construct simple functions for linear combinations and prove their
partial-function representation equivalences. -/
structure BishopRegularSeqTheorem58ClosureTargets
    (T : BishopRegularSeqMeasureToIntegrationSkeleton Arch X) : Type 1 where
  simpleLinComb :
    RegularSeq -> RegularSeq ->
      BishopRegularSeqSimpleFunction T.measureSpace ->
      BishopRegularSeqSimpleFunction T.measureSpace ->
      BishopRegularSeqSimpleFunction T.measureSpace
  simpleLinComb_rep :
    forall a b f g,
      BishopRegularSeqPFun.equiv
        (T.simpleRep (simpleLinComb a b f g)).pfun
        (BishopRegularSeqPFun.linComb Arch a b
          (T.simpleRep f).pfun
          (T.simpleRep g).pfun)
  simpleAbs :
    BishopRegularSeqSimpleFunction T.measureSpace ->
      BishopRegularSeqSimpleFunction T.measureSpace
  simpleAbs_rep :
    forall f,
      BishopRegularSeqPFun.equiv
        (T.simpleRep (simpleAbs f)).pfun
        (BishopRegularSeqPFun.absf (T.simpleRep f).pfun)
  simpleMinOne :
    BishopRegularSeqSimpleFunction T.measureSpace ->
      BishopRegularSeqSimpleFunction T.measureSpace
  simpleMinOne_rep :
    forall f,
      BishopRegularSeqPFun.equiv
        (T.simpleRep (simpleMinOne f)).pfun
        (BishopRegularSeqPFun.minConst Arch (T.simpleRep f).pfun oneSeq)

/-- G31 progress meter after closing the first RegularSeq bridge theorems for
theorem 5.8. -/
structure CRealCOFOCG31MeasureBridgeProgressMeter : Type where
  completedSec1To4ScopePreservedPercent : Nat
  theorem55BridgePercent : Nat
  theorem58LinearityBridgePercent : Nat
  bishopFaithfulInterfacePercent : Nat
  chapter5MeasureSkeletonPercent : Nat
  measureTheoryRefactorPercent : Nat
  oldQuotNoExtraInputPercent : Nat
  sourceFaithfulnessConfidencePercent : Nat
  next_step_is_closure_targets_for_simple_functions : Prop

def cRealCOFOCG31MeasureBridgeProgressMeter :
    CRealCOFOCG31MeasureBridgeProgressMeter where
  completedSec1To4ScopePreservedPercent := 100
  theorem55BridgePercent := 38
  theorem58LinearityBridgePercent := 31
  bishopFaithfulInterfacePercent := 60
  chapter5MeasureSkeletonPercent := 31
  measureTheoryRefactorPercent := 20
  oldQuotNoExtraInputPercent := 69
  sourceFaithfulnessConfidencePercent := 94
  next_step_is_closure_targets_for_simple_functions := True

end BishopCReal

set_option linter.style.longLine false
