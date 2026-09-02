import Mathdemo.Internal.Real.RegularSeqDataInterfaceForkBishopStyle

/-!
# Setoid law layer for the RegularSeq data-interface

`RegularSeqDataInterfaceForkBishopStyle` exposed the Bishop-style carrier as `RegularSeq` with
data-valued positivity and data-indexed reciprocal.  This file adds the next
layer: the operations in that interface respect the representative equality
used by the implementation.

The source-level equality remains the raw Bishop relation `rel`; the already
closed implementation setoid is `relEventually`.  We therefore record both:

* raw `rel` with its source-shaped reflexivity/symmetry and bridge to
  `relEventually`;
* `relEventually` as the transitive implementation setoid;
* operation respect for add/sub/neg/abs/mul/max/min and the positive-data
  inverse.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Sequence-level max respects eventual Bishop equality. -/
theorem maxSeqWith_respects_eventually
    (A : ScalarMulArchimedeanData)
    (x x' y y' : RegularSeq)
    (hxx : relEventually x x') (hyy : relEventually y y') :
    relEventually (maxSeqWith A x y) (maxSeqWith A x' y') := by
  unfold maxSeqWith
  have hsum :
      relEventually (addSeq x y) (addSeq x' y') :=
    addSeq_respects_eventually x x' y y' hxx hyy
  have hsub :
      relEventually (subSeq x y) (subSeq x' y') :=
    subSeq_respects_eventually x x' y y' hxx hyy
  have habs :
      relEventually (absSeq (subSeq x y)) (absSeq (subSeq x' y')) :=
    absSeq_respects_eventually (subSeq x y) (subSeq x' y') hsub
  have hbody :
      relEventually
        (addSeq (addSeq x y) (absSeq (subSeq x y)))
        (addSeq (addSeq x' y') (absSeq (subSeq x' y'))) :=
    addSeq_respects_eventually
      (addSeq x y) (addSeq x' y')
      (absSeq (subSeq x y)) (absSeq (subSeq x' y'))
      hsum habs
  exact mulSeqConcrete_respects_eventually A
    halfSeq halfSeq
    (addSeq (addSeq x y) (absSeq (subSeq x y)))
    (addSeq (addSeq x' y') (absSeq (subSeq x' y')))
    (relEventually_refl halfSeq) hbody

/-- Sequence-level min respects eventual Bishop equality. -/
theorem minSeqWith_respects_eventually
    (A : ScalarMulArchimedeanData)
    (x x' y y' : RegularSeq)
    (hxx : relEventually x x') (hyy : relEventually y y') :
    relEventually (minSeqWith A x y) (minSeqWith A x' y') := by
  unfold minSeqWith
  have hsum :
      relEventually (addSeq x y) (addSeq x' y') :=
    addSeq_respects_eventually x x' y y' hxx hyy
  have hsub :
      relEventually (subSeq x y) (subSeq x' y') :=
    subSeq_respects_eventually x x' y y' hxx hyy
  have habs :
      relEventually (absSeq (subSeq x y)) (absSeq (subSeq x' y')) :=
    absSeq_respects_eventually (subSeq x y) (subSeq x' y') hsub
  have hbody :
      relEventually
        (subSeq (addSeq x y) (absSeq (subSeq x y)))
        (subSeq (addSeq x' y') (absSeq (subSeq x' y'))) :=
    subSeq_respects_eventually
      (addSeq x y) (addSeq x' y')
      (absSeq (subSeq x y)) (absSeq (subSeq x' y'))
      hsum habs
  exact mulSeqConcrete_respects_eventually A
    halfSeq halfSeq
    (subSeq (addSeq x y) (absSeq (subSeq x y)))
    (subSeq (addSeq x' y') (absSeq (subSeq x' y')))
    (relEventually_refl halfSeq) hbody


/-- Data-indexed reciprocal respects eventual equality when positive data is
given on both representatives. -/
theorem positiveTailInvSeqWithBound_respects_eventually_data
    (A : ScalarMulArchimedeanData)
    {x y : RegularSeq}
    (hx : PosEventuallyData x) (hy : PosEventuallyData y)
    (hxy : relEventually x y) :
    relEventually
      (positiveTailInvSeqWithBound A x hx)
      (positiveTailInvSeqWithBound A y hy) :=
  positiveTailInvSeqWithBound_respects_eventually A x y hx hy hxy

/-- Setoid and operation-respect layer for the RegularSeq data-interface. -/
structure CRealRegularSeqSetoidLawLayer
    (A : ScalarMulArchimedeanData) : Type 1 where
  rawEq : RegularSeq → RegularSeq → Prop
  rawEq_refl : ∀ x : RegularSeq, rawEq x x
  rawEq_symm : ∀ x y : RegularSeq, rawEq x y → rawEq y x
  eventualEq : RegularSeq → RegularSeq → Prop
  raw_to_eventual : ∀ x y : RegularSeq, rawEq x y → eventualEq x y
  eventual_refl : ∀ x : RegularSeq, eventualEq x x
  eventual_symm : ∀ x y : RegularSeq, eventualEq x y → eventualEq y x
  eventual_trans :
    ∀ x y z : RegularSeq,
      eventualEq x y → eventualEq y z → eventualEq x z
  neg_respects :
    ∀ x y : RegularSeq,
      eventualEq x y → eventualEq (negSeq x) (negSeq y)
  add_respects :
    ∀ x x' y y' : RegularSeq,
      eventualEq x x' → eventualEq y y' →
        eventualEq (addSeq x y) (addSeq x' y')
  sub_respects :
    ∀ x x' y y' : RegularSeq,
      eventualEq x x' → eventualEq y y' →
        eventualEq (subSeq x y) (subSeq x' y')
  abs_respects :
    ∀ x y : RegularSeq,
      eventualEq x y → eventualEq (absSeq x) (absSeq y)
  mul_respects :
    ∀ x x' y y' : RegularSeq,
      eventualEq x x' → eventualEq y y' →
        eventualEq (mulSeqConcreteWith A x y) (mulSeqConcreteWith A x' y')
  max_respects :
    ∀ x x' y y' : RegularSeq,
      eventualEq x x' → eventualEq y y' →
        eventualEq (maxSeqWith A x y) (maxSeqWith A x' y')
  min_respects :
    ∀ x x' y y' : RegularSeq,
      eventualEq x x' → eventualEq y y' →
        eventualEq (minSeqWith A x y) (minSeqWith A x' y')
  positiveData_transport_prop :
    ∀ {x y : RegularSeq},
      eventualEq x y → PosEventuallyData x → PosEventually y
  invData_respects :
    ∀ {x y : RegularSeq},
      ∀ hx : PosEventuallyData x, ∀ hy : PosEventuallyData y,
        eventualEq x y →
          eventualEq
            (positiveTailInvSeqWithBound A x hx)
            (positiveTailInvSeqWithBound A y hy)


/-- Extended data-interface package after adding the setoid law layer. -/
structure CRealRegularSeqDataCOFOCSetoidPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  dataInterface : CRealRegularSeqDataCOFOCInterface A
  setoidLaws : CRealRegularSeqSetoidLawLayer A
  raw_source_equality_exposed : Prop
  transitive_implementation_equality_available : Prop
  operations_respect_implementation_equality : Prop
  inverse_respects_positive_data_and_eventual_equality : Prop




end BishopCReal

set_option linter.style.longLine false

