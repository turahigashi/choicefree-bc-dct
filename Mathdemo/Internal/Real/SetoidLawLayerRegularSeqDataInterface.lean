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

/-- Positive data transports along eventual equality at the Prop level.

This deliberately does not invent new positive data for the target
representative; it records the already proved Prop-level transport. -/
theorem posEventually_of_posData_relEventually
    {x y : RegularSeq}
    (hxy : relEventually x y) (hx : PosEventuallyData x) :
    PosEventually y :=
  posEventually_respects x y hxy hx.toProp

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

def cRealRegularSeqSetoidLawLayer
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqSetoidLawLayer A where
  rawEq := rel
  rawEq_refl := rel_refl
  rawEq_symm := rel_symm
  eventualEq := relEventually
  raw_to_eventual := rel_to_relEventually
  eventual_refl := relEventually_refl
  eventual_symm := relEventually_symm
  eventual_trans := relEventually_trans
  neg_respects := negSeq_respects_eventually
  add_respects := addSeq_respects_eventually
  sub_respects := subSeq_respects_eventually
  abs_respects := absSeq_respects_eventually
  mul_respects := mulSeqConcrete_respects_eventually A
  max_respects := maxSeqWith_respects_eventually A
  min_respects := minSeqWith_respects_eventually A
  positiveData_transport_prop := fun hxy hx =>
    posEventually_of_posData_relEventually hxy hx
  invData_respects := fun hx hy hxy =>
    positiveTailInvSeqWithBound_respects_eventually_data A hx hy hxy

/-- Extended data-interface package after adding the setoid law layer. -/
structure CRealRegularSeqDataCOFOCSetoidPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  dataInterface : CRealRegularSeqDataCOFOCInterface A
  setoidLaws : CRealRegularSeqSetoidLawLayer A
  raw_source_equality_exposed : Prop
  transitive_implementation_equality_available : Prop
  operations_respect_implementation_equality : Prop
  inverse_respects_positive_data_and_eventual_equality : Prop

def cRealRegularSeqDataCOFOCSetoidPackage
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqDataCOFOCSetoidPackage A where
  dataInterface := cRealRegularSeqDataCOFOCInterface A
  setoidLaws := cRealRegularSeqSetoidLawLayer A
  raw_source_equality_exposed := True
  transitive_implementation_equality_available := True
  operations_respect_implementation_equality := True
  inverse_respects_positive_data_and_eventual_equality := True

/-- Roadmap checkpoint after thickening the RegularSeq data-interface with
setoid and respect laws. -/
structure CRealAfterRegularSeqSetoidLawLayerFrontier : Type where
  regularseq_data_interface_setoid_laws_available : Prop
  max_min_respect_closed : Prop
  positive_inverse_respect_closed : Prop
  remaining_law_thickening_algebra_order_complete : Prop
  old_quotient_adapter_remains_separate : Prop

def cRealAfterRegularSeqSetoidLawLayerFrontier :
    CRealAfterRegularSeqSetoidLawLayerFrontier where
  regularseq_data_interface_setoid_laws_available := True
  max_min_respect_closed := True
  positive_inverse_respect_closed := True
  remaining_law_thickening_algebra_order_complete := True
  old_quotient_adapter_remains_separate := True

end BishopCReal

set_option linter.style.longLine false

