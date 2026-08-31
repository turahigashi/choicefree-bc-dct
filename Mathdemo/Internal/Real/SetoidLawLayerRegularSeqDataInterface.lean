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









end BishopCReal

set_option linter.style.longLine false

