import Mathdemo.Internal.Real.CRealQuotientDataOrderPackage

/-!
# Conditional CReal quotient COF record

`CRealQuotientDataOrderPackage` closed the data-order layer once quotient representatives are
available.  This file performs the next packaging step: if the final quotient
interface supplies

* a representative witness for every quotient element, and
* a constructive translation from the current Prop-valued `ltQuot` into the
  data-valued quotient order,

then the actual `BishopC.COF CRealQuot` record can be emitted.

This does not register a global instance.  The multiplication still depends on
the explicit scalar multiplicative Archimedean datum, and the two extraction
maps remain honest frontier inputs.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- COF-facing maximum written with the inherited ring subtraction convention.
This is definitionally aligned with the `BishopC.COF.max_halfsum` field. -/
def maxQuotCOFWith
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) : CRealQuot :=
  mulQuotConcreteWith A halfQuot
    (addQuot (addQuot x y) (absQuot (addQuot x (negQuot y))))

/-- COF-facing minimum written with the inherited ring subtraction convention.
This is definitionally aligned with the `BishopC.COF.min_halfsum` field. -/
def minQuotCOFWith
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) : CRealQuot :=
  mulQuotConcreteWith A halfQuot
    (addQuot (addQuot x y) (negQuot (absQuot (addQuot x (negQuot y)))))

theorem maxQuotCOF_eq_concrete
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) :
    maxQuotCOFWith A x y = maxQuotConcreteWith A x y := by
  unfold maxQuotCOFWith maxQuotConcreteWith
  rw [subQuot_eq_add_neg]

theorem minQuotCOF_eq_concrete
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) :
    minQuotCOFWith A x y = minQuotConcreteWith A x y := by
  unfold minQuotCOFWith minQuotConcreteWith
  rw [subQuot_eq_add_neg (addQuot x y) (absQuot (subQuot x y)),
    subQuot_eq_add_neg x y]









end BishopCReal

