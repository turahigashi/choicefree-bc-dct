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

theorem maxQuotCOF_halfsum
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) :
    maxQuotCOFWith A x y =
      mulQuotConcreteWith A halfQuot
        (addQuot (addQuot x y) (absQuot (addQuot x (negQuot y)))) :=
  rfl

theorem minQuotCOF_halfsum
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) :
    minQuotCOFWith A x y =
      mulQuotConcreteWith A halfQuot
        (addQuot (addQuot x y) (negQuot (absQuot (addQuot x (negQuot y))))) :=
  rfl

/-- Map the data-order cotransitivity split back through the live Prop-valued
order required by `BishopC.COF`. -/
def ltQuot_cotrans_data_conditional
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    {a b : CRealQuot} (h : ltQuot a b) (c : CRealQuot) :
    PSum (ltQuot a c) (ltQuot c b) := by
  cases ltQuotData_cotrans_with_rep (ltDataOf h) c (rep c) with
  | inl hac => exact PSum.inl (ltQuotData_to_ltQuot hac)
  | inr hcb => exact PSum.inr (ltQuotData_to_ltQuot hcb)

/-- Conditional actual `COF` record for the CReal quotient.  The parameters are
exactly the two extraction frontiers isolated by `CRealQuotientCotransitivityDataBridge`/`CRealQuotientDataOrderPackage`. -/
@[reducible] def cRealQuotCOFConditionalWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    BishopC.COF CRealQuot where
  toCommRing := cRealQuotCommRingConcreteWith A
  lt := ltQuot
  lt_irrefl := ltQuot_irrefl
  lt_cotrans := fun {a b} h c => ltQuot_cotrans a b c h
  lt_cotrans_data := fun {a b} h c =>
    ltQuot_cotrans_data_conditional rep ltDataOf h c
  lt_add_left := fun c {a b} h => ltQuot_add_left c a b h
  abs := absQuot
  max := maxQuotCOFWith A
  min := minQuotCOFWith A
  half := halfQuot
  half_add_half := halfQuot_add_half
  max_halfsum := by
    intro x y
    rfl
  min_halfsum := by
    intro x y
    rfl

/-- Audited package exposing the conditional COF record together with the
data-order ingredients used to build it. -/
structure CRealQuotConditionalCOFPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  dataOrder : CRealQuotDataOrderWithReps
  cof : BishopC.COF CRealQuot

def cRealQuotConditionalCOFPackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotConditionalCOFPackage A where
  rep := rep
  ltDataOf := ltDataOf
  dataOrder := cRealQuotDataOrderWithReps rep
  cof := cRealQuotCOFConditionalWith A rep ltDataOf

/-- Frontier after the conditional `COF` record is available: the remaining
work is to construct the two extraction maps, then proceed to the stronger
`COFO` and `COFOC` fields. -/
structure CRealQuotCOFConditionalRemainingFrontier : Type where
  representative_extraction : Prop
  prop_lt_to_data_lt : Prop
  cofo_order_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFConditionalRemainingFrontier :
    CRealQuotCOFConditionalRemainingFrontier where
  representative_extraction := True
  prop_lt_to_data_lt := True
  cofo_order_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

