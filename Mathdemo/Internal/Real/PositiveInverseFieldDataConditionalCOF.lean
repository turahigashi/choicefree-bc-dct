import Mathdemo.Internal.Real.PositivityProofIndexedPositiveQuotientInverse

/-!
# Positive inverse field data for the conditional COF branch

`PositivityProofIndexedPositiveQuotientInverse` proves both inverse laws for the positive total selector:

* cancellation on positive inputs;
* positivity of the selected inverse on positive inputs.

This file packages those two theorems as the `CRealQuotPositiveInverseFieldData`
expected by `COFOAssemblyPositiveInverseData`, and then assembles the corresponding conditional
`COFO` record.  The construction is still conditional on the existing
representative/data-order branch plus a decidable strict-order selector for the
total inverse.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Positive-inverse field data for the conditional quotient `COF` branch,
using the decidable total selector from `TotalPositiveInverseSelectorDecidableQuotient`. -/
def cRealQuotPositiveInverseFieldDataWithDecidable
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotPositiveInverseFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  inv := positiveQuotInvOrZeroWithDecidable A hdec ltDataOf
  mul_inv_cancel := by
    intro x hx
    change
      mulQuotConcreteWith A x
        (positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x) = oneQuot
    change ltQuot zeroQuot x at hx
    exact positiveQuotInvOrZeroWithDecidable_mul_inv_cancel A hdec ltDataOf hx
  inv_pos := by
    intro x hx
    change
      ltQuot zeroQuot
        (positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x)
    change ltQuot zeroQuot x at hx
    exact positiveQuotInvOrZeroWithDecidable_inv_pos A hdec ltDataOf hx

/-- The non-completeness `COFO` record after supplying the newly closed
positive-inverse field data. -/
@[reducible] def cRealQuotCOFOWithPositiveInverseDecidable
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOWithPositiveInverse A rep ltDataOf
    (cRealQuotPositiveInverseFieldDataWithDecidable A rep hdec ltDataOf)

/-- A compact package exposing the inverse selector, its two laws, and the
assembled conditional `COFO` record. -/
structure CRealQuotPositiveInverseCOFOPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  pinv : CRealQuotPositiveInverseFieldData
    (cRealQuotCOFConditionalWith A rep ltDataOf)
  cofo : BishopC.COFO CRealQuot

def cRealQuotPositiveInverseCOFOPackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotPositiveInverseCOFOPackage A where
  rep := rep
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  pinv := cRealQuotPositiveInverseFieldDataWithDecidable A rep hdec ltDataOf
  cofo := cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf

/-- Frontier after conditional positive-inverse `COFO` assembly.  The remaining
large item is sequential Cauchy completeness; removing the decidable-order
fork would be a separate constructivity-strengthening task. -/
structure CRealQuotAfterPositiveInverseCOFOFrontier : Type where
  cauchy_completeness : Prop
  remove_decidable_order_fork : Prop

def cRealQuotAfterPositiveInverseCOFOFrontier :
    CRealQuotAfterPositiveInverseCOFOFrontier where
  cauchy_completeness := True
  remove_decidable_order_fork := True

end BishopCReal

