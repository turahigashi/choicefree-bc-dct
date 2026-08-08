import Mathdemo.Internal.CRat_iter100

/-!
# Representative scope of positive `ltQuotData`

`CRat_iter100` showed that even in the localized positive-data branch,
representatives for all Cauchy-sequence values collapse back to the previous global
representative selector.

This file records the narrower positive-order-data consequence that is
actually available: positive `ltQuotData` supplies a representative for a
strictly positive quotient element, and zero has its canonical representative.
That still does not produce representatives for arbitrary quotient elements.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The zero quotient has the canonical constant representative. -/
def cRealQuotRepWitness_zero : CRealQuotRepWitness zeroQuot where
  rep := zeroSeq
  eq_mk := rfl

/-- Positive-order-data extraction supplies a representative for a strictly
positive quotient element. -/
def cRealQuotRepWitness_of_positiveLTData
    (posDataOf : CRealQuotPositiveLTDataOf)
    {x : CRealQuot} (hx : ltQuot zeroQuot x) :
    CRealQuotRepWitness x := by
  let h := posDataOf hx
  exact { rep := h.right, eq_mk := h.right_eq }

/-- A compact package for the representatives directly supplied by positive
order data: zero and strictly positive quotient elements. -/
structure CRealQuotPositiveRepresentativeData : Type where
  zero_rep : CRealQuotRepWitness zeroQuot
  positive_rep :
    ∀ {x : CRealQuot}, ltQuot zeroQuot x → CRealQuotRepWitness x

/-- Positive-order-data extraction gives exactly the representative package
for zero and strictly positive quotient elements. -/
def cRealQuotPositiveRepresentativeData_of_positiveLTData
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotPositiveRepresentativeData where
  zero_rep := cRealQuotRepWitness_zero
  positive_rep := fun hx =>
    cRealQuotRepWitness_of_positiveLTData posDataOf hx

/-- Frontier after auditing the representative scope of positive-order data. -/
structure CRealQuotAfterPositiveLTDataRepScopeFrontier : Type where
  positive_lt_data_supplies_positive_representatives : Prop
  zero_has_canonical_representative : Prop
  missing_positive_shift_to_global_representatives : Prop
  construct_positive_lt_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterPositiveLTDataRepScopeFrontier :
    CRealQuotAfterPositiveLTDataRepScopeFrontier where
  positive_lt_data_supplies_positive_representatives := True
  zero_has_canonical_representative := True
  missing_positive_shift_to_global_representatives := True
  construct_positive_lt_data_extraction := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

set_option linter.style.longLine false

