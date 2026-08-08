import Mathdemo.Internal.CRat_iter101

/-!
# Positive shifts recover global representatives

`CRat_iter101` recorded that positive `ltQuotData` supplies representatives
only for strictly positive quotient elements, plus the canonical representative
of zero.

This file isolates the exact additional bridge needed to turn that partial
representative supply into a global one: every quotient element must be
shiftable, by a represented quotient element, into the strictly positive cone.
With that data, the additive group laws move the positive representative back
to a representative of the original quotient element.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A represented additive shift of `x` gives a representative of `x` once
`x + shift` is represented. -/
def cRealQuotRepWitness_of_add_shift_rep
    {x shift : CRealQuot}
    (hshift : CRealQuotRepWitness shift)
    (hshifted : CRealQuotRepWitness (addQuot x shift)) :
    CRealQuotRepWitness x := by
  rcases hshift with ⟨shiftRep, hshiftEq⟩
  rcases hshifted with ⟨shiftedRep, hshiftedEq⟩
  refine {
    rep := addSeq shiftedRep (negSeq shiftRep)
    eq_mk := ?_
  }
  have hcancel : addQuot (addQuot x shift) (negQuot shift) = x := by
    rw [addQuot_assoc, addQuot_neg_right, addQuot_zero_right]
  calc
    x = addQuot (addQuot x shift) (negQuot shift) := hcancel.symm
    _ = addQuot (mkQuot shiftedRep) (negQuot (mkQuot shiftRep)) := by
      rw [hshiftedEq, hshiftEq]
    _ = mkQuot (addSeq shiftedRep (negSeq shiftRep)) := rfl

/-- Data asserting that every quotient element can be moved into the strictly
positive cone by adding a represented shift. -/
structure CRealQuotPositiveShiftData : Type where
  shift : CRealQuot → CRealQuot
  shift_rep : ∀ x : CRealQuot, CRealQuotRepWitness (shift x)
  shifted_positive : ∀ x : CRealQuot, ltQuot zeroQuot (addQuot x (shift x))

/-- Positive-order-data extraction plus represented positive shifts recovers a
global representative selector. -/
def cRealQuotGlobalRep_of_positiveLTData_and_positiveShift
    (posDataOf : CRealQuotPositiveLTDataOf)
    (shiftData : CRealQuotPositiveShiftData) :
    ∀ x : CRealQuot, CRealQuotRepWitness x := by
  intro x
  let hshifted : CRealQuotRepWitness (addQuot x (shiftData.shift x)) :=
    cRealQuotRepWitness_of_positiveLTData posDataOf
      (shiftData.shifted_positive x)
  exact cRealQuotRepWitness_of_add_shift_rep
    (shiftData.shift_rep x) hshifted

/-- Frontier after reducing global representatives to represented positive
shifts plus positive-order-data extraction. -/
structure CRealQuotAfterPositiveShiftRepFrontier : Type where
  positive_shift_plus_positive_lt_data_implies_global_rep : Prop
  construct_represented_positive_shift_data : Prop
  construct_positive_lt_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterPositiveShiftRepFrontier :
    CRealQuotAfterPositiveShiftRepFrontier where
  positive_shift_plus_positive_lt_data_implies_global_rep := True
  construct_represented_positive_shift_data := True
  construct_positive_lt_data_extraction := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

set_option linter.style.longLine false

