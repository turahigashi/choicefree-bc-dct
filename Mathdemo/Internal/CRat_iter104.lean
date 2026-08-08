import Mathdemo.Internal.CRat_iter103

/-!
# Represented positive shifts are not a genuine weakening

`CRat_iter102` reduced global representatives to positive `ltQuotData` plus
represented positive shifts.  This file audits the other direction: a global
representative selector immediately supplies represented positive shifts by
using the algebraic shift `-x + 1`.

Thus, once positive `ltQuotData` is assumed, represented positive shifts and
global representatives are interderivable.  The shift route is still a useful
localization of where the representative problem re-enters, but it is not an
independent weakening of the quotient-representative frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The algebraic shift `-x + 1` moves `x` exactly to `1`. -/
theorem add_positiveUnitShift_eq_one (x : CRealQuot) :
    addQuot x (addQuot (negQuot x) oneQuot) = oneQuot := by
  rw [← addQuot_assoc x (negQuot x) oneQuot,
    addQuot_neg_right, addQuot_zero_left]

/-- The algebraic shift `-x + 1` moves every quotient element into the strictly
positive cone. -/
theorem ltQuot_zero_add_positiveUnitShift (x : CRealQuot) :
    ltQuot zeroQuot (addQuot x (addQuot (negQuot x) oneQuot)) := by
  rw [add_positiveUnitShift_eq_one x]
  exact ltQuot_zero_one

/-- A global representative selector supplies represented positive shifts. -/
def cRealQuotPositiveShiftData_of_globalRep
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x) :
    CRealQuotPositiveShiftData where
  shift := fun x => addQuot (negQuot x) oneQuot
  shift_rep := fun x => rep (addQuot (negQuot x) oneQuot)
  shifted_positive := ltQuot_zero_add_positiveUnitShift

/-- Under positive `ltQuotData`, represented positive shifts and global
representatives are interderivable. -/
structure CRealQuotPositiveShiftDataEquivGlobal
    (posDataOf : CRealQuotPositiveLTDataOf) : Type 1 where
  to_global :
    CRealQuotPositiveShiftData →
      ∀ x : CRealQuot, CRealQuotRepWitness x
  from_global :
    (∀ x : CRealQuot, CRealQuotRepWitness x) →
      CRealQuotPositiveShiftData

def cRealQuotPositiveShiftDataEquivGlobal
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotPositiveShiftDataEquivGlobal posDataOf where
  to_global :=
    cRealQuotGlobalRep_of_positiveLTData_and_positiveShift posDataOf
  from_global := cRealQuotPositiveShiftData_of_globalRep

/-- Frontier after the positive-shift equivalence audit. -/
structure CRealQuotAfterPositiveShiftEquivAuditFrontier : Type where
  represented_positive_shift_equivalent_to_global_rep_under_positive_lt_data :
    Prop
  construct_positive_lt_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop
  find_non_global_rep_free_positive_shift_construction : Prop

def cRealQuotAfterPositiveShiftEquivAuditFrontier :
    CRealQuotAfterPositiveShiftEquivAuditFrontier where
  represented_positive_shift_equivalent_to_global_rep_under_positive_lt_data :=
    True
  construct_positive_lt_data_extraction := True
  construct_or_remove_strict_order_decidability := True
  find_non_global_rep_free_positive_shift_construction := True

end BishopCReal

set_option linter.style.longLine false

