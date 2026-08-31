import Mathdemo.Internal.Real.RepresentedPositiveShiftsNotGenuineWeakening

/-!
# Splitting Prop-order to data-order extraction

`RepresentedPositiveShiftsNotGenuineWeakening` showed that represented positive shifts are equivalent to a
global representative selector once positive `ltQuotData` is assumed.  The
other remaining extraction problem is the Prop-to-Type bridge from `ltQuot` to
`ltQuotData`.

This file splits that bridge into two explicit ingredients:

* representatives for the compared quotient elements;
* a representative-level extraction from `PosEventually : Prop` to
  `PosEventuallyData : Type`.

The second ingredient is the true Prop-to-data positivity frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative-level Prop-to-data positivity extraction. -/
abbrev CRealPosEventuallyDataOf : Type :=
  ∀ {x : RegularSeq}, PosEventually x → PosEventuallyData x

/-- Once representatives of the two endpoints are supplied, the general
Prop-valued quotient order can be converted to data-valued quotient order using
only representative-level positivity-data extraction. -/
def ltQuotData_of_repWitnesses_and_posEventuallyDataOf
    (posDataOf : CRealPosEventuallyDataOf)
    {a b : CRealQuot}
    (ha : CRealQuotRepWitness a)
    (hb : CRealQuotRepWitness b)
    (h : ltQuot a b) :
    ltQuotData a b := by
  rcases ha with ⟨ar, har⟩
  rcases hb with ⟨br, hbr⟩
  have hmk : ltQuot (mkQuot ar) (mkQuot br) := by
    rwa [har, hbr] at h
  change PosEventually (subSeq br ar) at hmk
  exact {
    left := ar
    right := br
    left_eq := har
    right_eq := hbr
    pos := posDataOf hmk
  }

/-- A global representative selector plus representative-level positivity-data
extraction supplies the previous general `ltQuotData` extractor. -/
def cRealQuotLTDataOf_of_globalRep_and_posEventuallyDataOf
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (posDataOf : CRealPosEventuallyDataOf) :
    CRealQuotPropLTToDataLTObligation :=
  fun {a b} h =>
    ltQuotData_of_repWitnesses_and_posEventuallyDataOf
      posDataOf (rep a) (rep b) h

/-- The same split specializes to the positive-data extractor used by the
localized positive inverse branch. -/
def cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallyDataOf
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (posDataOf : CRealPosEventuallyDataOf) :
    CRealQuotPositiveLTDataOf :=
  cRealQuotPositiveLTDataOf_of_ltDataOf
    (cRealQuotLTDataOf_of_globalRep_and_posEventuallyDataOf
      rep posDataOf)

/-- Frontier after splitting quotient Prop-order extraction into
representative extraction plus representative-level positivity-data
extraction. -/
structure CRealQuotAfterLTDataExtractionSplitFrontier : Type where
  lt_data_extraction_reduces_to_reps_plus_pos_eventually_data : Prop
  representative_extraction : Prop
  pos_eventually_prop_to_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterLTDataExtractionSplitFrontier :
    CRealQuotAfterLTDataExtractionSplitFrontier where
  lt_data_extraction_reduces_to_reps_plus_pos_eventually_data := True
  representative_extraction := True
  pos_eventually_prop_to_data_extraction := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

set_option linter.style.longLine false

