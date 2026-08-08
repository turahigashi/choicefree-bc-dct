import Mathdemo.Internal.CRat_iter47

/-!
# CReal quotient COF via a decidable-order alternative

`CRat_iter47` sharpened the two extraction frontiers for the quotient route.
There is a second, logically distinct way to satisfy the live
`BishopC.COF.lt_cotrans_data` field: if the quotient strict order itself is
decidable, the existing Prop-valued cotransitivity

```
ltQuot a b → ltQuot a c ∨ ltQuot c b
```

can be converted into the Type-valued split by deciding the left branch.

This file packages that alternative.  It is not claimed as the Bishop-real
solution: decidability of strict order is much stronger than Bishop-style
apartness data.  The point is to isolate the exact fork:

* either provide Type-level order/representative data, as in `CRat_iter46`; or
* provide a decidable strict order, as in this conditional package.
-/

namespace BishopCReal

open BishopC
open BishopCRat

abbrev CRealQuotLTDecidable : Type :=
  ∀ a b : CRealQuot, Decidable (ltQuot a b)

/-- Convert the existing Prop-valued quotient cotransitivity into the
Type-valued `PSum` split when strict order is decidable. -/
def ltQuot_cotrans_data_of_decidable
    (hdec : CRealQuotLTDecidable)
    {a b : CRealQuot} (h : ltQuot a b) (c : CRealQuot) :
    PSum (ltQuot a c) (ltQuot c b) := by
  haveI : Decidable (ltQuot a c) := hdec a c
  haveI : Decidable (ltQuot c b) := hdec c b
  by_cases hac : ltQuot a c
  · exact PSum.inl hac
  · by_cases hcb : ltQuot c b
    · exact PSum.inr hcb
    · exact False.elim <|
        (ltQuot_cotrans a b c h).elim
          (fun hleft => hac hleft)
          (fun hright => hcb hright)

/-- Conditional actual `COF` record for the quotient route if strict order is
decidable.  This avoids quotient representative extraction, but pays for it
with a much stronger order assumption. -/
@[reducible] def cRealQuotCOFConditionalWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    BishopC.COF CRealQuot where
  toCommRing := cRealQuotCommRingConcreteWith A
  lt := ltQuot
  lt_irrefl := ltQuot_irrefl
  lt_cotrans := fun {a b} h c => ltQuot_cotrans a b c h
  lt_cotrans_data := fun {a b} h c =>
    ltQuot_cotrans_data_of_decidable hdec h c
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

/-- Conditional package exposing the decidable-order fork. -/
structure CRealQuotDecidableLTCOFPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  cof : BishopC.COF CRealQuot

def cRealQuotDecidableLTCOFPackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotDecidableLTCOFPackage A where
  strict_order_decidable := hdec
  cof := cRealQuotCOFConditionalWithDecidableLT A hdec

/-- Remaining fork after this file.  For Bishop constructive reals the
decidable-order branch is expected to be too strong, so the representation/data
branch remains the faithful one. -/
structure CRealQuotCOFForkFrontier : Type where
  data_order_or_representative_branch : Prop
  decidable_strict_order_branch : Prop
  cofo_order_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFForkFrontier : CRealQuotCOFForkFrontier where
  data_order_or_representative_branch := True
  decidable_strict_order_branch := True
  cofo_order_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

