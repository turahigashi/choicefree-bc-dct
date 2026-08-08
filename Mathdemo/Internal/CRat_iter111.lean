import Mathdemo.Internal.CRat_iter110

/-!
# Positive-data inverse consumer without total inverse selection

`CRat_iter110` removed strict-order decidability from the live quotient
`COFOC` route, but it still needed
`CRealQuotPositiveInverseTotalizationData A` because `BishopC.COFO` asks for a
total field

```
inv : CRealQuot -> CRealQuot
```

Bishop's constructive real inverse is not a total computational operation in
that sense: the reciprocal is constructed from positive/apartness data.  This
file therefore records the faithful consumer interface for the quotient
positive inverse: cancellation and positivity are available from
`ltQuotData zeroQuot x`, and from Prop-level positivity only after the
Prop-to-data bridge has supplied such a witness.

No inverse totalization datum is used below.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Positive-inverse laws consumed in their data-indexed form.

This is the constructive part of the `COFO` inverse fields, with the total
selector deliberately absent.  The Prop-level consumers are included only after
an explicit positive-data bridge has supplied the witness hidden in
`COF.lt 0 x`. -/
structure CRealQuotPositiveDataInverseLayer
    (A : ScalarMulArchimedeanData) : Type 1 where
  cof : BishopC.COF CRealQuot
  positiveDataOf :
    letI : BishopC.COF CRealQuot := cof
    ∀ {x : CRealQuot}, COF.lt 0 x -> ltQuotData zeroQuot x
  invData : ∀ {x : CRealQuot}, ltQuotData zeroQuot x -> CRealQuot
  invData_agrees :
    ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
      invData h = positiveQuotInvWithData A h
  data_mul_inv_cancel :
    ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
      mulQuotConcreteWith A x (invData h) = oneQuot
  data_inv_pos :
    ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
      ltQuot zeroQuot (invData h)
  prop_mul_inv_cancel :
    letI : BishopC.COF CRealQuot := cof
    ∀ {x : CRealQuot}, ∀ hx : COF.lt 0 x,
      x * invData (positiveDataOf hx) = 1
  prop_inv_pos :
    letI : BishopC.COF CRealQuot := cof
    ∀ {x : CRealQuot}, ∀ hx : COF.lt 0 x,
      COF.lt 0 (invData (positiveDataOf hx))

/-- The nondecidable selector route supplies the positive-data inverse layer
without any total inverse selection. -/
def cRealQuotPositiveDataInverseLayerWithGlobalRepSelector
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotPositiveDataInverseLayer A where
  cof := cRealQuotCOFWithGlobalRepPosEventuallySelector A rep sel
  positiveDataOf := by
    intro x hx
    change ltQuot zeroQuot x at hx
    exact cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector rep sel hx
  invData := fun h => positiveQuotInvWithData A h
  invData_agrees := by
    intro x h
    rfl
  data_mul_inv_cancel := by
    intro x h
    exact positiveQuot_mul_invWithData_eq_one A h
  data_inv_pos := by
    intro x h
    exact positiveQuotInvWithData_pos A h
  prop_mul_inv_cancel := by
    intro x hx
    change ltQuot zeroQuot x at hx
    let h : ltQuotData zeroQuot x :=
      cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector rep sel hx
    change mulQuotConcreteWith A x (positiveQuotInvWithData A h) = oneQuot
    exact positiveQuot_mul_invWithData_eq_one A h
  prop_inv_pos := by
    intro x hx
    change ltQuot zeroQuot x at hx
    let h : ltQuotData zeroQuot x :=
      cRealQuotPositiveLTDataOfGlobalRepPosEventuallySelector rep sel hx
    change ltQuot zeroQuot (positiveQuotInvWithData A h)
    exact positiveQuotInvWithData_pos A h

/-- Compact package exposing the data-order layer, the faithful positive
inverse consumer, and the still-separate live `COFOC` totalization route.

The package intentionally has no `CRealQuotPositiveInverseTotalizationData`
field.  It records the part that is already constructive before forcing it
through the older total-`inv` interface. -/
structure CRealQuotPositiveDataInversePackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  globalRep : ∀ x : CRealQuot, CRealQuotRepWitness x
  posEventuallySelector : CRealPosEventuallySelector
  dataCOFPackage : CRealQuotDataCOFToLiveCOFPackage A
  inverseLayer : CRealQuotPositiveDataInverseLayer A

def cRealQuotPositiveDataInversePackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotPositiveDataInversePackage A where
  globalRep := rep
  posEventuallySelector := sel
  dataCOFPackage :=
    cRealQuotDataCOFToLiveCOFPackageWithGlobalRepPosEventuallySelector
      A rep sel
  inverseLayer :=
    cRealQuotPositiveDataInverseLayerWithGlobalRepSelector A rep sel

/-- Frontier after separating the faithful positive-inverse consumer from the
total-inverse field demanded by live `BishopC.COFO`. -/
structure CRealQuotAfterPositiveDataInverseLayerFrontier : Type where
  positive_inverse_laws_need_only_positive_data : Prop
  live_cofo_total_inv_field_is_interface_pressure : Prop
  inverse_totalization_not_used_in_positive_data_layer : Prop
  remaining_inputs_global_rep_and_pos_eventually_selector : Prop
  next_step_choose_data_cofo_or_construct_totalization : Prop

def cRealQuotAfterPositiveDataInverseLayerFrontier :
    CRealQuotAfterPositiveDataInverseLayerFrontier where
  positive_inverse_laws_need_only_positive_data := True
  live_cofo_total_inv_field_is_interface_pressure := True
  inverse_totalization_not_used_in_positive_data_layer := True
  remaining_inputs_global_rep_and_pos_eventually_selector := True
  next_step_choose_data_cofo_or_construct_totalization := True

end BishopCReal

set_option linter.style.longLine false

