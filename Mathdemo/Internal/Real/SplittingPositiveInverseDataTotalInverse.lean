import Mathdemo.Internal.Real.COFOCAssemblyGlobalRepsPosEventuallySelector

/-!
# Splitting positive inverse data from total inverse selection

`COFOCAssemblyGlobalRepsPosEventuallySelector` normalized the current route to `COFOC` as depending on strict
order decidability, global representatives, and a `PosEventually` selector.
This file attacks the strict-order-decidability dependency at the positive
inverse layer.

The proof-indexed positive inverse already has cancellation and positivity when
given explicit `ltQuotData zeroQuot x`.  Decidability is only one way to turn
that partial/data-indexed inverse into the total `inv : CRealQuot → CRealQuot`
field required by `COFO`.  We isolate that totalization step as its own datum.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Decidability-free data-indexed positive inverse field. -/
structure CRealQuotPositiveInverseDataField : Type 1 where
  invData :
    ∀ _A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ltQuotData zeroQuot x → CRealQuot
  invData_respects_data :
    ∀ A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ∀ h₁ h₂ : ltQuotData zeroQuot x,
        invData A h₁ = invData A h₂
  invData_respects_quot_eq :
    ∀ A : ScalarMulArchimedeanData, ∀ {x y : CRealQuot},
      x = y → ∀ hx : ltQuotData zeroQuot x,
        ∀ hy : ltQuotData zeroQuot y, invData A hx = invData A hy
  mul_inv_cancel_data :
    ∀ A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ∀ h : ltQuotData zeroQuot x,
        mulQuotConcreteWith A x (invData A h) = oneQuot
  inv_pos_data :
    ∀ A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ∀ h : ltQuotData zeroQuot x,
        ltQuotData zeroQuot (invData A h)
  inv_pos :
    ∀ A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ∀ h : ltQuotData zeroQuot x,
        ltQuot zeroQuot (invData A h)

def cRealQuotPositiveInverseDataField :
    CRealQuotPositiveInverseDataField where
  invData := fun A {x} h => positiveQuotInvWithData A (x := x) h
  invData_respects_data := fun A {x} h₁ h₂ =>
    positiveQuotInvWithData_respects_data A (x := x) h₁ h₂
  invData_respects_quot_eq := fun A {x} {y} hxy hx hy =>
    positiveQuotInvWithData_respects_quot_eq A (x := x) (y := y)
      hxy hx hy
  mul_inv_cancel_data := fun A {x} h =>
    positiveQuot_mul_invWithData_eq_one A (x := x) h
  inv_pos_data := fun A {x} h =>
    positiveQuotInvWithData_posData A (x := x) h
  inv_pos := fun A {x} h =>
    positiveQuotInvWithData_pos A (x := x) h

/-- A totalization of the data-indexed inverse for a fixed multiplication
choice.  This is the exact extra datum needed to fill the total `COFO.inv`
field without asking the inverse construction itself to decide positivity. -/
structure CRealQuotPositiveInverseTotalizationData
    (A : ScalarMulArchimedeanData) : Type where
  inv : CRealQuot → CRealQuot
  agrees_on_positive_data :
    ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
      inv x = positiveQuotInvWithData A h

/-- The previous decidable positive-branch selector is one way to totalize the
data-indexed positive inverse. -/
def cRealQuotPositiveInverseTotalizationData_of_decidablePositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotPositiveInverseTotalizationData A where
  inv := positiveQuotInvOrZeroWithDecidablePositiveData A hdec posDataOf
  agrees_on_positive_data := by
    intro x h
    have hx : ltQuot zeroQuot x := ltQuotData_to_ltQuot h
    rw [positiveQuotInvOrZeroWithDecidablePositiveData_eq_of_pos
      A hdec posDataOf hx]
    exact positiveQuotInvWithData_respects_data A (posDataOf hx) h

/-- Positive-inverse field data for the decidable-order `COF` branch using an
abstract totalization datum instead of branching inside the inverse proof. -/
def cRealQuotPositiveInverseFieldDataWithTotalizationDecidableCOF
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealQuotPositiveInverseFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  inv := tot.inv
  mul_inv_cancel := by
    intro x hx
    change ltQuot zeroQuot x at hx
    let h : ltQuotData zeroQuot x := posDataOf hx
    change mulQuotConcreteWith A x (tot.inv x) = oneQuot
    rw [tot.agrees_on_positive_data h]
    exact positiveQuot_mul_invWithData_eq_one A h
  inv_pos := by
    intro x hx
    change ltQuot zeroQuot x at hx
    let h : ltQuotData zeroQuot x := posDataOf hx
    change ltQuot zeroQuot (tot.inv x)
    rw [tot.agrees_on_positive_data h]
    exact positiveQuotInvWithData_pos A h

/-- Full `COFO` field data for the decidable-order branch, with the inverse
dependency split into positive data extraction plus totalization. -/
def cRealQuotCOFOFieldDataWithPositiveInverseDecidableLTTotalized
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    CRealQuotCOFOFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) := by
  let base := cRealQuotCOFOAfterEqSmallFieldDataWithDecidableLT A hdec
  let pinv :=
    cRealQuotPositiveInverseFieldDataWithTotalizationDecidableCOF
      A hdec posDataOf tot
  exact {
    lt_trans := base.lt_trans
    abs_zero := base.abs_zero
    abs_neg := base.abs_neg
    neg_le_abs := base.neg_le_abs
    le_abs_self := base.le_abs_self
    abs_le_of := base.abs_le_of
    one_pos := base.one_pos
    half_pos := base.half_pos
    mul_pos := base.mul_pos
    archimedean := base.archimedean
    archimedean_pos := base.archimedean_pos
    abs_add_le := base.abs_add_le
    eq_of_small := base.eq_of_small
    abs_of_nonneg := base.abs_of_nonneg
    max_zero_nonneg := base.max_zero_nonneg
    max_le_abs := base.max_le_abs
    neg_min_zero_nonneg := base.neg_min_zero_nonneg
    neg_min_le_abs := base.neg_min_le_abs
    lt_or_lt_of_abs_pos := base.lt_or_lt_of_abs_pos
    abs_mul := base.abs_mul
    mul_nonneg := base.mul_nonneg
    mul_archimedean := base.mul_archimedean
    inv := pinv.inv
    mul_inv_cancel := pinv.mul_inv_cancel
    inv_pos := pinv.inv_pos
  }

/-- A live `COFO` in the decidable-order branch when totalization is supplied
separately. -/
@[reducible] def cRealQuotCOFOWithPositiveInverseDecidableLTTotalized
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (tot : CRealQuotPositiveInverseTotalizationData A) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOConditionalWithDecidableLT A hdec
    (cRealQuotCOFOFieldDataWithPositiveInverseDecidableLTTotalized
      A hdec posDataOf tot)

/-- Frontier after splitting the inverse-totalization problem away from the
data-indexed positive inverse.  Strict-order decidability still appears in the
current `COF` order branch, but it is no longer intrinsic to the positive
inverse laws themselves. -/
structure CRealQuotAfterPositiveInverseTotalizationSplitFrontier : Type where
  positive_inverse_data_field_is_decidability_free : Prop
  decidable_positive_branch_is_one_totalization : Prop
  total_inverse_selection_remains_for_live_cofo : Prop
  strict_order_decidability_remains_in_cof_order_branch : Prop
  representative_and_pos_eventually_selector_frontiers_remain : Prop

def cRealQuotAfterPositiveInverseTotalizationSplitFrontier :
    CRealQuotAfterPositiveInverseTotalizationSplitFrontier where
  positive_inverse_data_field_is_decidability_free := True
  decidable_positive_branch_is_one_totalization := True
  total_inverse_selection_remains_for_live_cofo := True
  strict_order_decidability_remains_in_cof_order_branch := True
  representative_and_pos_eventually_selector_frontiers_remain := True

end BishopCReal

set_option linter.style.longLine false

