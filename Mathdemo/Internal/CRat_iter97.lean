import Mathdemo.Internal.CRat_iter96

/-!
# Localizing order-data extraction to positive inverse inputs

`CRat_iter93` removed the global representative selector from the live
decidable-order quotient `COFO`, but its positive inverse field still accepted
a general extraction principle

`forall {a b}, ltQuot a b -> ltQuotData a b`.

The inverse branch only ever applies that principle to inequalities of the
form `ltQuot zeroQuot x`.  This file makes that dependence explicit.  It does
not construct the positive-data extractor, and it does not remove strict-order
decidability; it narrows the remaining order-data frontier to the exact shape
used by `COFO.inv`, `mul_inv_cancel`, and `inv_pos`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The exact data-extraction principle used by the positive inverse branch. -/
abbrev CRealQuotPositiveLTDataOf : Type :=
  ∀ {x : CRealQuot}, ltQuot zeroQuot x → ltQuotData zeroQuot x

/-- A general `ltQuotData` extractor specializes to the positive branch. -/
def cRealQuotPositiveLTDataOf_of_ltDataOf
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotPositiveLTDataOf :=
  fun {x} hx => ltDataOf (a := zeroQuot) (b := x) hx

/-- Total inverse selector whose data argument is localized to positive
quotient elements. -/
def positiveQuotInvOrZeroWithDecidablePositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    (x : CRealQuot) : CRealQuot :=
  letI : Decidable (ltQuot zeroQuot x) := hdec zeroQuot x
  if hx : ltQuot zeroQuot x then
    positiveQuotInvWithData A (posDataOf hx)
  else
    zeroQuot

/-- On a positive quotient element, the localized total selector reduces to
the data-indexed positive inverse. -/
theorem positiveQuotInvOrZeroWithDecidablePositiveData_eq_of_pos
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    {x : CRealQuot} (hx : ltQuot zeroQuot x) :
    positiveQuotInvOrZeroWithDecidablePositiveData A hdec posDataOf x =
      positiveQuotInvWithData A (posDataOf hx) := by
  simp [positiveQuotInvOrZeroWithDecidablePositiveData, hx]

/-- On a non-positive quotient element, the localized total selector is zero. -/
theorem positiveQuotInvOrZeroWithDecidablePositiveData_eq_zero_of_not_pos
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    {x : CRealQuot} (hx : ¬ ltQuot zeroQuot x) :
    positiveQuotInvOrZeroWithDecidablePositiveData A hdec posDataOf x =
      zeroQuot := by
  simp [positiveQuotInvOrZeroWithDecidablePositiveData, hx]

/-- The localized total selector respects quotient equality on positive
inputs. -/
theorem positiveQuotInvOrZeroWithDecidablePositiveData_respects_pos_eq
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    {x y : CRealQuot} (hxy : x = y)
    (hx : ltQuot zeroQuot x) (hy : ltQuot zeroQuot y) :
    positiveQuotInvOrZeroWithDecidablePositiveData A hdec posDataOf x =
      positiveQuotInvOrZeroWithDecidablePositiveData A hdec posDataOf y := by
  rw [positiveQuotInvOrZeroWithDecidablePositiveData_eq_of_pos
      A hdec posDataOf hx,
    positiveQuotInvOrZeroWithDecidablePositiveData_eq_of_pos
      A hdec posDataOf hy]
  exact positiveQuotInvWithData_respects_quot_eq
    A hxy (posDataOf hx) (posDataOf hy)

/-- Cancellation for the localized total inverse selector. -/
theorem positiveQuotInvOrZeroWithDecidablePositiveData_mul_inv_cancel
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    {x : CRealQuot} (hx : ltQuot zeroQuot x) :
    mulQuotConcreteWith A x
      (positiveQuotInvOrZeroWithDecidablePositiveData A hdec posDataOf x) =
        oneQuot := by
  rw [positiveQuotInvOrZeroWithDecidablePositiveData_eq_of_pos
    A hdec posDataOf hx]
  exact positiveQuot_mul_invWithData_eq_one A (posDataOf hx)

/-- Positivity for the localized total inverse selector. -/
theorem positiveQuotInvOrZeroWithDecidablePositiveData_inv_pos
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf)
    {x : CRealQuot} (hx : ltQuot zeroQuot x) :
    ltQuot zeroQuot
      (positiveQuotInvOrZeroWithDecidablePositiveData A hdec posDataOf x) := by
  rw [positiveQuotInvOrZeroWithDecidablePositiveData_eq_of_pos
    A hdec posDataOf hx]
  exact positiveQuotInvWithData_pos A (posDataOf hx)

/-- Positive-inverse field data for the decidable-order quotient `COF`
branch, using only positive-branch order-data extraction. -/
def cRealQuotPositiveInverseFieldDataWithDecidableLTPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotPositiveInverseFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  inv := positiveQuotInvOrZeroWithDecidablePositiveData A hdec posDataOf
  mul_inv_cancel := by
    intro x hx
    change
      mulQuotConcreteWith A x
        (positiveQuotInvOrZeroWithDecidablePositiveData
          A hdec posDataOf x) = oneQuot
    change ltQuot zeroQuot x at hx
    exact positiveQuotInvOrZeroWithDecidablePositiveData_mul_inv_cancel
      A hdec posDataOf hx
  inv_pos := by
    intro x hx
    change
      ltQuot zeroQuot
        (positiveQuotInvOrZeroWithDecidablePositiveData
          A hdec posDataOf x)
    change ltQuot zeroQuot x at hx
    exact positiveQuotInvOrZeroWithDecidablePositiveData_inv_pos
      A hdec posDataOf hx

/-- Full quotient `COFO` field data for the decidable-order branch, with the
positive inverse depending only on positive-branch order data. -/
def cRealQuotCOFOFieldDataWithPositiveInverseDecidableLTPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotCOFOFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) := by
  let base := cRealQuotCOFOAfterEqSmallFieldDataWithDecidableLT A hdec
  let pinv := cRealQuotPositiveInverseFieldDataWithDecidableLTPositiveData
    A hdec posDataOf
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

/-- A live quotient `COFO` record in the decidable-order branch, whose
positive inverse asks only for positive-branch `ltQuotData`. -/
@[reducible] def cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOConditionalWithDecidableLT A hdec
    (cRealQuotCOFOFieldDataWithPositiveInverseDecidableLTPositiveData
      A hdec posDataOf)

/-- Compact package for the localized positive-order-data `COFO` branch. -/
structure CRealQuotDecidableLTPositiveDataCOFOPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  positiveLtDataOf : CRealQuotPositiveLTDataOf
  pinv : CRealQuotPositiveInverseFieldData
    (cRealQuotCOFConditionalWithDecidableLT A strict_order_decidable)
  cofo : BishopC.COFO CRealQuot

def cRealQuotDecidableLTPositiveDataCOFOPackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (posDataOf : CRealQuotPositiveLTDataOf) :
    CRealQuotDecidableLTPositiveDataCOFOPackage A where
  strict_order_decidable := hdec
  positiveLtDataOf := posDataOf
  pinv := cRealQuotPositiveInverseFieldDataWithDecidableLTPositiveData
    A hdec posDataOf
  cofo := cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData
    A hdec posDataOf

/-- The general-data `COFO` from `CRat_iter93` is an instance of this localized
interface by specialization to positive inequalities. -/
@[reducible] def cRealQuotCOFOWithPositiveInverseDecidableLTData_asPositiveData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOWithPositiveInverseDecidableLTPositiveData A hdec
    (cRealQuotPositiveLTDataOf_of_ltDataOf ltDataOf)

/-- Frontier after localizing `ltQuotData` extraction to the positive-inverse
branch. -/
structure CRealQuotAfterPositiveLTDataLocalizationFrontier : Type where
  positive_inverse_uses_only_positive_lt_data : Prop
  construct_positive_lt_data_extraction : Prop
  construct_or_remove_strict_order_decidability : Prop
  rep_free_cauchy_completeness_without_global_rep : Prop

def cRealQuotAfterPositiveLTDataLocalizationFrontier :
    CRealQuotAfterPositiveLTDataLocalizationFrontier where
  positive_inverse_uses_only_positive_lt_data := True
  construct_positive_lt_data_extraction := True
  construct_or_remove_strict_order_decidability := True
  rep_free_cauchy_completeness_without_global_rep := True

end BishopCReal

