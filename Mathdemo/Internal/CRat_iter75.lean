import Mathdemo.Internal.CRat_iter74

/-!
# Total positive-inverse selector under decidable quotient order

`CRat_iter74` defines the inverse of a positive quotient element when explicit
order data is supplied.  A live `COFO.inv` field is total, so this file isolates
one honest way to obtain a total selector: assume the quotient strict order is
decidable and keep the existing `ltQuot → ltQuotData` extraction parameter.

This is still a conditional selector, not the final Bishop-real inverse laws.
The cancellation and positivity laws require separate quotient estimates.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Total inverse selector for the conditional decidable-order branch:
positive elements use the data-indexed inverse, and non-positive elements are
sent to zero. -/
def positiveQuotInvOrZeroWithDecidable
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (x : CRealQuot) : CRealQuot :=
  letI : Decidable (ltQuot zeroQuot x) := hdec zeroQuot x
  if hx : ltQuot zeroQuot x then
    positiveQuotInvWithData A (ltDataOf hx)
  else
    zeroQuot

/-- On a positive quotient element, the total selector reduces to the
proof-indexed positive inverse. -/
theorem positiveQuotInvOrZeroWithDecidable_eq_of_pos
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    {x : CRealQuot} (hx : ltQuot zeroQuot x) :
    positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x =
      positiveQuotInvWithData A (ltDataOf hx) := by
  simp [positiveQuotInvOrZeroWithDecidable, hx]

/-- On a non-positive quotient element, the total selector is zero. -/
theorem positiveQuotInvOrZeroWithDecidable_eq_zero_of_not_pos
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    {x : CRealQuot} (hx : ¬ ltQuot zeroQuot x) :
    positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x = zeroQuot := by
  simp [positiveQuotInvOrZeroWithDecidable, hx]

/-- The total selector respects quotient equality on positive inputs. -/
theorem positiveQuotInvOrZeroWithDecidable_respects_pos_eq
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    {x y : CRealQuot} (hxy : x = y)
    (hx : ltQuot zeroQuot x) (hy : ltQuot zeroQuot y) :
    positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x =
      positiveQuotInvOrZeroWithDecidable A hdec ltDataOf y := by
  rw [positiveQuotInvOrZeroWithDecidable_eq_of_pos A hdec ltDataOf hx,
    positiveQuotInvOrZeroWithDecidable_eq_of_pos A hdec ltDataOf hy]
  exact positiveQuotInvWithData_respects_quot_eq A hxy (ltDataOf hx) (ltDataOf hy)

/-- Data package for the conditional total inverse selector. -/
structure PositiveQuotInvOrZeroWithDecidableSeed : Type 1 where
  inv :
    ScalarMulArchimedeanData →
      CRealQuotLTDecidable →
      (∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) →
      CRealQuot → CRealQuot
  inv_eq_of_pos :
    ∀ A : ScalarMulArchimedeanData,
      ∀ hdec : CRealQuotLTDecidable,
      ∀ ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b,
      ∀ {x : CRealQuot}, ∀ hx : ltQuot zeroQuot x,
        inv A hdec ltDataOf x = positiveQuotInvWithData A (ltDataOf hx)
  inv_eq_zero_of_not_pos :
    ∀ A : ScalarMulArchimedeanData,
      ∀ hdec : CRealQuotLTDecidable,
      ∀ ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b,
      ∀ {x : CRealQuot}, ∀ _hx : ¬ ltQuot zeroQuot x,
        inv A hdec ltDataOf x = zeroQuot
  inv_respects_pos_eq :
    ∀ A : ScalarMulArchimedeanData,
      ∀ hdec : CRealQuotLTDecidable,
      ∀ ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b,
      ∀ {x y : CRealQuot}, x = y →
        ltQuot zeroQuot x → ltQuot zeroQuot y →
          inv A hdec ltDataOf x = inv A hdec ltDataOf y

def positiveQuotInvOrZeroWithDecidableSeed :
    PositiveQuotInvOrZeroWithDecidableSeed where
  inv := positiveQuotInvOrZeroWithDecidable
  inv_eq_of_pos := positiveQuotInvOrZeroWithDecidable_eq_of_pos
  inv_eq_zero_of_not_pos := positiveQuotInvOrZeroWithDecidable_eq_zero_of_not_pos
  inv_respects_pos_eq := positiveQuotInvOrZeroWithDecidable_respects_pos_eq

/-- Frontier after a conditional total inverse selector is available. -/
structure CRealQuotPositiveInverseTotalSelectorFrontier : Type where
  constructive_nondecidable_selector : Prop
  quotient_mul_inv_cancel : Prop
  quotient_inv_pos : Prop
  cauchy_completeness : Prop

def cRealQuotPositiveInverseTotalSelectorFrontier :
    CRealQuotPositiveInverseTotalSelectorFrontier where
  constructive_nondecidable_selector := True
  quotient_mul_inv_cancel := True
  quotient_inv_pos := True
  cauchy_completeness := True

end BishopCReal

