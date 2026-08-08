import Mathdemo.Internal.CRat_iter78

/-!
# Cancellation for the conditional total inverse selector

`CRat_iter78` proves cancellation for the proof-indexed positive inverse.
This file transports that theorem to the decidable-order total selector from
`CRat_iter75`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- In the decidable-order branch, the total selector satisfies cancellation
on positive quotient elements. -/
theorem positiveQuotInvOrZeroWithDecidable_mul_inv_cancel
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    {x : CRealQuot} (hx : ltQuot zeroQuot x) :
    mulQuotConcreteWith A x
      (positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x) = oneQuot := by
  rw [positiveQuotInvOrZeroWithDecidable_eq_of_pos A hdec ltDataOf hx]
  exact positiveQuot_mul_invWithData_eq_one A (ltDataOf hx)

/-- Parameterized cancellation field data for the decidable-order branch. -/
structure CRealQuotPositiveInverseCancellationWith
    (A : ScalarMulArchimedeanData) : Type 1 where
  inv : CRealQuot → CRealQuot
  mul_inv_cancel :
    ∀ {x : CRealQuot}, ltQuot zeroQuot x →
      mulQuotConcreteWith A x (inv x) = oneQuot

def cRealQuotPositiveInverseCancellationWithDecidable
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotPositiveInverseCancellationWith A where
  inv := positiveQuotInvOrZeroWithDecidable A hdec ltDataOf
  mul_inv_cancel := by
    intro x hx
    exact positiveQuotInvOrZeroWithDecidable_mul_inv_cancel A hdec ltDataOf hx

/-- Data package for total-selector cancellation in the decidable-order branch. -/
structure PositiveQuotInvOrZeroCancellationSeed : Type 1 where
  mul_inv_cancel :
    ∀ A : ScalarMulArchimedeanData,
      ∀ hdec : CRealQuotLTDecidable,
      ∀ ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b,
      ∀ {x : CRealQuot}, ltQuot zeroQuot x →
        mulQuotConcreteWith A x
          (positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x) = oneQuot
  cancellationWith :
    ∀ A : ScalarMulArchimedeanData,
      CRealQuotLTDecidable →
      (∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) →
        CRealQuotPositiveInverseCancellationWith A

def positiveQuotInvOrZeroCancellationSeed :
    PositiveQuotInvOrZeroCancellationSeed where
  mul_inv_cancel := positiveQuotInvOrZeroWithDecidable_mul_inv_cancel
  cancellationWith := cRealQuotPositiveInverseCancellationWithDecidable

/-- Frontier after conditional total-selector cancellation is available. -/
structure CRealQuotPositiveInverseTotalCancellationFrontier : Type where
  quotient_inv_pos_uniform_lower_bound : Prop
  full_positive_inverse_field_data : Prop
  cauchy_completeness : Prop

def cRealQuotPositiveInverseTotalCancellationFrontier :
    CRealQuotPositiveInverseTotalCancellationFrontier where
  quotient_inv_pos_uniform_lower_bound := True
  full_positive_inverse_field_data := True
  cauchy_completeness := True

end BishopCReal

