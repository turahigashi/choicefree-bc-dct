import Mathdemo.Internal.Real.ExplicitAdapterBoundaryPreviousQuotientCOFOC

/-!
# Final source-shaped RegularSeq COFOC surface

`ExplicitAdapterBoundaryPreviousQuotientCOFOC` isolated the previous quotient route as an explicit adapter
boundary.  This file gives the constructive CReal route a single surface
object: the carrier is `RegularSeq`, equality is Bishop equality, strict order
and positivity are data-carrying, and inverse is indexed by positive data.

This is intentionally not a live `BishopC.COFOC RegularSeq` instance.  The old
typeclass uses Lean's structural equality and a total inverse field, while the
source-shaped real interface uses the implementation setoid and data-indexed
reciprocal.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A source-shaped CReal surface over regular representatives.

The field names mirror the previous scalar interface where that is meaningful, but
the equality, order, inverse, and completeness fields are the data-carrying
Bishop versions used by the construction. -/
structure CRealRegularSeqSourceCOFOCSurface
    (A : ScalarMulArchimedeanData) : Type 1 where
  carrier : Type
  carrier_is_regularSeq : carrier = RegularSeq
  eqRel : RegularSeq → RegularSeq → Prop
  eqRel_is_bishop_rel : eqRel = rel
  eventualEq : RegularSeq → RegularSeq → Prop
  eventualEq_is_impl_setoid : eventualEq = relEventually
  zero : RegularSeq
  one : RegularSeq
  half : RegularSeq
  add : RegularSeq → RegularSeq → RegularSeq
  neg : RegularSeq → RegularSeq
  sub : RegularSeq → RegularSeq → RegularSeq
  mul : RegularSeq → RegularSeq → RegularSeq
  abs : RegularSeq → RegularSeq
  max : RegularSeq → RegularSeq → RegularSeq
  min : RegularSeq → RegularSeq → RegularSeq
  ltProp : RegularSeq → RegularSeq → Prop
  ltData : RegularSeq → RegularSeq → Type
  ltData_to_prop : ∀ {x y : RegularSeq}, ltData x y → ltProp x y
  positiveData : RegularSeq → Type
  positiveData_to_prop : ∀ {x : RegularSeq}, positiveData x → PosEventually x
  positiveInv : ∀ {x : RegularSeq}, PosEventuallyData x → RegularSeq
  positiveInv_agrees :
    ∀ {x : RegularSeq}, ∀ hx : PosEventuallyData x,
      positiveInv hx = positiveTailInvSeqWithBound A x hx
  positiveInv_posData :
    ∀ {x : RegularSeq}, ∀ hx : PosEventuallyData x,
      ltData zero (positiveInv hx)
  positiveInv_mul_cancel :
    ∀ {x : RegularSeq}, ∀ hx : PosEventuallyData x,
      eventualEq (mul x (positiveInv hx)) one
  archimedean_posData :
    ∀ {x : RegularSeq}, PosEventuallyData x →
      Sigma (fun k : Nat => ltData (constSeq (eps k)) x)
  mul_archimedean_data :
    ∀ x : RegularSeq,
      { m : Nat // ¬ ltProp one (mul (abs x) (constSeq (eps m))) }
  setoidLaws : CRealRegularSeqSetoidLawLayer A
  algebraLaws : CRealRegularSeqAlgebraLawLayer A
  orderLaws : CRealRegularSeqDataOrderLawLayer
  archDataPackage : CRealRegularSeqDataCOFOCArchDataPackage A
  repSequenceComplete : CRealRepSequenceCompleteLayer
  oldQuotAdapterBoundary : CRealOldQuotCOFOCAdapterBoundary A
  source_surface_uses_regular_sequences : Prop
  structural_equality_is_not_the_real_equality : Prop
  inverse_is_data_indexed_not_total : Prop
  old_typeclass_is_adapter_only : Prop

def cRealRegularSeqSourceCOFOCSurface
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqSourceCOFOCSurface A where
  carrier := RegularSeq
  carrier_is_regularSeq := rfl
  eqRel := rel
  eqRel_is_bishop_rel := rfl
  eventualEq := relEventually
  eventualEq_is_impl_setoid := rfl
  zero := zeroSeq
  one := oneSeq
  half := halfSeq
  add := addSeq
  neg := negSeq
  sub := subSeq
  mul := mulSeqConcreteWith A
  abs := absSeq
  max := maxSeqWith A
  min := minSeqWith A
  ltProp := regularSeqLtProp
  ltData := regularSeqLtData
  ltData_to_prop := regularSeqLtData_to_prop
  positiveData := PosEventuallyData
  positiveData_to_prop := fun hx => hx.toProp
  positiveInv := fun {x} hx => positiveTailInvSeqWithBound A x hx
  positiveInv_agrees := fun {x} hx => rfl
  positiveInv_posData := by
    intro x hx
    exact regularSeqPositiveInvData_posData A hx
  positiveInv_mul_cancel := by
    intro x hx
    exact regularSeqPositiveInvData_mul_cancel A hx
  archimedean_posData := fun hx =>
    regularSeqArchimedeanPositiveData hx
  mul_archimedean_data :=
    regularSeqMulArchimedean_const_data A
  setoidLaws := cRealRegularSeqSetoidLawLayer A
  algebraLaws := cRealRegularSeqAlgebraLawLayer A
  orderLaws := cRealRegularSeqDataOrderLawLayer
  archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage A
  repSequenceComplete := cRealRepSequenceCompleteLayer
  oldQuotAdapterBoundary := cRealOldQuotCOFOCAdapterBoundary A
  source_surface_uses_regular_sequences := True
  structural_equality_is_not_the_real_equality := True
  inverse_is_data_indexed_not_total := True
  old_typeclass_is_adapter_only := True

/-- Roadmap checkpoint after exposing the final RegularSeq surface. -/
structure CRealAfterRegularSeqSourceSurfaceFrontier : Type where
  regularseq_source_surface_available : Prop
  setoid_algebra_order_layers_in_surface : Prop
  positive_inverse_and_archimedean_data_in_surface : Prop
  representative_completeness_in_surface : Prop
  old_quotient_adapter_boundary_in_surface : Prop
  next_compare_surface_with_old_adapter : Prop

def cRealAfterRegularSeqSourceSurfaceFrontier :
    CRealAfterRegularSeqSourceSurfaceFrontier where
  regularseq_source_surface_available := True
  setoid_algebra_order_layers_in_surface := True
  positive_inverse_and_archimedean_data_in_surface := True
  representative_completeness_in_surface := True
  old_quotient_adapter_boundary_in_surface := True
  next_compare_surface_with_old_adapter := True

end BishopCReal

set_option linter.style.longLine false

