import Mathdemo.Internal.Real.TotalPositiveInverseSelectorDecidableQuotient

/-!
# Source quotient represented by positive order data

`PositiveQuotientInverseExplicitOrderData` builds the positive inverse from the representative
`right - left` carried by `ltQuotData zeroQuot x`.  For the eventual
`mul_inv_cancel` theorem, we need to connect that source representative back to
the original quotient element `x`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The source representative `right - left` carried by positive order data. -/
def positiveQuotInvSource {x : CRealQuot}
    (h : ltQuotData zeroQuot x) : CRealQuot :=
  mkQuot (subSeq h.right h.left)

/-- For data witnessing `0 < x`, the carried source representative is
quotient-equal to `x`. -/
theorem positiveQuotInvSource_eq_self {x : CRealQuot}
    (h : ltQuotData zeroQuot x) :
    positiveQuotInvSource h = x := by
  rcases h with ⟨l, r, hl, hr, _hpos⟩
  change subQuot (mkQuot r) (mkQuot l) = x
  rw [← hl, ← hr]
  exact subQuot_zero_right x

/-- The carried source representative is itself positive. -/
theorem positiveQuotInvSource_pos {x : CRealQuot}
    (h : ltQuotData zeroQuot x) :
    ltQuot zeroQuot (positiveQuotInvSource h) := by
  rcases h with ⟨l, r, _hl, _hr, hpos⟩
  change PosEventually (subSeq (subSeq r l) zeroSeq)
  exact posEventually_sub_zero_of_pos (subSeq r l) hpos.toProp

/-- The data-indexed inverse may be read as the inverse of the carried source
representative. -/
theorem positiveQuotInvWithData_source_eq
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h : ltQuotData zeroQuot x) :
    positiveQuotInvWithData A h =
      mkQuot (positiveTailInvSeqWithBound A (subSeq h.right h.left) h.pos) := by
  rfl

/-- Data package for the source-quotient bridge needed by cancellation. -/
structure PositiveQuotInverseSourceSeed : Type where
  source : ∀ {x : CRealQuot}, ltQuotData zeroQuot x → CRealQuot
  source_eq_self :
    ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x, source h = x
  source_pos :
    ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
      ltQuot zeroQuot (source h)
  inv_source_eq :
    ∀ A : ScalarMulArchimedeanData,
      ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
        positiveQuotInvWithData A h =
          mkQuot (positiveTailInvSeqWithBound A (subSeq h.right h.left) h.pos)

def positiveQuotInverseSourceSeed :
    PositiveQuotInverseSourceSeed where
  source := positiveQuotInvSource
  source_eq_self := positiveQuotInvSource_eq_self
  source_pos := positiveQuotInvSource_pos
  inv_source_eq := positiveQuotInvWithData_source_eq

/-- Frontier after the source quotient is connected back to the original
positive element. -/
structure CRealQuotPositiveInverseSourceFrontier : Type where
  quotient_product_reindex_cancel : Prop
  quotient_inv_pos_uniform_lower_bound : Prop
  cauchy_completeness : Prop

def cRealQuotPositiveInverseSourceFrontier :
    CRealQuotPositiveInverseSourceFrontier where
  quotient_product_reindex_cancel := True
  quotient_inv_pos_uniform_lower_bound := True
  cauchy_completeness := True

end BishopCReal

