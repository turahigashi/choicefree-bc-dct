import Mathdemo.Internal.Real.SampledClosenessReciprocalQuotientRespect

/-!
# Positive quotient inverse with explicit order data

The `COFO` interface asks for a total `inv : CRealQuot → CRealQuot`, but the
Bishop inverse construction is data-dependent: it needs a positive lower-tail
witness.  This file therefore builds the honest proof-indexed positive inverse
first and proves that it is independent of the particular positive-order data
for a fixed quotient element.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Quotient equality of representatives gives their eventual equality. -/
theorem relEventually_of_mkQuot_eq {x y : RegularSeq}
    (h : mkQuot x = mkQuot y) : relEventually x y :=
  Quotient.exact h

/-- Representative selected for the inverse of a positive quotient element,
where positivity is supplied as explicit data. -/
def positiveQuotInvSeqWithData
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h : ltQuotData zeroQuot x) : RegularSeq :=
  positiveTailInvSeqWithBound A (subSeq h.right h.left) h.pos

/-- Quotient value of the proof-indexed positive inverse. -/
def positiveQuotInvWithData
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h : ltQuotData zeroQuot x) : CRealQuot :=
  mkQuot (positiveQuotInvSeqWithData A h)

/-- The positive inverse representative is independent of the chosen positive
data for the same quotient element. -/
theorem positiveQuotInvSeqWithData_respects_data
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h₁ h₂ : ltQuotData zeroQuot x) :
    relEventually
      (positiveQuotInvSeqWithData A h₁)
      (positiveQuotInvSeqWithData A h₂) := by
  rcases h₁ with ⟨l₁, r₁, hl₁, hr₁, hpos₁⟩
  rcases h₂ with ⟨l₂, r₂, hl₂, hr₂, hpos₂⟩
  have hleft_eq : mkQuot l₁ = mkQuot l₂ := by
    rw [← hl₁, ← hl₂]
  have hright_eq : mkQuot r₁ = mkQuot r₂ := by
    rw [← hr₁, ← hr₂]
  have hleft_rel : relEventually l₁ l₂ :=
    relEventually_of_mkQuot_eq hleft_eq
  have hright_rel : relEventually r₁ r₂ :=
    relEventually_of_mkQuot_eq hright_eq
  have hsub_rel : relEventually (subSeq r₁ l₁) (subSeq r₂ l₂) :=
    subSeq_respects_eventually r₁ r₂ l₁ l₂ hright_rel hleft_rel
  exact positiveTailInvSeqWithBound_respects_eventually A
    (subSeq r₁ l₁) (subSeq r₂ l₂) hpos₁ hpos₂ hsub_rel

/-- The proof-indexed positive inverse quotient is independent of the chosen
positive data for the same quotient element. -/
theorem positiveQuotInvWithData_respects_data
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h₁ h₂ : ltQuotData zeroQuot x) :
    positiveQuotInvWithData A h₁ = positiveQuotInvWithData A h₂ :=
  Quotient.sound (positiveQuotInvSeqWithData_respects_data A h₁ h₂)

/-- The proof-indexed positive inverse respects equality of positive quotient
elements. -/
theorem positiveQuotInvWithData_respects_quot_eq
    (A : ScalarMulArchimedeanData) {x y : CRealQuot}
    (hxy : x = y)
    (hx : ltQuotData zeroQuot x) (hy : ltQuotData zeroQuot y) :
    positiveQuotInvWithData A hx = positiveQuotInvWithData A hy := by
  subst y
  exact positiveQuotInvWithData_respects_data A hx hy

/-- Data package for the proof-indexed positive quotient inverse. -/
structure PositiveQuotInverseWithDataSeed : Type where
  invSeq :
    ∀ _A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ltQuotData zeroQuot x → RegularSeq
  inv :
    ∀ _A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ltQuotData zeroQuot x → CRealQuot
  invSeq_respects_data :
    ∀ A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ∀ h₁ h₂ : ltQuotData zeroQuot x,
        relEventually (invSeq A h₁) (invSeq A h₂)
  inv_respects_data :
    ∀ A : ScalarMulArchimedeanData, ∀ {x : CRealQuot},
      ∀ h₁ h₂ : ltQuotData zeroQuot x,
        inv A h₁ = inv A h₂
  inv_respects_quot_eq :
    ∀ A : ScalarMulArchimedeanData, ∀ {x y : CRealQuot},
      x = y → ∀ hx : ltQuotData zeroQuot x, ∀ hy : ltQuotData zeroQuot y,
        inv A hx = inv A hy

def positiveQuotInverseWithDataSeed :
    PositiveQuotInverseWithDataSeed where
  invSeq := fun A {x} h => positiveQuotInvSeqWithData A (x := x) h
  inv := fun A {x} h => positiveQuotInvWithData A (x := x) h
  invSeq_respects_data := fun A {x} h₁ h₂ =>
    positiveQuotInvSeqWithData_respects_data A (x := x) h₁ h₂
  inv_respects_data := fun A {x} h₁ h₂ =>
    positiveQuotInvWithData_respects_data A (x := x) h₁ h₂
  inv_respects_quot_eq := fun A {x} {y} hxy hx hy =>
    positiveQuotInvWithData_respects_quot_eq A (x := x) (y := y) hxy hx hy

/-- Frontier after the data-indexed positive quotient inverse is well-defined
on positive quotient elements. -/
structure CRealQuotPositiveInverseWithDataFrontier : Type where
  total_inv_selector : Prop
  quotient_positive_witness_transport : Prop
  quotient_mul_inv_cancel : Prop
  quotient_inv_pos : Prop
  cauchy_completeness : Prop

def cRealQuotPositiveInverseWithDataFrontier :
    CRealQuotPositiveInverseWithDataFrontier where
  total_inv_selector := True
  quotient_positive_witness_transport := True
  quotient_mul_inv_cancel := True
  quotient_inv_pos := True
  cauchy_completeness := True

end BishopCReal

