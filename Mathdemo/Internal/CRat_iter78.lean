import Mathdemo.Internal.CRat_iter77

/-!
# Quotient cancellation for proof-indexed positive inverse

`CRat_iter77` proves the value-level estimate for a source representative times
its reciprocal tail.  This file applies that estimate to concrete quotient
multiplication and proves the data-indexed cancellation theorem:

`x * positiveQuotInvWithData A h = 1`

for `h : ltQuotData zeroQuot x`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A positive source representative multiplied by its reciprocal-tail
representative is eventually equal to one. -/
theorem positiveTail_mulSeqConcreteWith_invSeq_eventually_one
    (A : ScalarMulArchimedeanData)
    (x : RegularSeq) (h : PosEventuallyData x) :
    relEventually
      (mulSeqConcreteWith A x (positiveTailInvSeqWithBound A x h))
      oneSeq := by
  intro k
  set y : RegularSeq := positiveTailInvSeqWithBound A x h
  set K : Nat := mulBoundWith A x y
  set L : Scalar := COF.abs (scalarPositiveInverseSeed.inv (eps h.k))
  set B : Nat := scalarBoundWith A L
  refine ⟨B + (k + 1), ?_⟩
  intro n hn
  set p : Nat := mulIndexFromBound K n
  have hnp : n ≤ p := by
    simpa [p] using le_mulIndexFromBound K n
  have hp : B + (k + 1) ≤ p := Nat.le_trans hn hnp
  have hq : B + (k + 1) ≤ reciprocalTailIndexWith A x h p := by
    exact Nat.le_trans hp (reciprocalTailIndex_ge_self A x h p)
  have hbudget :
      Le
        (COF.abs
          (x.val p * positiveTailInvValWithBound A x h p - 1))
        (eps (k + 1) + eps (k + 1)) := by
    exact positiveTail_source_mul_invValWithBound_abs_sub_one_le_budget
      A x h (p := p) (m := p) (r := k + 1) (by simpa [B, L] using hp)
      (by simpa [B, L] using hq)
  have hfinal :
      Le
        (COF.abs
          (x.val p * positiveTailInvValWithBound A x h p - 1))
        (eps k) := by
    rwa [eps_succ_add_self k] at hbudget
  change
    Le
      (COF.abs
        ((mulSeqConcreteWith A x y).val n - oneSeq.val n))
      (eps k)
  change
    Le
      (COF.abs
        (x.val p * y.val p - 1))
      (eps k)
  simpa [y] using hfinal

/-- Quotient-level cancellation for the carried positive source representative. -/
theorem positiveQuot_source_mul_invWithData_eq_one
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h : ltQuotData zeroQuot x) :
    mulQuotConcreteWith A (positiveQuotInvSource h)
      (positiveQuotInvWithData A h) = oneQuot := by
  change
    mulQuotConcreteWith A
      (mkQuot (subSeq h.right h.left))
      (mkQuot (positiveTailInvSeqWithBound A (subSeq h.right h.left) h.pos)) =
        oneQuot
  apply Quotient.sound
  exact positiveTail_mulSeqConcreteWith_invSeq_eventually_one
    A (subSeq h.right h.left) h.pos

/-- Quotient-level cancellation for the original positive quotient element. -/
theorem positiveQuot_mul_invWithData_eq_one
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h : ltQuotData zeroQuot x) :
    mulQuotConcreteWith A x (positiveQuotInvWithData A h) = oneQuot := by
  have hs : positiveQuotInvSource h = x := positiveQuotInvSource_eq_self h
  calc
    mulQuotConcreteWith A x (positiveQuotInvWithData A h)
        = mulQuotConcreteWith A (positiveQuotInvSource h)
            (positiveQuotInvWithData A h) := by
          rw [hs]
    _ = oneQuot := positiveQuot_source_mul_invWithData_eq_one A h

/-- Data package for the proof-indexed positive inverse cancellation theorem. -/
structure PositiveQuotInverseCancellationSeed : Type where
  recipSeq_mul_eventually_one :
    ∀ A : ScalarMulArchimedeanData,
      ∀ x : RegularSeq, ∀ h : PosEventuallyData x,
        relEventually
          (mulSeqConcreteWith A x (positiveTailInvSeqWithBound A x h))
          oneSeq
  source_mul_inv_eq_one :
    ∀ A : ScalarMulArchimedeanData,
      ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
        mulQuotConcreteWith A (positiveQuotInvSource h)
          (positiveQuotInvWithData A h) = oneQuot
  mul_inv_eq_one :
    ∀ A : ScalarMulArchimedeanData,
      ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
        mulQuotConcreteWith A x (positiveQuotInvWithData A h) = oneQuot

def positiveQuotInverseCancellationSeed :
    PositiveQuotInverseCancellationSeed where
  recipSeq_mul_eventually_one :=
    positiveTail_mulSeqConcreteWith_invSeq_eventually_one
  source_mul_inv_eq_one := positiveQuot_source_mul_invWithData_eq_one
  mul_inv_eq_one := positiveQuot_mul_invWithData_eq_one

/-- Frontier after proof-indexed positive inverse cancellation is available. -/
structure CRealQuotPositiveInverseCancellationFrontier : Type where
  total_selector_cancellation : Prop
  quotient_inv_pos_uniform_lower_bound : Prop
  cauchy_completeness : Prop

def cRealQuotPositiveInverseCancellationFrontier :
    CRealQuotPositiveInverseCancellationFrontier where
  total_selector_cancellation := True
  quotient_inv_pos_uniform_lower_bound := True
  cauchy_completeness := True

end BishopCReal

