import Mathdemo.Internal.Real.ValueEstimateSourceTimesReciprocalTail

/-!
# Quotient cancellation for proof-indexed positive inverse

`ValueEstimateSourceTimesReciprocalTail` proves the value-level estimate for a source representative times
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







end BishopCReal

