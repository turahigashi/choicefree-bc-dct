import Mathdemo.Internal.Rat.UniformBoundPositiveTailReciprocals

/-!
# Regularity of the bound-sensitive reciprocal tail

This file combines:

* the exact reciprocal-difference identity from `PositiveScalarReciprocalDifference`;
* the bound-sensitive reciprocal index from `BoundSensitiveReciprocalTailScaffold`;
* the uniform reciprocal bound from `UniformBoundPositiveTailReciprocals`;

to prove that the reindexed positive reciprocal tail is a regular sequence.

It still stops before quotient-level inverse definition and respect.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The reciprocal Lipschitz bound absorbs the two sampled dyadic errors for the
bound-sensitive reciprocal tail. -/
theorem reciprocal_tail_lipschitz_eps_sum_le
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (m n : Nat) :
    Le
      (COF.abs (positiveReciprocalLipschitzBound x h) *
        (eps (reciprocalTailIndexWith A x h m) +
          eps (reciprocalTailIndexWith A x h n)))
      (eps m + eps n) := by
  set L : Scalar := positiveReciprocalLipschitzBound x h
  set B : Nat := reciprocalTailBoundWith A x h
  set p : Nat := reciprocalTailIndexWith A x h m
  set q : Nat := reciprocalTailIndexWith A x h n
  have hpB : B + m ≤ p := by
    simpa [B, p] using reciprocalTailIndex_bound A x h m
  have hqB : B + n ≤ q := by
    simpa [B, q] using reciprocalTailIndex_bound A x h n
  have hp_eps : Le (eps p) (eps (B + m)) :=
    eps_le_of_le hpB
  have hq_eps : Le (eps q) (eps (B + n)) :=
    eps_le_of_le hqB
  have hLnonneg : Le 0 (COF.abs L) := scalar_abs_nonneg L
  have hp_step :
      Le (COF.abs L * eps p) (COF.abs L * eps (B + m)) :=
    scalar_mul_le_mul_left hp_eps hLnonneg
  have hq_step :
      Le (COF.abs L * eps q) (COF.abs L * eps (B + n)) :=
    scalar_mul_le_mul_left hq_eps hLnonneg
  have hp_budget : Le (COF.abs L * eps (B + m)) (eps m) := by
    simpa [L, B] using reciprocal_tail_bound_eps_le A x h m
  have hq_budget : Le (COF.abs L * eps (B + n)) (eps n) := by
    simpa [L, B] using reciprocal_tail_bound_eps_le A x h n
  have hp_final : Le (COF.abs L * eps p) (eps m) :=
    BishopC.le_trans hp_step hp_budget
  have hq_final : Le (COF.abs L * eps q) (eps n) :=
    BishopC.le_trans hq_step hq_budget
  have hsum := BishopC.le_add hp_final hq_final
  rw [show COF.abs L * (eps p + eps q) =
      COF.abs L * eps p + COF.abs L * eps q from by ring]
  simpa [L, p, q] using hsum

/-- The bound-sensitive reciprocal tail is regular. -/
theorem positiveTailInvValWithBound_regular
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) :
    RegularVal (positiveTailInvValWithBound A x h) := by
  intro m n
  set p : Nat := reciprocalTailIndexWith A x h m
  set q : Nat := reciprocalTailIndexWith A x h n
  have hpTail : h.N ≤ p := by
    simpa [p] using reciprocalTailIndex_tail A x h m
  have hqTail : h.N ≤ q := by
    simpa [q] using reciprocalTailIndex_tail A x h n
  have hpPos : COF.lt 0 (x.val p) :=
    scalar_pos_of_posEventuallyData_tail x h hpTail
  have hqPos : COF.lt 0 (x.val q) :=
    scalar_pos_of_posEventuallyData_tail x h hqTail
  have hdiff0 :
      Le
        (COF.abs
          (positiveTailInvValWithBound A x h m -
            positiveTailInvValWithBound A x h n))
        (COF.abs (positiveTailInvValWithBound A x h m) *
          COF.abs (positiveTailInvValWithBound A x h n) *
            COF.abs (x.val q - x.val p)) := by
    unfold positiveTailInvValWithBound positiveTailInvVal
    rw [show reciprocalTailIndexWith A x h m = p from by simp [p],
      show reciprocalTailIndexWith A x h n = q from by simp [q],
      if_pos hpTail, if_pos hqTail]
    exact scalar_abs_posInv_sub_le_mul_abs_sub (x.val p) (x.val q) hpPos hqPos
  have hinvProd :
      Le
        (COF.abs (positiveTailInvValWithBound A x h m) *
          COF.abs (positiveTailInvValWithBound A x h n))
        (COF.abs (positiveReciprocalLipschitzBound x h)) :=
    positiveTailInvValWithBound_abs_mul_le_lipschitzBound A x h m n
  have hdiffNonneg : Le 0 (COF.abs (x.val q - x.val p)) :=
    scalar_abs_nonneg (x.val q - x.val p)
  have hstep1 :
      Le
        (COF.abs (positiveTailInvValWithBound A x h m) *
          COF.abs (positiveTailInvValWithBound A x h n) *
            COF.abs (x.val q - x.val p))
        (COF.abs (positiveReciprocalLipschitzBound x h) *
          COF.abs (x.val q - x.val p)) :=
    scalar_mul_le_mul_right hinvProd hdiffNonneg
  have hxreg0 : Le (COF.abs (x.val p - x.val q)) (eps p + eps q) :=
    x.regular p q
  have hxreg : Le (COF.abs (x.val q - x.val p)) (eps p + eps q) := by
    rw [show x.val q - x.val p = -(x.val p - x.val q) from by ring]
    change Le (BishopCRat.CRat.absF (-(x.val p - x.val q))) (eps p + eps q)
    rw [BishopCRat.CRat.abs_neg (x.val p - x.val q)]
    exact hxreg0
  have hstep2 :
      Le
        (COF.abs (positiveReciprocalLipschitzBound x h) *
          COF.abs (x.val q - x.val p))
        (COF.abs (positiveReciprocalLipschitzBound x h) *
          (eps p + eps q)) :=
    scalar_mul_le_mul_left hxreg
      (scalar_abs_nonneg (positiveReciprocalLipschitzBound x h))
  have hbudget :
      Le
        (COF.abs (positiveReciprocalLipschitzBound x h) *
          (eps p + eps q))
        (eps m + eps n) := by
    simpa [p, q] using reciprocal_tail_lipschitz_eps_sum_le A x h m n
  exact BishopC.le_trans hdiff0
    (BishopC.le_trans hstep1 (BishopC.le_trans hstep2 hbudget))

/-- Regular sequence represented by the bound-sensitive positive reciprocal
tail. -/
def positiveTailInvSeqWithBound
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) : RegularSeq where
  val := positiveTailInvValWithBound A x h
  regular := positiveTailInvValWithBound_regular A x h





end BishopCReal

