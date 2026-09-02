import Mathdemo.Internal.Real.RegularityBoundSensitiveReciprocalTail

/-!
# Mixed reciprocal estimates for quotient respect

`RegularityBoundSensitiveReciprocalTail` proves that a positive representative has a regular reciprocal
tail.  To descend this construction to a quotient inverse, the next local
ingredient is a mixed estimate for two positive representatives.

This file closes the algebraic/Lipschitz half of that respect proof.  It still
stops before proving that the two independently reindexed tails of equivalent
representatives are eventually close.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Mixed Lipschitz constant for reciprocal differences between two positive
tail representatives. -/
def positiveReciprocalMixedLipschitzBound
    (_x : RegularSeq) (hx : PosEventuallyData _x)
    (_y : RegularSeq) (hy : PosEventuallyData _y) : Scalar :=
  scalarPositiveInverseSeed.inv (eps hx.k) *
    scalarPositiveInverseSeed.inv (eps hy.k)

/-- Product of two reciprocal samples, possibly from different positive
representatives, is bounded by the mixed reciprocal Lipschitz constant. -/
theorem positiveTailInvValWithBound_abs_mul_le_mixedLipschitzBound
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq)
    (hx : PosEventuallyData x) (hy : PosEventuallyData y)
    (m n : Nat) :
    Le
      (COF.abs (positiveTailInvValWithBound A x hx m) *
        COF.abs (positiveTailInvValWithBound A y hy n))
      (COF.abs (positiveReciprocalMixedLipschitzBound x hx y hy)) := by
  set Lx : Scalar := COF.abs (scalarPositiveInverseSeed.inv (eps hx.k))
  set Ly : Scalar := COF.abs (scalarPositiveInverseSeed.inv (eps hy.k))
  have hm :
      Le (COF.abs (positiveTailInvValWithBound A x hx m)) Lx := by
    simpa [Lx] using
      positiveTailInvValWithBound_abs_le_lipschitzFactor A x hx m
  have hn :
      Le (COF.abs (positiveTailInvValWithBound A y hy n)) Ly := by
    simpa [Ly] using
      positiveTailInvValWithBound_abs_le_lipschitzFactor A y hy n
  have hstep1 :
      Le
        (COF.abs (positiveTailInvValWithBound A x hx m) *
          COF.abs (positiveTailInvValWithBound A y hy n))
        (COF.abs (positiveTailInvValWithBound A x hx m) * Ly) :=
    scalar_mul_le_mul_left hn
      (scalar_abs_nonneg (positiveTailInvValWithBound A x hx m))
  have hstep2 :
      Le
        (COF.abs (positiveTailInvValWithBound A x hx m) * Ly)
        (Lx * Ly) :=
    scalar_mul_le_mul_right hm (by
      unfold Ly
      exact scalar_abs_nonneg (scalarPositiveInverseSeed.inv (eps hy.k)))
  have hprod :
      Le
        (COF.abs (positiveTailInvValWithBound A x hx m) *
          COF.abs (positiveTailInvValWithBound A y hy n))
        (Lx * Ly) :=
    BishopC.le_trans hstep1 hstep2
  have hL :
      COF.abs (positiveReciprocalMixedLipschitzBound x hx y hy) = Lx * Ly := by
    unfold positiveReciprocalMixedLipschitzBound Lx Ly
    rw [scalar_abs_mul
      (scalarPositiveInverseSeed.inv (eps hx.k))
      (scalarPositiveInverseSeed.inv (eps hy.k))]
  rwa [hL]

/-- Exact reciprocal-difference estimate for samples taken from two positive
representatives. -/
theorem positiveTailInvValWithBound_mixed_abs_sub_le
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq)
    (hx : PosEventuallyData x) (hy : PosEventuallyData y)
    (m n : Nat) :
    Le
      (COF.abs
        (positiveTailInvValWithBound A x hx m -
          positiveTailInvValWithBound A y hy n))
      (COF.abs (positiveTailInvValWithBound A x hx m) *
        COF.abs (positiveTailInvValWithBound A y hy n) *
          COF.abs
            (y.val (reciprocalTailIndexWith A y hy n) -
              x.val (reciprocalTailIndexWith A x hx m))) := by
  set p : Nat := reciprocalTailIndexWith A x hx m
  set q : Nat := reciprocalTailIndexWith A y hy n
  have hpTail : hx.N ≤ p := by
    simpa [p] using reciprocalTailIndex_tail A x hx m
  have hqTail : hy.N ≤ q := by
    simpa [q] using reciprocalTailIndex_tail A y hy n
  have hpPos : COF.lt 0 (x.val p) :=
    scalar_pos_of_posEventuallyData_tail x hx hpTail
  have hqPos : COF.lt 0 (y.val q) :=
    scalar_pos_of_posEventuallyData_tail y hy hqTail
  unfold positiveTailInvValWithBound positiveTailInvVal
  rw [show reciprocalTailIndexWith A x hx m = p from by simp [p],
    show reciprocalTailIndexWith A y hy n = q from by simp [q],
    if_pos hpTail, if_pos hqTail]
  exact scalar_abs_posInv_sub_le_mul_abs_sub (x.val p) (y.val q) hpPos hqPos

/-- Mixed Lipschitz form of the reciprocal-difference estimate. -/
theorem positiveTailInvValWithBound_mixed_abs_sub_le_lipschitz
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq)
    (hx : PosEventuallyData x) (hy : PosEventuallyData y)
    (m n : Nat) :
    Le
      (COF.abs
        (positiveTailInvValWithBound A x hx m -
          positiveTailInvValWithBound A y hy n))
      (COF.abs (positiveReciprocalMixedLipschitzBound x hx y hy) *
        COF.abs
          (y.val (reciprocalTailIndexWith A y hy n) -
            x.val (reciprocalTailIndexWith A x hx m))) := by
  have hdiff :=
    positiveTailInvValWithBound_mixed_abs_sub_le A x y hx hy m n
  have hprod :
      Le
        (COF.abs (positiveTailInvValWithBound A x hx m) *
          COF.abs (positiveTailInvValWithBound A y hy n))
        (COF.abs (positiveReciprocalMixedLipschitzBound x hx y hy)) :=
    positiveTailInvValWithBound_abs_mul_le_mixedLipschitzBound
      A x y hx hy m n
  have hdistNonneg :
      Le 0
        (COF.abs
          (y.val (reciprocalTailIndexWith A y hy n) -
            x.val (reciprocalTailIndexWith A x hx m))) :=
    scalar_abs_nonneg
      (y.val (reciprocalTailIndexWith A y hy n) -
        x.val (reciprocalTailIndexWith A x hx m))
  have hstep :
      Le
        (COF.abs (positiveTailInvValWithBound A x hx m) *
          COF.abs (positiveTailInvValWithBound A y hy n) *
            COF.abs
              (y.val (reciprocalTailIndexWith A y hy n) -
                x.val (reciprocalTailIndexWith A x hx m)))
        (COF.abs (positiveReciprocalMixedLipschitzBound x hx y hy) *
          COF.abs
            (y.val (reciprocalTailIndexWith A y hy n) -
              x.val (reciprocalTailIndexWith A x hx m))) :=
    scalar_mul_le_mul_right hprod hdistNonneg
  exact BishopC.le_trans hdiff hstep

/-- The exact remaining closeness obligation needed to turn the mixed
reciprocal estimate into quotient respect. -/
def positiveTailReciprocalSampledClose
    (A : ScalarMulArchimedeanData)
    (x : RegularSeq) (hx : PosEventuallyData x)
    (y : RegularSeq) (hy : PosEventuallyData y) : Prop :=
  ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
    Le
      (COF.abs (positiveReciprocalMixedLipschitzBound x hx y hy) *
        COF.abs
          (y.val (reciprocalTailIndexWith A y hy n) -
            x.val (reciprocalTailIndexWith A x hx n)))
      (eps k)

/-- Once the independently reindexed source representatives are close with the
mixed reciprocal Lipschitz budget, the reciprocal tails are eventually equal. -/
theorem positiveTailInvSeqWithBound_respects_eventually_of_sampled_close
    (A : ScalarMulArchimedeanData)
    (x : RegularSeq) (hx : PosEventuallyData x)
    (y : RegularSeq) (hy : PosEventuallyData y)
    (hclose : positiveTailReciprocalSampledClose A x hx y hy) :
    relEventually
      (positiveTailInvSeqWithBound A x hx)
      (positiveTailInvSeqWithBound A y hy) := by
  intro k
  rcases hclose k with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact BishopC.le_trans
    (positiveTailInvValWithBound_mixed_abs_sub_le_lipschitz
      A x y hx hy n n)
    (hN n hn)





end BishopCReal

