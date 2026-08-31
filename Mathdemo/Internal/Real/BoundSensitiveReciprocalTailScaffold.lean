import Mathdemo.Internal.Rat.PositiveScalarReciprocalDifference

/-!
# Bound-sensitive reciprocal tail scaffold

`PositiveScalarReciprocalDifference` gives the exact scalar reciprocal-difference identity.  To turn it
into regularity, the reciprocal representative must be sampled far enough out
to absorb the reciprocal Lipschitz constant.  This file adds that indexing
scaffold and a reusable scalar-bound absorption lemma.

It still stops before the final reciprocal regularity estimate.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Natural dyadic bound supplied by scalar multiplicative Archimedean data for
an arbitrary scalar. -/
def scalarBoundWith (A : ScalarMulArchimedeanData) (B : Scalar) : Nat :=
  (A.witness B).val

/-- Certificate carried by `scalarBoundWith`. -/
theorem scalarBoundWith_spec (A : ScalarMulArchimedeanData) (B : Scalar) :
    Le (COF.abs B * eps (scalarBoundWith A B)) 1 := by
  unfold scalarBoundWith
  exact (A.witness B).property

/-- A scalar bound absorbs a later dyadic gauge. -/
theorem scalar_bound_tail_eps_le
    (A : ScalarMulArchimedeanData) (B : Scalar) (r : Nat) :
    Le (COF.abs B * eps (scalarBoundWith A B + r)) (eps r) := by
  have hidx :
      eps (scalarBoundWith A B + r) = eps (scalarBoundWith A B) * eps r :=
    eps_add_mul_local (scalarBoundWith A B) r
  rw [hidx]
  have hspec : Le (COF.abs B * eps (scalarBoundWith A B)) 1 :=
    scalarBoundWith_spec A B
  have hmul :
      Le ((COF.abs B * eps (scalarBoundWith A B)) * eps r) (1 * eps r) :=
    scalar_mul_le_mul_right hspec (eps_nonneg r)
  rw [show COF.abs B * (eps (scalarBoundWith A B) * eps r) =
        (COF.abs B * eps (scalarBoundWith A B)) * eps r from by ring]
  simpa [one_mul] using hmul

/-- Reciprocal Lipschitz constant suggested by the positive lower tail
`eps h.k < x_n`: the future estimate uses
`|1/a - 1/b| <= L * |b-a|`. -/
def positiveReciprocalLipschitzBound
    (_x : RegularSeq) (h : PosEventuallyData _x) : Scalar :=
  scalarPositiveInverseSeed.inv (eps h.k) *
    scalarPositiveInverseSeed.inv (eps h.k)

/-- Bound index for the reciprocal Lipschitz constant. -/
def reciprocalTailBoundWith
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) : Nat :=
  scalarBoundWith A (positiveReciprocalLipschitzBound x h)

/-- Bound absorption specialized to the reciprocal Lipschitz constant. -/
theorem reciprocal_tail_bound_eps_le
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (r : Nat) :
    Le (COF.abs (positiveReciprocalLipschitzBound x h) *
        eps (reciprocalTailBoundWith A x h + r))
      (eps r) := by
  exact scalar_bound_tail_eps_le A (positiveReciprocalLipschitzBound x h) r

/-- Output index for the reciprocal representative.  It is forced past both
the positive tail and the scalar bound that absorbs the reciprocal Lipschitz
constant. -/
def reciprocalTailIndexWith
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) : Nat :=
  Nat.max h.N (reciprocalTailBoundWith A x h + n)

theorem reciprocalTailIndex_tail
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) :
    h.N ≤ reciprocalTailIndexWith A x h n := by
  unfold reciprocalTailIndexWith
  exact Nat.le_max_left _ _

theorem reciprocalTailIndex_bound
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) :
    reciprocalTailBoundWith A x h + n ≤ reciprocalTailIndexWith A x h n := by
  unfold reciprocalTailIndexWith
  exact Nat.le_max_right _ _

/-- Bound-sensitive reciprocal tail value. -/
def positiveTailInvValWithBound
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) : Scalar :=
  positiveTailInvVal x h (reciprocalTailIndexWith A x h n)

theorem positiveTailInvValWithBound_pos
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) :
    COF.lt 0 (positiveTailInvValWithBound A x h n) :=
  positiveTailInvVal_pos x h (reciprocalTailIndex_tail A x h n)

theorem positiveTail_mul_invValWithBound_eq_one
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) :
    x.val (reciprocalTailIndexWith A x h n) *
      positiveTailInvValWithBound A x h n = 1 :=
  positiveTail_mul_invVal_eq_one x h (reciprocalTailIndex_tail A x h n)

/-- Data package for the bound-sensitive reciprocal tail scaffold. -/
structure PositiveTailReciprocalBoundSeed : Type where
  scalarBound : ScalarMulArchimedeanData → Scalar → Nat
  scalar_bound_tail_eps_le :
    ∀ A : ScalarMulArchimedeanData, ∀ B : Scalar, ∀ r : Nat,
      Le (COF.abs B * eps (scalarBound A B + r)) (eps r)
  lipschitzBound : ∀ x : RegularSeq, PosEventuallyData x → Scalar
  recipBound : ∀ _A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
    PosEventuallyData x → Nat
  recipIndex : ∀ _A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
    PosEventuallyData x → Nat → Nat
  recipIndex_tail :
    ∀ A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
      ∀ h : PosEventuallyData x, ∀ n : Nat, h.N ≤ recipIndex A x h n
  recipIndex_bound :
    ∀ A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
      ∀ h : PosEventuallyData x, ∀ n : Nat,
        recipBound A x h + n ≤ recipIndex A x h n
  recipVal : ∀ _A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
    PosEventuallyData x → Nat → Scalar
  recipVal_pos :
    ∀ A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
      ∀ h : PosEventuallyData x, ∀ n : Nat, COF.lt 0 (recipVal A x h n)
  tail_mul_recipVal :
    ∀ A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
      ∀ h : PosEventuallyData x, ∀ n : Nat,
        x.val (recipIndex A x h n) * recipVal A x h n = 1

def positiveTailReciprocalBoundSeed :
    PositiveTailReciprocalBoundSeed where
  scalarBound := scalarBoundWith
  scalar_bound_tail_eps_le := scalar_bound_tail_eps_le
  lipschitzBound := positiveReciprocalLipschitzBound
  recipBound := reciprocalTailBoundWith
  recipIndex := reciprocalTailIndexWith
  recipIndex_tail := reciprocalTailIndex_tail
  recipIndex_bound := reciprocalTailIndex_bound
  recipVal := positiveTailInvValWithBound
  recipVal_pos := positiveTailInvValWithBound_pos
  tail_mul_recipVal := positiveTail_mul_invValWithBound_eq_one

/-- Frontier after the bound-sensitive reciprocal tail scaffold is available. -/
structure CRealQuotPositiveInverseBoundFrontier : Type where
  reciprocal_lipschitz_order_bound : Prop
  reciprocal_tail_regular : Prop
  quotient_inv_definition : Prop
  quotient_inverse_laws : Prop

def cRealQuotPositiveInverseBoundFrontier :
    CRealQuotPositiveInverseBoundFrontier where
  reciprocal_lipschitz_order_bound := True
  reciprocal_tail_regular := True
  quotient_inv_definition := True
  quotient_inverse_laws := True

end BishopCReal

